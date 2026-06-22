#![allow(non_snake_case)]

#[cfg(not(feature = "std"))]
use alloc::{boxed::Box, vec, vec::Vec};

use ark_ec::{AffineRepr, VariableBaseMSM};
use ark_ff::Field;
use ark_std::{format, string::ToString, One, UniformRand, Zero};
use core::borrow::BorrowMut;
use core::mem;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::MerlinTranscript;
use rand_core::{CryptoRng, RngCore};

use super::constraint_system::{
    ConstraintSystem, RandomizableConstraintSystem, RandomizedConstraintSystem,
};
use super::linear_combination::{LinearCombination, Variable};
use super::proof::R1CSProof;

use crate::errors::R1CSError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::r1cs::prover::{COMMITMENT_LABEL, VEC_COMMITMENT_LABEL};
use crate::r1cs::{committed_t_degrees, degrees, t_poly_degree, Metrics};
use crate::transcript::TranscriptProtocol;
pub use batch::{batch_verify_with_given_randomness, batch_verify_with_rng};

pub mod batch;

/// A [`ConstraintSystem`] implementation for use by the verifier.
///
/// The verifier adds high-level variable commitments to the transcript,
/// allocates low-level variables and creates constraints in terms of these
/// high-level variables and low-level variables.
///
/// When all constraints are added, the verifying code calls `verify`
/// which consumes the `Verifier` instance, samples random challenges
/// that instantiate the randomized constraints, and verifies the proof.
pub struct Verifier<T: BorrowMut<MerlinTranscript>, C: AffineRepr> {
    transcript: T,
    pub constraints: Vec<LinearCombination<C::ScalarField>>,

    pub vec_comms: Vec<(C, usize)>,

    /// Records the number of low-level variables allocated in the
    /// constraint system.
    ///
    /// Because the `VerifierCS` only keeps the constraints
    /// themselves, it doesn't record the assignments (they're all
    /// `Missing`), so the `num_multiplier` isn't kept implicitly in the
    /// variable assignments.
    pub(crate) num_multiplier: usize,
    pub(crate) V: Vec<C>,

    /// This list holds closures that will be called in the second phase of the protocol,
    /// when non-randomized variables are committed.
    /// After that, the option will flip to None and additional calls to `randomize_constraints`
    /// will invoke closures immediately.
    deferred_constraints:
        Vec<Box<dyn FnOnce(&mut RandomizingVerifier<T, C>) -> Result<(), R1CSError>>>,

    /// Index of a pending multiplier that's not fully assigned yet.
    pending_multiplier: Option<usize>,
}

// todo I assume this would be automatically implemented by the compiler if it did not have a a mutable borrow of a transcript
unsafe impl<'g, T: BorrowMut<MerlinTranscript>, C: AffineRepr> Send for Verifier<T, C> {} // todo fix after refactor

/// Verifier in the randomizing phase.
///
/// Note: this type is exported because it is used to specify the associated type
/// in the public impl of a trait `ConstraintSystem`, which boils down to allowing compiler to
/// monomorphize the closures for the proving and verifying code.
/// However, this type cannot be instantiated by the user and therefore can only be used within
/// the callback provided to `specify_randomized_constraints`.
pub struct RandomizingVerifier<T: BorrowMut<MerlinTranscript>, C: AffineRepr> {
    verifier: Verifier<T, C>,
}

impl<T: BorrowMut<MerlinTranscript>, C: AffineRepr> ConstraintSystem<C::ScalarField>
    for Verifier<T, C>
{
    fn transcript(&mut self) -> &mut MerlinTranscript {
        self.transcript.borrow_mut()
    }

    fn multiply(
        &mut self,
        mut left: LinearCombination<C::ScalarField>,
        mut right: LinearCombination<C::ScalarField>,
    ) -> (
        Variable<C::ScalarField>,
        Variable<C::ScalarField>,
        Variable<C::ScalarField>,
    ) {
        let var = self.num_multiplier;
        self.num_multiplier += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        // Constrain l,r,o:
        left.terms.push((l_var, -C::ScalarField::one()));
        right.terms.push((r_var, -C::ScalarField::one()));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate(
        &mut self,
        _: Option<C::ScalarField>,
    ) -> Result<Variable<C::ScalarField>, R1CSError> {
        match self.pending_multiplier {
            None => {
                let i = self.num_multiplier;
                self.num_multiplier += 1;
                self.pending_multiplier = Some(i);
                Ok(Variable::MultiplierLeft(i))
            }
            Some(i) => {
                self.pending_multiplier = None;
                Ok(Variable::MultiplierRight(i))
            }
        }
    }

    fn allocate_multiplier(
        &mut self,
        _: Option<(C::ScalarField, C::ScalarField)>,
    ) -> Result<
        (
            Variable<C::ScalarField>,
            Variable<C::ScalarField>,
            Variable<C::ScalarField>,
        ),
        R1CSError,
    > {
        let var = self.num_multiplier;
        self.num_multiplier += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        Ok((l_var, r_var, o_var))
    }

    fn metrics(&self) -> Metrics {
        Metrics {
            multipliers: self.num_multiplier,
            constraints: self.constraints.len() + self.deferred_constraints.len(),
            phase_one_constraints: self.constraints.len(),
            phase_two_constraints: self.deferred_constraints.len(),
        }
    }

    fn constrain(&mut self, lc: LinearCombination<C::ScalarField>) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination
        // evals to 0 for prover, etc).
        self.constraints.push(lc);
    }

    fn evaluate(&self, _: &LinearCombination<C::ScalarField>) -> Option<C::ScalarField> {
        None
    }
}

impl<T: BorrowMut<MerlinTranscript>, C: AffineRepr> RandomizableConstraintSystem<C::ScalarField>
    for Verifier<T, C>
{
    type RandomizedCS = RandomizingVerifier<T, C>;

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
    where
        F: 'static + FnOnce(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        self.deferred_constraints.push(Box::new(callback));
        Ok(())
    }
}

impl<T: BorrowMut<MerlinTranscript>, C: AffineRepr> ConstraintSystem<C::ScalarField>
    for RandomizingVerifier<T, C>
{
    fn transcript(&mut self) -> &mut MerlinTranscript {
        self.verifier.transcript.borrow_mut()
    }

    fn multiply(
        &mut self,
        left: LinearCombination<C::ScalarField>,
        right: LinearCombination<C::ScalarField>,
    ) -> (
        Variable<C::ScalarField>,
        Variable<C::ScalarField>,
        Variable<C::ScalarField>,
    ) {
        self.verifier.multiply(left, right)
    }

    fn allocate(
        &mut self,
        assignment: Option<C::ScalarField>,
    ) -> Result<Variable<C::ScalarField>, R1CSError> {
        self.verifier.allocate(assignment)
    }

    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(C::ScalarField, C::ScalarField)>,
    ) -> Result<
        (
            Variable<C::ScalarField>,
            Variable<C::ScalarField>,
            Variable<C::ScalarField>,
        ),
        R1CSError,
    > {
        self.verifier.allocate_multiplier(input_assignments)
    }

    fn metrics(&self) -> Metrics {
        self.verifier.metrics()
    }

    fn constrain(&mut self, lc: LinearCombination<C::ScalarField>) {
        self.verifier.constrain(lc)
    }

    fn evaluate(&self, lc: &LinearCombination<C::ScalarField>) -> Option<C::ScalarField> {
        self.verifier.evaluate(lc)
    }
}

impl<T: BorrowMut<MerlinTranscript>, C: AffineRepr> RandomizedConstraintSystem<C::ScalarField>
    for RandomizingVerifier<T, C>
{
    fn challenge_scalar(&mut self, label: &'static [u8]) -> C::ScalarField {
        let t = self.verifier.transcript.borrow_mut();
        TranscriptProtocol::challenge_scalar::<C>(t, label)
    }
}

impl<T: BorrowMut<MerlinTranscript>, C: AffineRepr> Verifier<T, C> {
    /// Construct an empty constraint system with specified external
    /// input variables.
    ///
    /// # Inputs
    ///
    /// The `transcript` parameter is a Merlin proof transcript.  The
    /// `VerifierCS` holds onto the `&mut MerlinTranscript` until it consumes
    /// itself during [`VerifierCS::verify`], releasing its borrow of the
    /// transcript.  This ensures that the transcript cannot be
    /// altered except by the `VerifierCS` before proving is complete.
    ///
    /// The `commitments` parameter is a list of Pedersen commitments
    /// to the external variables for the constraint system.  All
    /// external variables must be passed up-front, so that challenges
    /// produced by [`ConstraintSystem::challenge_scalar`] are bound
    /// to the external variables.
    ///
    /// # Returns
    ///
    /// Returns a tuple `(cs, vars)`.
    ///
    /// The first element is the newly constructed constraint system.
    ///
    /// The second element is a list of [`Variable`]s corresponding to
    /// the external inputs, which can be used to form constraints.
    pub fn new(mut transcript: T) -> Self {
        transcript.borrow_mut().r1cs_domain_sep();

        Verifier {
            vec_comms: Vec::new(),
            transcript,
            num_multiplier: 0,
            V: Vec::new(),
            constraints: Vec::new(),
            deferred_constraints: Vec::new(),
            pending_multiplier: None,
        }
    }

    pub fn size(&self) -> usize {
        let mut n = self.num_multiplier;
        for (_, dim) in self.vec_comms.iter() {
            n = core::cmp::max(*dim, n)
        }
        n
    }

    /// Creates commitment to a high-level variable and adds it to the transcript.
    ///
    /// # Inputs
    ///
    /// The `commitment` parameter is a Pedersen commitment
    /// to the external variable for the constraint system.  All
    /// external variables must be passed up-front, so that challenges
    /// produced by [`ConstraintSystem::challenge_scalar`] are bound
    /// to the external variables.
    ///
    /// # Returns
    ///
    /// Returns a pair of a Pedersen commitment (as a compressed Ristretto point),
    /// and a [`Variable`] corresponding to it, which can be used to form constraints.
    pub fn commit(&mut self, commitment: C) -> Variable<C::ScalarField> {
        let i = self.V.len();
        self.V.push(commitment);

        // Add the commitment to the transcript.
        self.transcript
            .borrow_mut()
            .append_point(COMMITMENT_LABEL, &commitment);

        Variable::Committed(i)
    }

    /// `dimension` is the length of the committed vector
    pub fn commit_vec(&mut self, dimension: usize, comm: C) -> Vec<Variable<C::ScalarField>> {
        // allocate next index for vector commitment
        let comm_idx = self.vec_comms.len();

        // add the commitment to the transcript.
        self.transcript
            .borrow_mut()
            .append_point(VEC_COMMITMENT_LABEL, &comm);

        // add to list of commitments
        self.vec_comms.push((comm, dimension));

        // create variables for all the addressable coordinates
        (0..dimension)
            .map(|i| Variable::VectorCommit(comm_idx, i))
            .collect()
    }

    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV, wc)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    ///
    /// This has the same logic as `ProverCS::flattened_constraints()`
    /// but also computes the constant terms (which the prover skips
    /// because they're not needed to construct the proof).
    fn flattened_constraints(
        &mut self,
        z: &C::ScalarField,
    ) -> (
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
        Vec<Vec<C::ScalarField>>,
        C::ScalarField,
    ) {
        let n = self.num_multiplier;
        let m = self.V.len();

        let mut wL = vec![C::ScalarField::zero(); n];
        let mut wR = vec![C::ScalarField::zero(); n];
        let mut wO = vec![C::ScalarField::zero(); n];
        let mut wV = vec![C::ScalarField::zero(); m];
        let mut wc = C::ScalarField::zero();

        let mut wVCs = Vec::with_capacity(self.vec_comms.len());
        for (_, dim) in self.vec_comms.iter() {
            wVCs.push(vec![C::ScalarField::zero(); *dim]);
        }

        let mut exp_z = *z;
        for lc in self.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var {
                    Variable::MultiplierLeft(i) => {
                        wL[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierRight(i) => {
                        wR[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierOutput(i) => {
                        wO[*i] += exp_z * coeff;
                    }
                    Variable::Committed(i) => {
                        wV[*i] -= exp_z * coeff;
                    }
                    Variable::VectorCommit(j, i) => {
                        // j : index of commitment
                        // i : coordinate with-in commitment
                        wVCs[*j][*i] += exp_z * coeff;
                    }
                    Variable::One(_) => {
                        wc -= exp_z * coeff;
                    }
                }
            }
            exp_z *= z;
        }

        (wL, wR, wO, wV, wVCs, wc)
    }

    /// Calls all remembered callbacks with an API that
    /// allows generating challenge scalars.
    fn create_randomized_constraints(mut self) -> Result<Self, R1CSError> {
        // Clear the pending multiplier (if any) because it was committed into A_L/A_R/S.
        self.pending_multiplier = None;

        if self.deferred_constraints.is_empty() {
            self.transcript.borrow_mut().r1cs_1phase_domain_sep();
            Ok(self)
        } else {
            self.transcript.borrow_mut().r1cs_2phase_domain_sep();
            // Note: the wrapper could've used &mut instead of ownership,
            // but specifying lifetimes for boxed closures is not going to be nice,
            // so we move the self into wrapper and then move it back out afterwards.
            let mut callbacks = mem::take(&mut self.deferred_constraints);
            let mut wrapped_self = RandomizingVerifier { verifier: self };
            for callback in callbacks.drain(..) {
                callback(&mut wrapped_self)?;
            }
            Ok(wrapped_self.verifier)
        }
    }

    /// Consume this `VerifierCS` and attempt to verify the supplied `proof`.
    /// The `pc_gens` and `bp_gens` are generators for Pedersen commitments and
    /// Bulletproofs vector commitments, respectively.  The
    /// [`BulletproofGens`] should have `gens_capacity` greater than
    /// the number of multiplication constraints that will eventually
    /// be added into the constraint system.
    #[cfg(feature = "std")]
    pub fn verify(
        self,
        proof: &R1CSProof<C>,
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
    ) -> Result<(), R1CSError> {
        let mut rng = rand::thread_rng();
        self.verify_with_rng(proof, pc_gens, bp_gens, &mut rng)
    }

    /// Consume this `VerifierCS` and attempt to verify the supplied `proof`.
    /// The `pc_gens` and `bp_gens` are generators for Pedersen commitments and
    /// Bulletproofs vector commitments, respectively.  The
    /// [`BulletproofGens`] should have `gens_capacity` greater than
    /// the number of multiplication constraints that will eventually
    /// be added into the constraint system.
    pub fn verify_with_rng<R: RngCore + CryptoRng>(
        self,
        proof: &R1CSProof<C>,
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
        rng: &mut R,
    ) -> Result<(), R1CSError> {
        let verification_tuple = match self.verification_scalars_and_points_with_rng(proof, rng) {
            Err(e) => return Err(e),
            Ok(t) => t,
        };
        verify_given_verification_tuple(verification_tuple, pc_gens, bp_gens)
    }

    #[cfg(feature = "std")]
    pub fn verification_scalars_and_points(
        self,
        proof: &R1CSProof<C>,
    ) -> Result<VerificationTuple<C>, R1CSError> {
        let mut rng = rand::thread_rng();
        self.verification_scalars_and_points_with_rng(proof, &mut rng)
    }

    pub fn verification_scalars_and_points_with_rng<R: RngCore + CryptoRng>(
        self,
        proof: &R1CSProof<C>,
        rng: &mut R,
    ) -> Result<VerificationTuple<C>, R1CSError> {
        self.verification_scalars_and_points_core(proof, || C::ScalarField::rand(rng))
    }

    pub fn verification_scalars_and_points_with_given_randomness(
        self,
        proof: &R1CSProof<C>,
        randomness: C::ScalarField,
    ) -> Result<VerificationTuple<C>, R1CSError> {
        self.verification_scalars_and_points_core(proof, || randomness)
    }

    pub fn verification_scalars_and_points_core<F>(
        mut self,
        proof: &R1CSProof<C>,
        mut randomness_getter: F,
    ) -> Result<VerificationTuple<C>, R1CSError>
    where
        F: FnMut() -> C::ScalarField,
    {
        // pad
        let size = self.size();
        while size > self.num_multiplier {
            self.allocate_multiplier(None)?;
        }

        let n1 = self.size();

        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        let transcript = self.transcript.borrow_mut();
        transcript.merlin.append_u64(b"m", self.V.len() as u64);
        transcript
            .merlin
            .append_u64(b"c", self.vec_comms.len() as u64);
        for i in 0..self.vec_comms.len() {
            transcript
                .merlin
                .append_u64(b"c_i", self.vec_comms[i].1 as u64);
        }

        // number of commitments
        let ncomm = self.vec_comms.len();

        let (l_r_degrees, inner_product_degree) = degrees(ncomm);
        let vec_com_degrees = &l_r_degrees[2..];
        let t_poly_deg = t_poly_degree(inner_product_degree);
        let comm_t_deg = committed_t_degrees(inner_product_degree);

        // #[cfg(debug_assertions)]
        // {
        //     log::debug!("op_degree = {}", op_degree);
        //     log::debug!("t_poly_deg = {}", t_poly_deg);
        //     log::debug!("ops = {:?}", &ops);
        // }

        let degree_aLaR = l_r_degrees[0];
        let degree_aO = l_r_degrees[1];

        if proof.T.len() != comm_t_deg.len() {
            return Err(R1CSError::VerificationErrorWithReason(format!(
                "Invalid length for proof.T: {} {}",
                proof.T.len(),
                comm_t_deg.len()
            )));
        }
        transcript.validate_and_append_point(b"A_I1", &proof.A_I1)?;
        transcript.validate_and_append_point(b"A_O1", &proof.A_O1)?;
        transcript.validate_and_append_point(b"S1", &proof.S1)?;

        // Process the remaining constraints.
        self = self.create_randomized_constraints()?;

        let n = self.size();

        let transcript = self.transcript.borrow_mut();

        // If the number of multiplications is not 0 or a power of 2, then pad the circuit.

        let n2 = n - n1;
        let padded_n = n.next_power_of_two();
        let pad = padded_n - n;

        // log::debug!("padded_n = {}", padded_n);

        use crate::util;
        use core::iter;
        use dock_crypto_utils::ff::inner_product;

        // These points are the identity in the 1-phase unrandomized case.
        let (A_I2, A_O2, S2) = proof.second_phase_commitments();
        TranscriptProtocol::append_point(transcript, b"A_I2", &A_I2);
        TranscriptProtocol::append_point(transcript, b"A_O2", &A_O2);
        TranscriptProtocol::append_point(transcript, b"S2", &S2);

        let y = TranscriptProtocol::challenge_scalar::<C>(transcript, b"y");
        let z = TranscriptProtocol::challenge_scalar::<C>(transcript, b"z");

        let transcript = self.transcript.borrow_mut();
        for (d, T_d) in comm_t_deg.iter().copied().zip(proof.T.iter()) {
            transcript.append_index(b"t_poly degree", d as u64);
            transcript.validate_and_append_point(b"t_poly", T_d)?;
        }

        let u = TranscriptProtocol::challenge_scalar::<C>(transcript, b"u");
        let x = TranscriptProtocol::challenge_scalar::<C>(transcript, b"x");

        // #[cfg(debug_assertions)]
        // println!("verifier: x = {}", x);

        // compute powers for vector commitments
        // they are assigned the lowest powers and therefore the coefficients
        // in the combination are correspondingly assigned the highest powers

        let r = randomness_getter();

        // precompute x powers
        // xs = [1, x, x^2, .., x^t_poly_deg]
        let mut xs: Vec<C::ScalarField> = vec![C::ScalarField::zero(); t_poly_deg + 1];
        // rxs = [r, r.x, r.x^2, .., r.x^t_poly_deg]
        let mut rxs: Vec<C::ScalarField> = vec![C::ScalarField::zero(); t_poly_deg + 1];
        xs[0] = C::ScalarField::one();
        rxs[0] = r;
        for i in 1..xs.len() {
            xs[i] = xs[i - 1] * x;
            rxs[i] = rxs[i - 1] * x;
        }

        transcript.append_scalar::<C>(b"t_x", &proof.t_x);
        transcript.append_scalar::<C>(b"t_x_blinding", &proof.t_x_blinding);
        transcript.append_scalar::<C>(b"e_blinding", &proof.e_blinding);

        let w = TranscriptProtocol::challenge_scalar::<C>(transcript, b"w");

        let (wL, wR, wO, wV, wVCs, wc) = self.flattened_constraints(&z);

        // #[cfg(debug_assertions)]
        // log::debug!("verifier wVCs = {:?}", &wVCs);

        // Get IPP variables
        let (u_sq, u_inv_sq, s) = proof
            .ipp_proof
            .verification_scalars(padded_n, self.transcript.borrow_mut())
            .map_err(|_| R1CSError::VerificationError)?;

        let a = proof.ipp_proof.a;
        let b = proof.ipp_proof.b;

        let y_inv = y.inverse().ok_or(R1CSError::VerificationError)?;
        // [1, 1/y, 1/y^2, 1/y^3, ...]
        let y_inv_vec = util::exp_iter(y_inv)
            .take(padded_n)
            .collect::<Vec<C::ScalarField>>();

        // [wR_i*1/y^i, ..., 0,0,..]
        let yneg_wR = wR
            .into_iter()
            .zip(y_inv_vec.iter())
            .map(|(wRi, exp_y_inv)| wRi * exp_y_inv)
            .chain(iter::repeat(C::ScalarField::zero()).take(padded_n - self.num_multiplier))
            .collect::<Vec<C::ScalarField>>();

        let delta = inner_product(&yneg_wR[0..self.num_multiplier], &wL);

        let u_for_g = iter::repeat(C::ScalarField::one())
            .take(n1)
            .chain(iter::repeat(u).take(n2 + pad));

        let mut u_for_h = u_for_g.clone();

        let xwR = xs[degree_aLaR.0];

        let g_scalars = yneg_wR
            .iter()
            .zip(u_for_g)
            .zip(s.iter().take(padded_n)) // s is from folding
            .map(|((yneg_wRi, u_or_1), s_i)| u_or_1 * (xwR * yneg_wRi - a * s_i));

        // r(x)
        let mut h_scalars = Vec::with_capacity(padded_n);
        {
            let mut wL = wL.into_iter();
            let mut wO = wO.into_iter();
            let mut s = s.iter().rev().take(padded_n);
            let mut y_inv_vec = y_inv_vec.into_iter();

            for i in 0..padded_n {
                let y_inv = y_inv_vec.next().ok_or(R1CSError::VerificationError)?;
                let u_or_1 = u_for_h.next().ok_or(R1CSError::VerificationError)?;

                let si = s.next().ok_or(R1CSError::VerificationError)?;
                let wLi = wL.next().unwrap_or_default();
                let wOi = wO.next().unwrap_or_default();

                // compute right polynomial combination
                let mut comb = C::ScalarField::zero();
                {
                    // special terms
                    comb += xs[degree_aLaR.1] * wLi;
                    comb += xs[degree_aO.1] * wOi;

                    // add terms for vector commitments (higher degrees).
                    for j in 0..wVCs.len() {
                        let wVCji = wVCs[j].get(i).copied().unwrap_or_default();
                        comb += xs[vec_com_degrees[j].1] * wVCji;
                    }
                }

                // y^{-n} o (w_O + w_L * x + w_VCi * x^2)
                let res = u_or_1 * (y_inv * (comb - b * si) - C::ScalarField::one());

                h_scalars.push(res);
            }
        }

        // homomorphically evaluate t polynomial at x
        let mut T_points = vec![];
        let mut T_scalars = vec![];
        for (d, T_d) in comm_t_deg.iter().copied().zip(proof.T.iter().copied()) {
            #[cfg(debug_assertions)]
            {
                log::debug!("T[{}]: {} {}", d, T_d, rxs[d]);
            }
            T_points.push(T_d);
            T_scalars.push(rxs[d]);
        }

        let xI = xs[degree_aLaR.0];
        let xO = xs[degree_aO.0];
        let xS = xs[inner_product_degree + 1];

        // "Split" the MSM in 2 parts, one part uses points dependent on the proof and other part's
        // points are fixed generators G, H, B, B_blinding. There would only 1 MSM done eventually but
        // this makes batching more efficient
        let vscalar = (0..ncomm).map(|j| xs[vec_com_degrees[j].0]);
        let vcomm = self.vec_comms.iter().copied().map(|(comm, _)| comm);

        let proof_points = vcomm
            .chain(iter::once(proof.A_I1))
            .chain(iter::once(proof.A_O1))
            .chain(iter::once(proof.S1))
            .chain(iter::once(A_I2))
            .chain(iter::once(A_O2))
            .chain(iter::once(S2))
            .chain(self.V.iter().copied())
            .chain(T_points.iter().copied())
            .chain(proof.ipp_proof.L_vec.iter().copied())
            .chain(proof.ipp_proof.R_vec.iter().copied())
            .collect();

        let proof_scalars = vscalar
            .chain(iter::once(xI)) // A_I1
            .chain(iter::once(xO)) // A_O1
            .chain(iter::once(xS)) // S1
            .chain(iter::once(xI * u)) // A_I2
            .chain(iter::once(xO * u)) // A_O2
            .chain(iter::once(xS * u)) // S2
            .chain(wV.iter().map(|wVi| *wVi * rxs[inner_product_degree])) // V : at op-degree
            .chain(T_scalars.iter().copied()) // T_points
            .chain(u_sq) // ipp_proof.L_vec
            .chain(u_inv_sq) // ipp_proof.R_vec
            .collect::<Vec<_>>();

        let fixed_point_scalars: Vec<C::ScalarField> = iter::once(
            w * (proof.t_x - a * b) + r * (xs[inner_product_degree] * (wc + delta) - proof.t_x),
        ) // B : shift (wc + delta) to the right power
        .chain(iter::once(-proof.e_blinding - r * proof.t_x_blinding)) // B_blinding
        .chain(g_scalars) // G
        .chain(h_scalars) // H
        .collect::<Vec<_>>();

        Ok(VerificationTuple {
            proof_dependent_points: proof_points,
            proof_dependent_scalars: proof_scalars,
            fixed_point_scalars,
        })
    }
}

pub fn verify_given_verification_tuple<C: AffineRepr>(
    verification_tuple: VerificationTuple<C>,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
) -> Result<(), R1CSError> {
    let padded_n = verification_tuple.padded_n()?;

    msm_check(
        verification_tuple.proof_dependent_points,
        verification_tuple.proof_dependent_scalars,
        verification_tuple.fixed_point_scalars,
        padded_n,
        pc_gens,
        bp_gens,
    )
}

pub fn add_verification_tuple_to_rmc<C: AffineRepr>(
    verification_tuple: VerificationTuple<C>,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
    rmc: &mut RandomizedMultChecker<C>,
) -> Result<(), R1CSError> {
    let padded_n = verification_tuple.padded_n()?;
    let VerificationTuple {
        proof_dependent_points,
        proof_dependent_scalars,
        fixed_point_scalars: proof_independent_scalars,
    } = verification_tuple;
    let (b, s) = bases_and_scalars(
        proof_dependent_points,
        proof_dependent_scalars,
        proof_independent_scalars,
        padded_n,
        pc_gens,
        bp_gens,
    )?;
    rmc.add_many(b, &s, C::zero());
    Ok(())
}

pub fn add_pre_randomized_verification_tuple_to_rmc<C: AffineRepr>(
    verification_tuple: VerificationTuple<C>,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
    rmc: &mut RandomizedMultChecker<C>,
) -> Result<(), R1CSError> {
    let padded_n = verification_tuple.padded_n()?;
    let VerificationTuple {
        proof_dependent_points,
        proof_dependent_scalars,
        fixed_point_scalars: proof_independent_scalars,
    } = verification_tuple;
    let (b, s) = bases_and_scalars(
        proof_dependent_points,
        proof_dependent_scalars,
        proof_independent_scalars,
        padded_n,
        pc_gens,
        bp_gens,
    )?;
    for (b_i, s_i) in b.into_iter().zip(s.into_iter()) {
        rmc.add(b_i, s_i);
    }
    Ok(())
}

#[derive(Clone)]
pub struct VerificationTuple<C: AffineRepr> {
    pub proof_dependent_points: Vec<C>,
    pub proof_dependent_scalars: Vec<C::ScalarField>,
    pub fixed_point_scalars: Vec<C::ScalarField>,
}

impl<C: AffineRepr> VerificationTuple<C> {
    /// Number of multipliers in the circuit which is same as the size of G (or H) vector used in
    /// the MSM
    pub fn padded_n(&self) -> Result<u32, R1CSError> {
        let scalar_minus_g_and_h = self
            .fixed_point_scalars
            .len()
            .checked_sub(2)
            .ok_or_else(|| R1CSError::VerificationErrorWithReason("verification tuple is malformed: proof_independent_scalars must contain at least 2 elements".to_string()))?;
        // This can be safely cast to 32 since parameters length always fits in u32
        Ok((scalar_minus_g_and_h / 2) as u32)
    }
}

pub fn msm_check<C: AffineRepr>(
    proof_dependent_points: Vec<C>,
    proof_dependent_scalars: Vec<C::ScalarField>,
    proof_independent_scalars: Vec<C::ScalarField>,
    padded_n: u32,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
) -> Result<(), R1CSError> {
    let (b, s) = bases_and_scalars(
        proof_dependent_points,
        proof_dependent_scalars,
        proof_independent_scalars,
        padded_n,
        pc_gens,
        bp_gens,
    )?;
    // let start = std::time::Instant::now();
    let mega_check = C::Group::msm_unchecked(&b, &s);
    // println!("msm_check took {:?}", start.elapsed());
    if !mega_check.is_zero() {
        return Err(R1CSError::VerificationError);
    }

    Ok(())
}

fn bases_and_scalars<C: AffineRepr>(
    proof_dependent_points: Vec<C>,
    proof_dependent_scalars: Vec<C::ScalarField>,
    proof_independent_scalars: Vec<C::ScalarField>,
    padded_n: u32,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
) -> Result<(Vec<C>, Vec<C::ScalarField>), R1CSError> {
    // We are performing a single-party circuit proof, so party index is 0.
    let gens = bp_gens.share(0);

    if bp_gens.gens_capacity < padded_n {
        return Err(R1CSError::InvalidGeneratorsLength(
            bp_gens.gens_capacity,
            padded_n,
        ));
    }

    use core::iter;
    let fixed_points = iter::once(pc_gens.B)
        .chain(iter::once(pc_gens.B_blinding))
        .chain(gens.G(padded_n).copied())
        .chain(gens.H(padded_n).copied());

    let b = proof_dependent_points
        .into_iter()
        .chain(fixed_points)
        .collect::<Vec<_>>();

    let s = proof_dependent_scalars
        .into_iter()
        .chain(proof_independent_scalars)
        .collect::<Vec<_>>();

    // println!("bases_and_scalars {}", b.len());

    Ok((b, s))
}
