use crate::curve_tree::{Root, SelectAndRerandomizePathWithDivisorComms};
use crate::error::Result;
use crate::parameters::SelRerandProofParametersNew;
use crate::prover::{constraints_for_dlogs, select_non_root, select_root, VC_LEN};
use crate::select::multi_select_public_set_ext_challenge;
use ark_dlog_gadget::dlog::{
    commit_witness_chunks_verifier, DiscreteLogParameters, DivisorComms, PointWithDlog,
};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_std::vec;
use ark_std::vec::Vec;
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Verifier};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};

impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > SelectAndRerandomizePathWithDivisorComms<L, P0, P1>
{
    pub fn select_and_rerandomize_verifier_gadget<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        root: &Root<L, 1, P0, P1>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandProofParametersNew<P0, P1, Parameters0, Parameters1>,
    ) -> Result<()> {
        let mut even_node_divisors = vec![];
        let mut odd_node_divisors = vec![];

        let root_is_even = match root {
            Root::Even(root) => {
                let child = &self.path.odd_commitments[0];
                let all_x_coords = &root.x_coord_children[0];
                let (x_var, y_var, x, y) = select_root(
                    even_verifier,
                    &parameters.odd_parameters.sl_params.delta,
                    child,
                    all_x_coords,
                    None,
                );
                let p = commit_dlog_and_divisor::<_, _, Parameters0>(
                    even_verifier,
                    &self.even_divisor_comms[0],
                );
                even_node_divisors.push((x_var.into(), y_var.into(), x, y, p));
                true
            }
            Root::Odd(root) => {
                let child = &self.path.even_commitments[0];
                let all_x_coords = &root.x_coord_children[0];
                let (x_var, y_var, x, y) = select_root(
                    odd_verifier,
                    &parameters.even_parameters.sl_params.delta,
                    child,
                    all_x_coords,
                    None,
                );
                let p = commit_dlog_and_divisor::<_, _, Parameters1>(
                    odd_verifier,
                    &self.odd_divisor_comms[0],
                );
                odd_node_divisors.push((x_var.into(), y_var.into(), x, y, p));
                false
            }
        };

        let mut commit_even = || {
            // Last item of self.path.even_commitments.len() is for leaf
            for parent_index in 0..(self.path.even_commitments.len() - 1) {
                // If the root is at even level, then the first element in self.path.odd_commitments will be child
                // of the root and its already processed in `root_level_select_and_rerandomize`
                let child_index = if root_is_even {
                    parent_index + 1
                } else {
                    parent_index
                };

                let child = &self.path.odd_commitments[child_index];
                let variables = even_verifier
                    .commit_vec(L, self.path.even_commitments[parent_index])
                    .iter()
                    .map(|v| LinearCombination::<P0::ScalarField>::from(*v))
                    .collect();
                let (x_var, y_var, x, y) = select_non_root(
                    even_verifier,
                    &parameters.odd_parameters.sl_params.delta,
                    child,
                    variables,
                    None,
                );
                let divisor_comms = &self.even_divisor_comms[child_index];
                let p = commit_dlog_and_divisor::<_, _, Parameters0>(even_verifier, divisor_comms);
                even_node_divisors.push((x_var.into(), y_var.into(), x, y, p))
            }
        };

        let mut commit_odd = || {
            for parent_index in 0..self.path.odd_commitments.len() {
                // If the root is at odd level, then the first element in self.path.even_commitments will be child
                // of the root and its already processed in `root_level_select_and_rerandomize`
                let child_index = if !root_is_even {
                    parent_index + 1
                } else {
                    parent_index
                };

                let child = &self.path.even_commitments[child_index];
                let variables = odd_verifier
                    .commit_vec(L, self.path.odd_commitments[parent_index])
                    .iter()
                    .map(|v| LinearCombination::<P1::ScalarField>::from(*v))
                    .collect();
                let (x_var, y_var, x, y) = select_non_root(
                    odd_verifier,
                    &parameters.even_parameters.sl_params.delta,
                    child,
                    variables,
                    None,
                );
                let divisor_comms = &self.odd_divisor_comms[child_index];
                let p = commit_dlog_and_divisor::<_, _, Parameters1>(odd_verifier, divisor_comms);
                odd_node_divisors.push((x_var.into(), y_var.into(), x, y, p))
            }
        };

        #[cfg(not(feature = "parallel"))]
        {
            commit_even();
            commit_odd();
        }

        #[cfg(feature = "parallel")]
        rayon::join(|| commit_even(), || commit_odd());

        constraints_for_dlogs::<_, _, _, _, P0, P1, Parameters0, Parameters1>(
            even_verifier,
            odd_verifier,
            &parameters.even_parameters.table_b_blinding,
            &parameters.odd_parameters.table_b_blinding,
            even_node_divisors,
            odd_node_divisors,
        )?;
        Ok(())
    }

    pub fn select_and_rerandomize_verifier_gadget_multi<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        paths: &[Self],
        root: &Root<L, 1, P0, P1>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandProofParametersNew<P0, P1, Parameters0, Parameters1>,
    ) -> Result<()> {
        let num_paths = paths.len();

        let mut even_node_divisors = Vec::with_capacity(num_paths);
        let mut odd_node_divisors = Vec::with_capacity(num_paths);

        let root_is_even = match root {
            Root::Even(root_node) => {
                let delta = parameters.odd_parameters.sl_params.delta;
                let all_x_coords = &root_node.x_coord_children[0];

                let re_randomized_children = (0..num_paths)
                    .map(|i| paths[i].path.odd_commitments[0])
                    .collect::<Vec<_>>();
                let even_node_comms = paths
                    .iter()
                    .map(|p| p.even_divisor_comms.clone())
                    .collect::<Vec<_>>();

                Self::process_root_for_all::<Parameters0>(
                    even_verifier,
                    re_randomized_children,
                    all_x_coords,
                    delta,
                    &mut even_node_divisors,
                    &even_node_comms,
                );
                true
            }
            Root::Odd(root_node) => {
                let delta = parameters.even_parameters.sl_params.delta;
                let all_x_coords = &root_node.x_coord_children[0];

                let re_randomized_children = (0..num_paths)
                    .map(|i| paths[i].path.even_commitments[0])
                    .collect::<Vec<_>>();
                let odd_node_comms = paths
                    .iter()
                    .map(|p| p.odd_divisor_comms.clone())
                    .collect::<Vec<_>>();

                SelectAndRerandomizePathWithDivisorComms::<L, P1, P0>::process_root_for_all::<
                    Parameters1,
                >(
                    odd_verifier,
                    re_randomized_children,
                    all_x_coords,
                    delta,
                    &mut odd_node_divisors,
                    &odd_node_comms,
                );
                false
            }
        };

        for path_idx in 0..num_paths {
            let path = &paths[path_idx];
            let path_even_comms = &path.even_divisor_comms;
            let path_odd_comms = &path.odd_divisor_comms;

            if even_node_divisors.len() <= path_idx {
                even_node_divisors.push(vec![]);
            }
            if odd_node_divisors.len() <= path_idx {
                odd_node_divisors.push(vec![]);
            }

            // Process even non-root nodes
            // Last item of path.path.even_commitments is for leaf
            for parent_index in 0..(path.path.even_commitments.len() - 1) {
                let child_index = if root_is_even {
                    parent_index + 1
                } else {
                    parent_index
                };

                let child = &path.path.odd_commitments[child_index];
                let variables: Vec<LinearCombination<F0>> = even_verifier
                    .commit_vec(L, path.path.even_commitments[parent_index])
                    .iter()
                    .map(|v| (*v).into())
                    .collect();

                let (x_var, y_var, x, y) = select_non_root(
                    even_verifier,
                    &parameters.odd_parameters.sl_params.delta,
                    child,
                    variables,
                    None,
                );

                let divisor_comms = &path_even_comms[child_index];
                let p = commit_dlog_and_divisor::<_, _, Parameters0>(even_verifier, divisor_comms);
                even_node_divisors[path_idx].push((x_var.into(), y_var.into(), x, y, p));
            }

            // Process odd non-root nodes
            for parent_index in 0..path.path.odd_commitments.len() {
                let child_index = if !root_is_even {
                    parent_index + 1
                } else {
                    parent_index
                };

                let child = &path.path.even_commitments[child_index];
                let variables: Vec<LinearCombination<F1>> = odd_verifier
                    .commit_vec(L, path.path.odd_commitments[parent_index])
                    .iter()
                    .map(|v| (*v).into())
                    .collect();

                let (x_var, y_var, x, y) = select_non_root(
                    odd_verifier,
                    &parameters.even_parameters.sl_params.delta,
                    child,
                    variables,
                    None,
                );

                let divisor_comms = &path_odd_comms[child_index];
                let p = commit_dlog_and_divisor::<_, _, Parameters1>(odd_verifier, divisor_comms);
                odd_node_divisors[path_idx].push((x_var.into(), y_var.into(), x, y, p));
            }
        }

        constraints_for_dlogs::<_, _, _, _, P0, P1, Parameters0, Parameters1>(
            even_verifier,
            odd_verifier,
            &parameters.even_parameters.table_b_blinding,
            &parameters.odd_parameters.table_b_blinding,
            even_node_divisors.into_iter().flatten(),
            odd_node_divisors.into_iter().flatten(),
        )?;
        Ok(())
    }

    fn process_root_for_all<Parameters: DiscreteLogParameters>(
        verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        re_randomized_children: Vec<Affine<P1>>,
        all_x_coords: &[F0],
        delta: Affine<P1>,
        node_divisors: &mut Vec<
            Vec<(
                LinearCombination<F0>,
                LinearCombination<F0>,
                F0,
                F0,
                Box<PointWithDlog<F0, Parameters>>,
            )>,
        >,
        node_comms: &[Vec<DivisorComms<Affine<P0>>>],
    ) {
        let num_paths = re_randomized_children.len();

        // Allocate x-coordinates for all selected children
        let x_vars: Vec<LinearCombination<F0>> = (0..num_paths)
            .map(|_| verifier.allocate(None).unwrap().into())
            .collect();

        // Get challenge and enforce multi-select on public set
        let challenge = verifier
            .transcript()
            .challenge_scalar(b"challenge-for-multi_select");
        multi_select_public_set_ext_challenge(verifier, x_vars.clone(), all_x_coords, challenge);

        // For each path, process its selected child of root
        for (path_idx, (x_var, rerandomized_child)) in x_vars
            .into_iter()
            .zip(re_randomized_children.into_iter())
            .enumerate()
        {
            // Add rerandomized child to transcript
            verifier
                .transcript()
                .append(b"rerandomized_child", &rerandomized_child);

            let y_var = verifier.allocate(None).unwrap().into();
            let (x, y) = (rerandomized_child + delta).into_affine().xy().unwrap();

            let path_divisor_comms = &node_comms[path_idx][0];

            let p = commit_dlog_and_divisor::<_, _, Parameters>(verifier, path_divisor_comms);

            node_divisors.push(vec![(x_var, y_var, x, y, p)]);
        }
    }
}

pub fn commit_dlog_and_divisor<
    F: PrimeField,
    C: AffineRepr<ScalarField = F>,
    Parameters: DiscreteLogParameters,
>(
    verifier: &mut Verifier<MerlinTranscript, C>,
    divisor_commitments: &DivisorComms<C>,
) -> Box<PointWithDlog<F, Parameters>> {
    commit_witness_chunks_verifier(verifier, divisor_commitments, VC_LEN as usize)
}
