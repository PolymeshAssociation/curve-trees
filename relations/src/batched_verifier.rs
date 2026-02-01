use crate::batched_prover::{
    batched_select_and_accumulate_non_root, batched_select_and_accumulate_root,
};
use crate::curve_tree::{Root, SelectAndRerandomizeMultiPathWithDivisorComms};
use crate::error::{Result};
use crate::prover::{constraints_for_dlogs};
use crate::select::select;
use crate::verifier::commit_dlog_and_divisor;
use ark_dlog_gadget::dlog::{DiscreteLogParameters};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_std::vec::Vec;
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Variable, Verifier};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use crate::parameters::SelRerandProofParametersNew;

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > SelectAndRerandomizeMultiPathWithDivisorComms<L, M, P0, P1>
{
    /// Divisor-based batched select and rerandomize verifier gadget.
    pub fn batched_select_and_rerandomize_verifier_gadget<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        root: &Root<L, M, P0, P1>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandProofParametersNew<P0, P1, Parameters0, Parameters1>,
    ) -> Result<()> {
        let num_indices = self.path.selected_commitments.len() as u32;
        // assert_eq!(leaf_comms.len(), num_indices as usize);

        let mut even_node_divisors = Vec::new();
        let mut odd_node_divisors = Vec::new();

        // Process root level and learn if it's even or odd
        let root_is_even = match root {
            Root::Even(root_node) => {
                let mut all_x_coords: Vec<F0> = Vec::with_capacity(L * num_indices as usize);
                for i in 0..num_indices as usize {
                    all_x_coords.extend_from_slice(root_node.x_coord_children[i].as_slice());
                }

                let (_, sum_x_var, sum_y_var) = batched_select_and_accumulate_root::<F0, P1, _>(
                    even_verifier,
                    num_indices,
                    &all_x_coords,
                    None,
                );

                let shifted_rerandomized = (self.path.odd_commitments[0]
                    + (parameters.odd_parameters.sl_params.delta * P1::ScalarField::from(num_indices)))
                .into_affine();
                let (x, y) = shifted_rerandomized.xy().unwrap();

                let p = commit_dlog_and_divisor::<_, _, Parameters0>(even_verifier, &self.even_divisor_comms[0]);
                even_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
                true
            }
            Root::Odd(root_node) => {
                let mut all_x_coords: Vec<F1> = Vec::with_capacity(L * num_indices as usize);
                for i in 0..num_indices as usize {
                    all_x_coords.extend_from_slice(root_node.x_coord_children[i].as_slice());
                }

                let (_, sum_x_var, sum_y_var) = batched_select_and_accumulate_root::<F1, P0, _>(
                    odd_verifier,
                    num_indices,
                    &all_x_coords,
                    None,
                );

                let shifted_rerandomized = (self.path.even_commitments[0]
                    + (parameters.even_parameters.sl_params.delta * P0::ScalarField::from(num_indices)))
                .into_affine();
                let (x, y) = shifted_rerandomized.xy().unwrap();

                let p = commit_dlog_and_divisor::<_, _, Parameters1>(odd_verifier, &self.odd_divisor_comms[0]);
                odd_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
                false
            }
        };

        // Process non-root nodes using closures (similar to verifier.rs pattern)
        let mut commit_even = || {
            let even_length = self.path.even_commitments.len();
            for parent_index in 0..even_length {
                let child_index = if root_is_even {
                    parent_index + 1
                } else {
                    parent_index
                };

                let children_vars: Vec<Variable<F0>> = even_verifier.commit_vec(
                    L * num_indices as usize,
                    self.path.even_commitments[parent_index],
                );
                let children_vars: Vec<LinearCombination<F0>> =
                    children_vars.into_iter().map(|v| v.into()).collect();
                let (_, sum_x_var, sum_y_var) = batched_select_and_accumulate_non_root::<F0, P1, _>(
                    even_verifier,
                    num_indices,
                    children_vars,
                    None,
                );

                let shifted_rerandomized = (self.path.odd_commitments[child_index]
                    + (parameters.odd_parameters.sl_params.delta * P1::ScalarField::from(num_indices)))
                .into_affine();
                let (x, y) = shifted_rerandomized.xy().unwrap();

                let p = commit_dlog_and_divisor::<_, _, Parameters0>(even_verifier, &self.even_divisor_comms[child_index]);
                even_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
            }
        };

        commit_even();

        let mut commit_odd = || {
            let odd_length = self.path.odd_commitments.len();
            for parent_index in 0..odd_length {
                let child_index = if !root_is_even {
                    parent_index + 1
                } else {
                    parent_index
                };

                // Skip the last level - that's leaves, handled separately
                if parent_index < (odd_length - 1) {
                    let children_vars: Vec<Variable<F1>> = odd_verifier
                        .commit_vec(L * num_indices as usize, self.path.odd_commitments[parent_index]);
                    let children_vars: Vec<LinearCombination<F1>> =
                        children_vars.into_iter().map(|v| v.into()).collect();
                    let (_, sum_x_var, sum_y_var) = batched_select_and_accumulate_non_root::<F1, P0, _>(
                        odd_verifier,
                        num_indices,
                        children_vars,
                        None,
                    );

                    let shifted_rerandomized = (self.path.even_commitments[child_index]
                        + (parameters.even_parameters.sl_params.delta * P0::ScalarField::from(num_indices)))
                    .into_affine();
                    let (x, y) = shifted_rerandomized.xy().unwrap();

                    let p = commit_dlog_and_divisor::<_, _, Parameters1>(odd_verifier, &self.odd_divisor_comms[child_index]);
                    odd_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
                }
            }
        };

        commit_odd();

        // Process leaf level - individual verification for each leaf
        {
            let odd_length = self.path.odd_commitments.len();
            let parent_index = odd_length - 1;

            // Commit to parent to get variables

            let children_vars: Vec<Variable<F1>> = odd_verifier
                .commit_vec(L * num_indices as usize, self.path.odd_commitments[parent_index]);
            let chunk_size = children_vars.len() / num_indices as usize;
            let chunks: Vec<_> = children_vars.chunks_exact(chunk_size).collect();

            for (i, chunk) in chunks.iter().enumerate() {
                let x_var: LinearCombination<F1> = odd_verifier.allocate(None).unwrap().into();
                let y_var = odd_verifier.allocate(None).unwrap().into();

                // Select
                let children_lc: Vec<LinearCombination<F1>> =
                    chunk.iter().map(|v| (*v).into()).collect();
                select(odd_verifier, x_var.clone(), children_lc.into_iter());

                // Add transcript entry for rerandomized leaf
                odd_verifier
                    .transcript()
                    .append(b"rerandomized_child", &self.path.selected_commitments[i]);

                let rerandomized_plus_delta =
                    (self.path.selected_commitments[i] + parameters.even_parameters.sl_params.delta).into_affine();
                let (x, y) = rerandomized_plus_delta.xy().unwrap();

                // TODO: Fix index cacl. it should check for errors first
                let p = commit_dlog_and_divisor::<_, _, Parameters1>(odd_verifier, &self.odd_divisor_comms[self.odd_divisor_comms.len() - num_indices as usize + i]);
                odd_node_divisors.push((x_var, y_var, x, y, p));
            }
        }
        
        constraints_for_dlogs::<_, _, _, _, P0, P1, Parameters0, Parameters1>(
            even_verifier,
            odd_verifier,
            &parameters.even_parameters.table,
            &parameters.odd_parameters.table,
            even_node_divisors,
            odd_node_divisors,
        )?;

        Ok(())
    }
}
