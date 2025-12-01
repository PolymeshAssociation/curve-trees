use ark_ec::short_weierstrass::Projective;
use ark_ec::CurveGroup;
use bulletproofs::r1cs::*;

use crate::error::Error;
use crate::single_level_select_and_rerandomize::*;

use crate::curve_tree::{CurveTree, CurveTreeNode, Root, SelRerandParameters, SelectAndRerandomizeMultiPath};
use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_ff::{PrimeField, Zero};
use ark_std::{vec, vec::Vec};
use core::borrow::BorrowMut;
use dock_crypto_utils::transcript::MerlinTranscript;

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > CurveTree<L, M, P0, P1>
{
    /// Adds the root to a randomized multi path provided by the prover
    pub fn batched_select_and_rerandomize_verification_commitments(
        &self,
        randomized_path: &mut SelectAndRerandomizeMultiPath<L, M, P0, P1>,
    ) -> Result<(), Error> {
        let num_indices = randomized_path.num_indices();
        if num_indices > M as u32 {
            return Err(Error::MoreIndicesThanSupportedBatchSize(
                num_indices,
                M as u32,
            ));
        }

        match self {
            Self::Odd(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len(),
                    randomized_path.odd_commitments.len()
                );
                let mut sum_of_roots = Projective::<P1>::zero();
                for i in 0..num_indices {
                    sum_of_roots += ct.commitment(i as usize)
                }
                let mut odd_commitments_with_root = vec![sum_of_roots.into_affine()];
                odd_commitments_with_root.append(&mut randomized_path.odd_commitments);
                randomized_path.odd_commitments = odd_commitments_with_root;
            }
            Self::Even(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len() + 1,
                    randomized_path.odd_commitments.len()
                );
                let mut sum_of_roots = Projective::<P0>::zero();
                for i in 0..num_indices {
                    sum_of_roots += ct.commitment(i as usize)
                }
                let mut even_commitments_with_root = vec![sum_of_roots.into_affine()];
                even_commitments_with_root.append(&mut randomized_path.even_commitments);
                randomized_path.even_commitments = even_commitments_with_root;
            }
        };
        Ok(())
    }
}

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > CurveTree<L, M, P0, P1>
{
    pub fn batched_select_and_rerandomize_verifier_gadget<T: BorrowMut<MerlinTranscript>>(
        &self,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        mut randomized_path: SelectAndRerandomizeMultiPath<L, M, P0, P1>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<Vec<Affine<P0>>, Error> {
        self.batched_select_and_rerandomize_verification_commitments(&mut randomized_path)?;
        // The even and odd commitments do not include the selected leaves, their sum should equal the height of the tree.
        debug_assert_eq!(
            self.height(),
            randomized_path.even_commitments.len() + randomized_path.odd_commitments.len()
        );

        randomized_path.even_verifier_gadget_old(even_verifier, parameters, self)?;
        randomized_path.odd_verifier_gadget_old(odd_verifier, parameters, self)?;

        Ok(randomized_path.get_rerandomized_leaves())
    }
}

impl<
        const L: usize,
        const M: usize,
        F: PrimeField,
        P0: SWCurveConfig<BaseField = F> + Copy + Send,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = F> + Copy + Send,
    > SelectAndRerandomizeMultiPath<L, M, P0, P1>
{
    /// Get the public rerandomization of the selected commitments
    pub fn get_rerandomized_leaves(&self) -> Vec<Affine<P0>> {
        self.selected_commitments.clone()
    }

    pub fn even_verifier_gadget_old<T: BorrowMut<MerlinTranscript>>(
        &self,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        parameters: &SelRerandParameters<P0, P1>,
        ct: &CurveTree<L, M, P0, P1>,
    ) -> Result<(), Error> {
        // Determine the parity of the root:
        let root_is_odd = self.even_commitments.len() + 1 == self.odd_commitments.len();
        if !root_is_odd {
            assert!(self.even_commitments.len() == self.odd_commitments.len());
        }

        let num_indices = self.ensure_acceptable_num_indices()? as usize;

        for parent_index in 0..self.even_commitments.len() {
            let odd_index = if root_is_odd {
                parent_index + 1
            } else {
                parent_index
            };
            let variables: Vec<LinearCombination<P0::ScalarField>> =
                if parent_index == 0 && !root_is_odd {
                    let children = match &ct {
                        CurveTree::Even(root) => {
                            // todo why not branch on this to determine if the root is even and if so extract the children, otherwise commit to get first set of vars
                            if let CurveTreeNode::InnerNode(inner_node) = root {
                                let mut children_xs = Vec::new();
                                for i in 0..num_indices {
                                    children_xs.append(&mut inner_node.x_coord_children[i].to_vec())
                                }
                                children_xs
                            } else {
                                unreachable!("Curve tree has at least one level")
                            }
                        }
                        _ => unreachable!("Root is even"),
                    };
                    children.into_iter().map(constant).collect()
                } else {
                    let variables =
                        even_verifier.commit_vec(L * num_indices, self.even_commitments[parent_index]);
                    variables
                        .iter()
                        .map(|v| LinearCombination::<P0::ScalarField>::from(*v))
                        .collect()
                };
            assert_eq!(variables.len(), num_indices * L);
            single_level_batched_select_and_rerandomize(
                even_verifier,
                &parameters.odd_parameters,
                num_indices as u32,
                &self.odd_commitments[odd_index],
                variables,
                None,
                None,
            )?;
        }
        Ok(())
    }

    pub fn odd_verifier_gadget_old<T: BorrowMut<MerlinTranscript>>(
        &self,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        ct: &CurveTree<L, M, P0, P1>,
    ) -> Result<(), Error> {
        // Determine the parity of the root:
        let root_is_odd = self.even_commitments.len() + 1 == self.odd_commitments.len();
        if !root_is_odd {
            assert!(self.even_commitments.len() == self.odd_commitments.len());
        }

        let num_indices = self.ensure_acceptable_num_indices()? as usize;

        for parent_index in 0..self.odd_commitments.len() {
            let even_index = if root_is_odd {
                parent_index
            } else {
                parent_index + 1
            };

            let variables: Vec<LinearCombination<P1::ScalarField>> = if parent_index == 0
                && root_is_odd
            {
                let children = match &ct {
                    CurveTree::Odd(root) => {
                        if let CurveTreeNode::InnerNode(inner_node) = root {
                            let mut children_xs = Vec::new();
                            for i in 0..num_indices {
                                children_xs.append(&mut inner_node.x_coord_children[i].to_vec())
                            }
                            children_xs
                        } else {
                            unreachable!("Curve tree has at least one level")
                        }
                    }
                    _ => unreachable!("Root is odd"),
                };
                children.into_iter().map(constant).collect()
            } else {
                let variables = odd_verifier.commit_vec(L * num_indices, self.odd_commitments[parent_index]);
                variables
                    .iter()
                    .map(|v| LinearCombination::<P1::ScalarField>::from(*v))
                    .collect()
            };
            assert_eq!(variables.len(), num_indices * L);

            if parent_index < self.odd_commitments.len() - 1 {
                single_level_batched_select_and_rerandomize(
                    odd_verifier,
                    &parameters.even_parameters,
                    num_indices as u32,
                    &self.even_commitments[even_index],
                    variables,
                    None,
                    None,
                )?;
            } else {
                // Split the variables of the vector commitments into chunks corresponding to the `num_indices` parents.
                let chunks = variables.chunks_exact(variables.len() / num_indices);
                for (i, chunk) in chunks.enumerate() {
                    single_level_select_and_rerandomize(
                        odd_verifier,
                        &parameters.even_parameters,
                        &self.selected_commitments[i],
                        chunk.to_vec(),
                        None,
                        None,
                    );
                }
            };
        }
        Ok(())
    }

    pub fn batched_select_and_rerandomize_verifier_gadget<T: BorrowMut<MerlinTranscript>>(
        &self,
        root: &Root<L, M, P0, P1>,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<Vec<Affine<P0>>, Error> {

        let num_indices = self.ensure_acceptable_num_indices()?;

        let root_is_even = match root {
            Root::Even(root) => {
                let mut children = Vec::with_capacity(L * num_indices as usize);
                for i in 0..num_indices {
                    children.extend_from_slice(root.x_coord_children[i as usize].as_slice());
                }
                root_level_batched_select_and_rerandomize(
                    even_verifier,
                    &parameters.odd_parameters,
                    num_indices,
                    &self.odd_commitments[0],
                    children,
                    None,
                    None,
                )?;
                true
            }
            Root::Odd(root) => {
                let mut children = Vec::with_capacity(L * num_indices as usize);
                for i in 0..num_indices {
                    children.extend_from_slice(root.x_coord_children[i as usize].as_slice());
                }
                root_level_batched_select_and_rerandomize(
                    odd_verifier,
                    &parameters.even_parameters,
                    num_indices,
                    &self.even_commitments[0],
                    children,
                    None,
                    None,
                )?;
                false
            }
        };

        let verify_even = |even_verifier: &mut Verifier<T, Affine<P0>>| {
            self.even_verifier_gadget(root_is_even, num_indices, even_verifier, &parameters.odd_parameters)
        };

        let verify_odd = |odd_verifier: &mut Verifier<T, Affine<P1>>| {
            self.odd_verifier_gadget(root_is_even, num_indices, odd_verifier, &parameters.even_parameters)
        };

        #[cfg(not(feature = "parallel"))]
        let res_even = verify_even(even_verifier);

        #[cfg(not(feature = "parallel"))]
        let res_odd = verify_odd(odd_verifier);

        #[cfg(feature = "parallel")]
        let (res_even, res_odd) = rayon::join(|| verify_even(even_verifier), || verify_odd(odd_verifier));

        res_even?;
        res_odd?;

        Ok(self.get_rerandomized_leaves())
    }

    /// Verify multiple multi-paths with a common root
    pub fn batched_select_and_rerandomize_verifier_gadget_for_common_root<T: BorrowMut<MerlinTranscript>>(
        paths: &[Self],
        root: &Root<L, M, P0, P1>,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<Vec<Vec<Affine<P0>>>, Error> {
        if paths.is_empty() {
            return Err(Error::PathsLengthMustBeGreaterThanZero);
        }

        let mut all_rerandomized_leaves = Vec::with_capacity(paths.len());

        for path in paths {
            let num_indices = path.ensure_acceptable_num_indices()?;

            let root_is_even = match root {
                Root::Even(root) => {
                    let mut children = Vec::with_capacity(L * num_indices as usize);
                    for i in 0..num_indices {
                        children.extend_from_slice(root.x_coord_children[i as usize].as_slice());
                    }
                    root_level_batched_select_and_rerandomize(
                        even_verifier,
                        &parameters.odd_parameters,
                        num_indices,
                        &path.odd_commitments[0],
                        children,
                        None,
                        None,
                    )?;
                    true
                }
                Root::Odd(root) => {
                    let mut children = Vec::with_capacity(L * num_indices as usize);
                    for i in 0..num_indices {
                        children.extend_from_slice(root.x_coord_children[i as usize].as_slice());
                    }
                    root_level_batched_select_and_rerandomize(
                        odd_verifier,
                        &parameters.even_parameters,
                        num_indices,
                        &path.even_commitments[0],
                        children,
                        None,
                        None,
                    )?;
                    false
                }
            };

            let verify_even = |even_verifier: &mut Verifier<T, Affine<P0>>| {
                path.even_verifier_gadget(root_is_even, num_indices, even_verifier, &parameters.odd_parameters)
            };

            let verify_odd = |odd_verifier: &mut Verifier<T, Affine<P1>>| {
                path.odd_verifier_gadget(root_is_even, num_indices, odd_verifier, &parameters.even_parameters)
            };

            #[cfg(not(feature = "parallel"))]
            let res_even = verify_even(even_verifier);

            #[cfg(not(feature = "parallel"))]
            let res_odd = verify_odd(odd_verifier);

            #[cfg(feature = "parallel")]
            let (res_even, res_odd) = rayon::join(|| verify_even(even_verifier), || verify_odd(odd_verifier));

            res_even?;
            res_odd?;

            all_rerandomized_leaves.push(path.get_rerandomized_leaves());
        }

        Ok(all_rerandomized_leaves)
    }

    pub fn even_verifier_gadget<T: BorrowMut<MerlinTranscript>>(
        &self,
        root_is_even: bool,
        num_indices: u32,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_parameters: &SingleLayerParameters<P1>,
    ) -> Result<(), Error> {
        for parent_index in 0..self.even_commitments.len() {
            // If the root is at even level, then the first element in self.odd_commitments will be child
            // of the root and its already processed in `root_level_select_and_rerandomize`
            let child_index = if root_is_even {
                parent_index + 1
            } else {
                parent_index
            };
            let variables =
                even_verifier.commit_vec(L * num_indices as usize, self.even_commitments[parent_index])
                    .into_iter()
                    .map(|v| LinearCombination::<P0::ScalarField>::from(v))
                    .collect();
            single_level_batched_select_and_rerandomize(
                even_verifier,
                odd_parameters,
                num_indices,
                &self.odd_commitments[child_index],
                variables,
                None,
                None,
            )?;
        }
        Ok(())
    }

    pub fn odd_verifier_gadget<T: BorrowMut<MerlinTranscript>>(
        &self,
        root_is_even: bool,
        num_indices: u32,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        even_parameters: &SingleLayerParameters<P0>,
    ) -> Result<(), Error> {
        for parent_index in 0..self.odd_commitments.len() {
            // If the root is at odd level, then the first element in self.even_commitments will be child
            // of the root and its already processed in `root_level_select_and_rerandomize`
            let child_index = if !root_is_even {
                parent_index + 1
            } else {
                parent_index
            };
            let variables =
                odd_verifier.commit_vec(L * num_indices as usize, self.odd_commitments[parent_index])
                    .into_iter()
                    .map(|v| LinearCombination::<P1::ScalarField>::from(v))
                    .collect();
            if parent_index < self.odd_commitments.len() - 1 {
                single_level_batched_select_and_rerandomize(
                    odd_verifier,
                    even_parameters,
                    num_indices,
                    &self.even_commitments[child_index],
                    variables,
                    None,
                    None,
                )?;
            } else {
                // Split the variables of the vector commitments into chunks corresponding to the `num_indices` parents.
                let chunks = variables.chunks_exact(variables.len() / num_indices as usize);
                for (i, chunk) in chunks.enumerate() {
                    single_level_select_and_rerandomize(
                        odd_verifier,
                        even_parameters,
                        &self.selected_commitments[i],
                        chunk.to_vec(),
                        None,
                        None,
                    );
                }
            }
        }
        Ok(())
    }

    /// Number of leaf indices for which this multi-path was created.
    pub fn num_indices(&self) -> u32 {
        self.selected_commitments.len() as u32
    }

    fn ensure_acceptable_num_indices(&self) -> Result<u32, Error> {
        let num_indices = self.num_indices();
        if num_indices as usize > M {
            Err(Error::MoreIndicesThanSupportedBatchSize(
                num_indices,
                M as u32,
            ))
        } else {
            Ok(num_indices)
        }
    }
}
