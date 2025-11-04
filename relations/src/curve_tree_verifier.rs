use bulletproofs::r1cs::*;

use crate::error::Error;
use crate::single_level_select_and_rerandomize::*;
use crate::curve_tree_prover::RootChildrenCoords;
use crate::select::multi_select_public_set_ext_challenge;
use crate::curve_tree::{
    CurveTree, CurveTreeNode, Root, SelRerandParameters, SelectAndRerandomizePath,
};
use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_ff::PrimeField;
use core::borrow::BorrowMut;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use ark_std::{string::ToString, vec::Vec};

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > CurveTree<L, M, P0, P1>
{
    /// Adds the root to a randomized path provided by the prover. The "root" here is the commitment to the x-coordinates
    /// of the children of root node.
    pub fn add_root_to_randomized_path(
        &self,
        randomized_path: &mut SelectAndRerandomizePath<L, P0, P1>,
    ) {
        match self {
            Self::Odd(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len(),
                    randomized_path.odd_commitments.len() + 1
                );
                randomized_path.odd_commitments.insert(0, ct.commitment(0));
            }
            Self::Even(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len(),
                    randomized_path.odd_commitments.len()
                );
                randomized_path.even_commitments.insert(0, ct.commitment(0));
            }
        };
    }
}

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > CurveTree<L, M, P0, P1>
{
    pub fn select_and_rerandomize_verifier_gadget<T: BorrowMut<MerlinTranscript>>(
        &self,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        mut randomized_path: SelectAndRerandomizePath<L, P0, P1>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Affine<P0> {
        self.add_root_to_randomized_path(&mut randomized_path);
        // The even and odd commitments include the root and the selected leaf, their sum should equal the height of the tree.
        debug_assert_eq!(
            self.height(),
            randomized_path.even_commitments.len() + randomized_path.odd_commitments.len()
        );

        randomized_path.even_verifier_gadget_old(even_verifier, parameters, self);
        randomized_path.odd_verifier_gadget_old(odd_verifier, parameters, self);

        randomized_path.get_rerandomized_leaf_old()
    }
}

impl<
        const L: usize,
        F: PrimeField,
        P0: SWCurveConfig<BaseField = F> + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = F> + Copy,
    > SelectAndRerandomizePath<L, P0, P1>
{
    /// Get the public rerandomization of the selected (leaf) commitment
    pub fn get_rerandomized_leaf_old(&self) -> Affine<P0> {
        self.even_commitments.last().unwrap().clone()
    }

    pub fn even_verifier_gadget_old<const M: usize, T: BorrowMut<MerlinTranscript>>(
        &self,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        parameters: &SelRerandParameters<P0, P1>,
        ct: &CurveTree<L, M, P0, P1>,
    ) {
        // Since the path now contains the root as well
        let root_is_odd = self.even_commitments.len() == self.odd_commitments.len();
        if !root_is_odd {
            assert_eq!(self.even_commitments.len(), self.odd_commitments.len() + 1);
        }

        // Last item of self.even_commitments.len() is for leaf
        for parent_index in 0..(self.even_commitments.len() - 1) {
            let odd_index = if root_is_odd {
                parent_index + 1
            } else {
                parent_index
            };
            let variables = if parent_index == 0 && !root_is_odd {
                // Root's children are not re-randomized
                let children = match &ct {
                    CurveTree::Even(root) => {
                        if let CurveTreeNode::InnerNode(inner_node) = root {
                            inner_node.x_coord_children[0]
                        } else {
                            unreachable!("Root of a curve tree can't be a leaf")
                        }
                    }
                    _ => panic!(),
                };
                children.map(constant).to_vec()
            } else {
                let variables = even_verifier.commit_vec(L, self.even_commitments[parent_index]);
                variables
                    .iter()
                    .map(|v| LinearCombination::<P0::ScalarField>::from(*v))
                    .collect()
            };
            single_level_select_and_rerandomize(
                even_verifier,
                &parameters.odd_parameters,
                &self.odd_commitments[odd_index],
                variables,
                None,
                None,
            );
        }
    }

    pub fn odd_verifier_gadget_old<const M: usize, T: BorrowMut<MerlinTranscript>>(
        &self,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        ct: &CurveTree<L, M, P0, P1>,
    ) {
        // Since the path now contains the root as well
        let root_is_odd = self.even_commitments.len() == self.odd_commitments.len();
        if !root_is_odd {
            assert_eq!(self.even_commitments.len(), self.odd_commitments.len() + 1);
        }
        for parent_index in 0..self.odd_commitments.len() {
            let even_index = if root_is_odd {
                parent_index
            } else {
                parent_index + 1
            };
            let child = self.even_commitments[even_index];
            let variables = if parent_index == 0 && root_is_odd {
                // Root's children are not re-randomized
                let children = match &ct {
                    CurveTree::Odd(root) => {
                        if let CurveTreeNode::InnerNode(inner_node) = root {
                            inner_node.x_coord_children[0]
                        } else {
                            unreachable!("Root of a curve tree can't be a leaf")
                        }
                    }
                    _ => panic!(),
                };
                children.map(|c| constant(c)).to_vec()
            } else {
                let variables = odd_verifier.commit_vec(L, self.odd_commitments[parent_index]);
                variables
                    .iter()
                    .map(|v| LinearCombination::<P1::ScalarField>::from(*v))
                    .collect()
            };
            single_level_select_and_rerandomize(
                odd_verifier,
                &parameters.even_parameters,
                &child,
                variables,
                None,
                None,
            );
        }
    }
}

impl<
        const L: usize,
        F: PrimeField,
        P0: SWCurveConfig<BaseField = F> + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = F> + Copy,
    > SelectAndRerandomizePath<L, P0, P1>
{
    pub fn select_and_rerandomize_verifier_gadget<T: BorrowMut<MerlinTranscript>>(
        &self,
        root: &Root<L, 1, P0, P1>,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Affine<P0> {
        let mut root_is_even = false;
        match root {
            Root::Even(root) => {
                root_is_even = true;
                let child = &self.odd_commitments[0];
                root_level_select_and_rerandomize(
                    even_verifier,
                    &parameters.odd_parameters,
                    &child,
                    &root.x_coord_children[0],
                    None,
                    None,
                );
            },
            Root::Odd(root) => {
                let child = &self.even_commitments[0];
                root_level_select_and_rerandomize(
                    odd_verifier,
                    &parameters.even_parameters,
                    &child,
                    &root.x_coord_children[0],
                    None,
                    None,
                );
            },
        }

        let verify_even = |even_verifier: &mut Verifier<T, Affine<P0>>| {
            self.even_verifier_gadget(root_is_even, even_verifier, &parameters.odd_parameters);
        };

        let verify_odd = |odd_verifier: &mut Verifier<T, Affine<P1>>| {
            self.odd_verifier_gadget(root_is_even, odd_verifier, &parameters.even_parameters);
        };

        #[cfg(not(feature = "parallel"))]
        verify_even(even_verifier);

        #[cfg(not(feature = "parallel"))]
        verify_odd(odd_verifier);

        #[cfg(feature = "parallel")]
        rayon::join(|| verify_even(even_verifier), || verify_odd(odd_verifier));

        self.get_rerandomized_leaf()
    }

    pub fn even_verifier_gadget<T: BorrowMut<MerlinTranscript>>(
        &self,
        root_is_even: bool,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_parameters: &SingleLayerParameters<P1>,
    ) {
        // Last item of self.even_commitments.len() is for leaf
        for parent_index in 0..(self.even_commitments.len() - 1) {
            // If the root is at odd level, then the first element in self.odd_commitments will be the root so skip that
            let child_index = if root_is_even {
                parent_index + 1
            } else {
                parent_index
            };

            let child = &self.odd_commitments[child_index];
            let variables = even_verifier
                .commit_vec(L, self.even_commitments[parent_index])
                .iter()
                .map(|v| LinearCombination::<P0::ScalarField>::from(*v))
                .collect();
            single_level_select_and_rerandomize(
                even_verifier,
                odd_parameters,
                child,
                variables,
                None,
                None,
            );
        }
    }

    pub fn odd_verifier_gadget<T: BorrowMut<MerlinTranscript>>(
        &self,
        root_is_even: bool,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        even_parameters: &SingleLayerParameters<P0>,
    ) {
        for parent_index in 0..self.odd_commitments.len() {
            // If the root is at even level, then the first element in self.even_commitments will be the root
            let child_index = if !root_is_even {
                parent_index + 1
            } else {
                parent_index
            };

            let child = self.even_commitments[child_index];
            let variables = odd_verifier
                .commit_vec(L, self.odd_commitments[parent_index])
                .iter()
                .map(|v| LinearCombination::<P1::ScalarField>::from(*v))
                .collect();
            single_level_select_and_rerandomize(
                odd_verifier,
                even_parameters,
                &child,
                variables,
                None,
                None,
            );
        }
    }

    pub fn process_root_nodes_for_given_paths_with_common_root<const M: usize, T: BorrowMut<MerlinTranscript>>(
        paths: &[Self],
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        root: &Root<L, M, P0, P1>,
    ) -> Result<RootChildrenCoords<P0::ScalarField, P1::ScalarField>, Error> {
        match root {
            Root::Even(root_node) => {
                // For verifier, we need to create variables for the x-coordinates
                let x_coords_children: Vec<LinearCombination<P0::ScalarField>> = paths.iter()
                    .map(|_| {
                        even_verifier.allocate(None).unwrap().into()
                    })
                    .collect();

                let c = even_verifier.transcript().challenge_scalar(b"challenge-for-multi_select");
                multi_select_public_set_ext_challenge(
                    even_verifier,
                    x_coords_children.clone(),
                    &root_node.x_coord_children[0],
                    c
                );

                Ok(RootChildrenCoords::Even(x_coords_children))
            },
            Root::Odd(root_node) => {
                // For verifier, we need to create variables for the x-coordinates
                let x_coords_children: Vec<LinearCombination<P1::ScalarField>> = paths.iter()
                    .map(|_| {
                        odd_verifier.allocate(None).unwrap().into()
                    })
                    .collect();

                let c = odd_verifier.transcript().challenge_scalar(b"challenge-for-multi_select");
                multi_select_public_set_ext_challenge(
                    odd_verifier,
                    x_coords_children.clone(),
                    &root_node.x_coord_children[0],
                    c
                );

                Ok(RootChildrenCoords::Odd(x_coords_children))
            }
        }
    }

    pub fn process_non_root_nodes_for_given_paths_with_common_root<const M: usize, T: BorrowMut<MerlinTranscript>>(
        paths: &[Self],
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        mut root_children_coords: RootChildrenCoords<P0::ScalarField, P1::ScalarField>,
        root: &Root<L, M, P0, P1>,
    ) -> Result<Vec<Affine<P0>>, Error> {
        if paths.is_empty() {
            return Err(Error::PathsLengthMustBeGreaterThanZero);
        }
        let is_root_even = matches!(root, Root::Even(_));
        let mut rerandomized_leaves = Vec::with_capacity(paths.len());

        for path in paths {
            // Validate root node using the batched coordinates
            match &mut root_children_coords {
                RootChildrenCoords::Even(coords) => {
                    let x_var = coords.remove(0);
                    if !is_root_even {
                        return Err(Error::RootTypeMismatch { expected: "even".to_string(), got: "odd".to_string() });
                    }
                    let child_commitment = &path.odd_commitments[0];
                    even_verifier.transcript().append(b"rerandomized_child", &child_commitment);
                    validate_point_and_re_randomize(
                        even_verifier,
                        &parameters.odd_parameters,
                        child_commitment,
                        x_var,
                        None,
                        None,
                    );
                }
                RootChildrenCoords::Odd(coords) => {
                    let x_var = coords.remove(0);
                    if is_root_even {
                        return Err(Error::RootTypeMismatch { expected: "odd".to_string(), got: "even".to_string() });
                    }
                    let child_commitment = &path.even_commitments[0];
                    odd_verifier.transcript().append(b"rerandomized_child", &child_commitment);
                    validate_point_and_re_randomize(
                        odd_verifier,
                        &parameters.even_parameters,
                        child_commitment,
                        x_var,
                        None,
                        None,
                    );
                }
            }

            // Process non-root nodes using existing verifier gadgets
            let verify_even = |even_verifier: &mut Verifier<T, Affine<P0>>| {
                path.even_verifier_gadget(is_root_even, even_verifier, &parameters.odd_parameters);
            };

            let verify_odd = |odd_verifier: &mut Verifier<T, Affine<P1>>| {
                path.odd_verifier_gadget(is_root_even, odd_verifier, &parameters.even_parameters);
            };

            #[cfg(not(feature = "parallel"))]
            verify_even(even_verifier);

            #[cfg(not(feature = "parallel"))]
            verify_odd(odd_verifier);

            #[cfg(feature = "parallel")]
            rayon::join(|| verify_even(even_verifier), || verify_odd(odd_verifier));

            rerandomized_leaves.push(path.get_rerandomized_leaf());
        }

        Ok(rerandomized_leaves)
    }

    /// Multi-path variant of select_and_rerandomize_verifier_gadget.
    /// Efficiently verifies multiple paths with a common root using batched operations.
    pub fn select_and_rerandomize_verifier_gadget_multi_path<const M: usize, T: BorrowMut<MerlinTranscript>>(
        paths: &[Self],
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        root: &Root<L, M, P0, P1>,
    ) -> Result<Vec<Affine<P0>>, Error> {
        // First, process the root nodes in batch
        let root_children_coords = Self::process_root_nodes_for_given_paths_with_common_root(
            paths,
            even_verifier,
            odd_verifier,
            root,
        )?;

        // Then, process the non-root nodes individually
        Self::process_non_root_nodes_for_given_paths_with_common_root(
            paths,
            even_verifier,
            odd_verifier,
            parameters,
            root_children_coords,
            root,
        )
    }

    /// Get the public rerandomization of the selected (leaf) commitment
    pub fn get_rerandomized_leaf(&self) -> Affine<P0> {
        self.even_commitments.last().unwrap().clone()
    }
}
