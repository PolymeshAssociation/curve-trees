use bulletproofs::r1cs::*;

use crate::single_level_select_and_rerandomize::*;

use crate::curve_tree::{
    CurveTree, CurveTreeNode, Root, SelRerandParameters, SelectAndRerandomizePath,
};
use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_ff::PrimeField;
use core::borrow::BorrowMut;
use dock_crypto_utils::transcript::MerlinTranscript;

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
        let verify_even = |even_verifier: &mut Verifier<T, Affine<P0>>| {
            self.even_verifier_gadget(root, even_verifier, &parameters.odd_parameters);
        };

        let verify_odd = |odd_verifier: &mut Verifier<T, Affine<P1>>| {
            self.odd_verifier_gadget(root, odd_verifier, &parameters.even_parameters);
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
        root: &Root<L, 1, P0, P1>,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_parameters: &SingleLayerParameters<P1>,
    ) {
        let (root_is_even, children_of_root) = match root {
            Root::Even(root) => (true, Some(root.x_coord_children[0].clone())),
            _ => (false, None),
        };

        if root_is_even {
            let variables = children_of_root.unwrap().map(|c| constant(c)).to_vec();
            let child = &self.odd_commitments[0];
            single_level_select_and_rerandomize(
                even_verifier,
                odd_parameters,
                &child,
                variables,
                None,
                None,
            );
        }

        // Last item of self.even_commitments.len() is for leaf
        for parent_index in 0..(self.even_commitments.len() - 1) {
            // If the root is at odd level, then the first element in self.odd_commitments will be the root so skip that
            let child_index = if root_is_even {
                parent_index + 1
            } else {
                parent_index
            };

            let child = &self.odd_commitments[child_index];
            let variables = even_verifier.commit_vec(L, self.even_commitments[parent_index])
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
        root: &Root<L, 1, P0, P1>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        even_parameters: &SingleLayerParameters<P0>,
    ) {
        let (root_is_even, children_of_root) = match root {
            Root::Odd(root) => (false, Some(root.x_coord_children[0].clone())),
            _ => (true, None),
        };

        if !root_is_even {
            let variables = children_of_root.unwrap().map(|c| constant(c)).to_vec();
            let child = &self.even_commitments[0];
            single_level_select_and_rerandomize(
                odd_verifier,
                even_parameters,
                &child,
                variables,
                None,
                None,
            );
        }

        for parent_index in 0..self.odd_commitments.len() {
            // If the root is at even level, then the first element in self.even_commitments will be the root
            let child_index = if !root_is_even {
                parent_index + 1
            } else {
                parent_index
            };

            let child = self.even_commitments[child_index];
            let variables = odd_verifier.commit_vec(L, self.odd_commitments[parent_index])
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

    /// Get the public rerandomization of the selected (leaf) commitment
    pub fn get_rerandomized_leaf(&self) -> Affine<P0> {
        self.even_commitments.last().unwrap().clone()
    }
}
