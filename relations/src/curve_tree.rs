use crate::error::Error;
use crate::single_level_select_and_rerandomize::*;

use ark_ec::AffineRepr;
use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate, Write,
};
use ark_std::{boxed::Box, io::Read, vec, vec::Vec, Zero};

/// Parameters for multi level select and rerandomize over a 2-cycle of curves
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SelRerandParameters<P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> {
    pub even_parameters: SingleLayerParameters<P0>,
    pub odd_parameters: SingleLayerParameters<P1>,
}

impl<P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> SelRerandParameters<P0, P1> {
    pub fn new(even_generators_length: usize, odd_generators_length: usize) -> Result<Self, Error> {
        Ok(SelRerandParameters {
            even_parameters: SingleLayerParameters::<P0>::new::<P1>(even_generators_length)?,
            odd_parameters: SingleLayerParameters::<P1>::new::<P0>(odd_generators_length)?,
        })
    }
}

pub enum CurveTree<
    const L: usize, // L is te branching factor, i.e. the number of children per branch
    const M: usize, // M the maximal batch size for which efficient parallel membership proofs are supported.
    P0: SWCurveConfig,
    P1: SWCurveConfig,
> {
    Even(CurveTreeNode<L, M, P0, P1>),
    Odd(CurveTreeNode<L, M, P1, P0>),
}

impl<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> core::fmt::Debug
    for CurveTree<L, M, P0, P1>
{
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        match self {
            Self::Even(ct) => fmt.debug_tuple("Even").field(&ct).finish(),
            Self::Odd(ct) => fmt.debug_tuple("Odd").field(&ct).finish(),
        }
    }
}

/// Implements functionality for creating the Curve Tree
impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > CurveTree<L, M, P0, P1>
{
    // TODO: This isn't practical to initialize with large sets that don't fit in memory.
    // We need to have Tornado cash like default leaves. Will also save with the un-necessary computation
    /// Build a curve tree from a set of commitments
    pub fn from_leaves(
        set: &[Affine<P0>],
        parameters: &SelRerandParameters<P0, P1>,
        height: Option<usize>, // resulting curve tree will have height at least `height`
    ) -> Self {
        if set.is_empty() {
            panic!("The curve tree must have at least one leaf.")
        }
        // Convert each commitment to a leaf.
        let mut num_nodes_at_current_level = set.len();
        // num_nodes_at_parent_level = ceil(num_nodes_at_current_level/L). Its more like number of parent nodes of this level
        let mut num_nodes_at_parent_level = (num_nodes_at_current_level + L - 1) / L;
        // Add all the leaves to `nodes_at_even_level`
        let mut nodes_at_even_level = Vec::with_capacity(num_nodes_at_current_level);
        for leaf in set {
            nodes_at_even_level.push(CurveTreeNode::<L, M, P0, P1>::Leaf(*leaf));
        }
        let mut nodes_at_odd_level = Vec::with_capacity(num_nodes_at_parent_level);
        // Leaves are at even level, i.e. level 0
        let mut is_current_level_even = true;

        while num_nodes_at_current_level > 1 {
            // TODO: Drain chunks in a way to avoid copying vector data (to_vec)
            if is_current_level_even {
                // For even-level nodes, an odd level parent is created
                for nodes in nodes_at_even_level.chunks(L) {
                    nodes_at_odd_level.push(CurveTreeNode::<L, M, P1, P0>::combine(
                        nodes.to_vec(),
                        &parameters.odd_parameters,
                        &parameters.even_parameters.delta,
                    ));
                }
                // This will hold nodes at the next even-level
                nodes_at_even_level = vec![];
            } else {
                // For odd-level nodes, an even level parent is created
                for nodes in nodes_at_odd_level.chunks(L) {
                    nodes_at_even_level.push(CurveTreeNode::<L, M, P0, P1>::combine(
                        nodes.to_vec(),
                        &parameters.even_parameters,
                        &parameters.odd_parameters.delta,
                    ));
                }
                // This will hold nodes at the next odd-level
                nodes_at_odd_level = vec![];
            }

            num_nodes_at_current_level = num_nodes_at_parent_level;
            num_nodes_at_parent_level = (num_nodes_at_parent_level + L - 1) / L;
            is_current_level_even = !is_current_level_even;
        }

        if is_current_level_even {
            Self::Even(nodes_at_even_level[0].clone()).increase_height(height, parameters)
        } else {
            Self::Odd(nodes_at_odd_level[0].clone()).increase_height(height, parameters)
        }
    }

    pub fn increase_height(
        self,
        height: Option<usize>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Self {
        match height {
            None => self,
            Some(height) => {
                let mut res = self;
                while res.height() < height {
                    match res {
                        Self::Even(ct) => {
                            res = Self::Odd(CurveTreeNode::<L, M, P1, P0>::combine(
                                vec![ct],
                                &parameters.odd_parameters,
                                &parameters.even_parameters.delta,
                            ));
                        }
                        Self::Odd(ct) => {
                            res = Self::Even(CurveTreeNode::<L, M, P0, P1>::combine(
                                vec![ct],
                                &parameters.even_parameters,
                                &parameters.odd_parameters.delta,
                            ));
                        }
                    }
                }
                res
            }
        }
    }

    //todo add a function to add a single/several commitments

    /// Get leaf at index `leaf_index`
    pub fn get_leaf(&self, leaf_index: usize) -> Affine<P0> {
        let mut leaf = None;
        match self {
            Self::Even(node) => Self::parse_even_node_for_leaf(node, leaf_index, &mut leaf),
            Self::Odd(node) => Self::parse_odd_node_for_leaf(node, leaf_index, &mut leaf),
        }
        assert!(leaf.is_some());
        leaf.unwrap()
    }

    /// Update value of leaf at index `leaf_index` to `new_leaf_value`
    pub fn update_leaf(
        &mut self,
        leaf_index: usize,
        tree_index: usize,
        new_leaf_value: Affine<P0>,
        parameters: &SelRerandParameters<P0, P1>,
    ) {
        match self {
            Self::Even(node) => {
                Self::update_even_node(node, leaf_index, tree_index, new_leaf_value, parameters)
            }
            Self::Odd(node) => {
                Self::update_odd_node(node, leaf_index, tree_index, new_leaf_value, parameters)
            }
        }
    }

    /// The height of a node is the number of edges to reach a leaf.
    pub fn height(&self) -> usize {
        match self {
            Self::Even(ct) => ct.height(),
            Self::Odd(ct) => ct.height(),
        }
    }

    /// Get the root node.
    pub fn root_node(&self) -> Root<L, M, P0, P1> {
        match self {
            Self::Even(ct) => match ct {
                CurveTreeNode::InnerNode(n) => Root::Even(RootNode {
                    commitments: n.commitments_to_children.clone(),
                    x_coord_children: n.x_coord_children.clone(),
                }),
                _ => unreachable!("Root of a curve tree can't be a leaf"),
            },
            Self::Odd(ct) => match ct {
                CurveTreeNode::InnerNode(n) => Root::Odd(RootNode {
                    commitments: n.commitments_to_children.clone(),
                    x_coord_children: n.x_coord_children.clone(),
                }),
                _ => unreachable!("Root of a curve tree can't be a leaf"),
            },
        }
    }

    pub fn parse_odd_node_for_leaf(
        node: &CurveTreeNode<L, M, P1, P0>,
        leaf_index: usize,
        leaf: &mut Option<Affine<P0>>,
    ) {
        match node {
            CurveTreeNode::Leaf(_) => unreachable!("Cannot have leaf at odd level"),
            CurveTreeNode::InnerNode(inner_node) => {
                let child_index = node.child_index(leaf_index).unwrap();
                let child = inner_node.get_child(child_index);
                Self::parse_even_node_for_leaf(child, leaf_index, leaf)
            }
        }
    }

    pub fn parse_even_node_for_leaf(
        node: &CurveTreeNode<L, M, P0, P1>,
        leaf_index: usize,
        leaf: &mut Option<Affine<P0>>,
    ) {
        match node {
            CurveTreeNode::Leaf(l) => *leaf = Some(*l),
            CurveTreeNode::InnerNode(inner_node) => {
                let child_index = node.child_index(leaf_index).unwrap();
                let child = inner_node.get_child(child_index);
                Self::parse_odd_node_for_leaf(child, leaf_index, leaf)
            }
        }
    }

    pub fn update_even_node(
        node: &mut CurveTreeNode<L, M, P0, P1>,
        leaf_index: usize,
        tree_index: usize,
        new_leaf_value: Affine<P0>,
        parameters: &SelRerandParameters<P0, P1>,
    ) {
        let child_node_index_to_update = node.child_index(leaf_index);
        match node {
            CurveTreeNode::Leaf(ref mut l) => {
                *l = new_leaf_value;
            }
            CurveTreeNode::InnerNode(inner_node) => {
                let child_node_index_to_update = child_node_index_to_update.unwrap();
                let mut child_node_to_update =
                    match &mut inner_node.children[child_node_index_to_update] {
                        None => panic!(
                            "Child index out of bounds. Height: {}, Index: {}, Local index: {}",
                            node.height(),
                            leaf_index,
                            child_node_index_to_update
                        ),
                        Some(child) => child,
                    };
                Self::update_odd_node(
                    &mut child_node_to_update,
                    leaf_index,
                    tree_index,
                    new_leaf_value,
                    parameters,
                );

                let child_commitment = child_node_to_update.commitment(tree_index);
                inner_node.update_x_coord_and_commitment(
                    tree_index,
                    child_node_index_to_update,
                    child_commitment,
                    &parameters.even_parameters,
                    &parameters.odd_parameters,
                );
            }
        }
    }

    pub fn update_odd_node(
        node: &mut CurveTreeNode<L, M, P1, P0>,
        leaf_index: usize,
        tree_index: usize,
        new_leaf_value: Affine<P0>,
        parameters: &SelRerandParameters<P0, P1>,
    ) {
        let child_node_index_to_update = node.child_index(leaf_index);
        match node {
            CurveTreeNode::InnerNode(inner_node) => {
                let child_node_index_to_update = child_node_index_to_update.unwrap();

                let mut child_node_to_update =
                    match &mut inner_node.children[child_node_index_to_update] {
                        None => panic!(
                            "Child index out of bounds. Height: {}, Index: {}, Local index: {}",
                            node.height(),
                            leaf_index,
                            child_node_index_to_update
                        ),
                        Some(child) => child,
                    };
                Self::update_even_node(
                    &mut child_node_to_update,
                    leaf_index,
                    tree_index,
                    new_leaf_value,
                    parameters,
                );

                let child_commitment = child_node_to_update.commitment(tree_index);
                inner_node.update_x_coord_and_commitment(
                    tree_index,
                    child_node_index_to_update,
                    child_commitment,
                    &parameters.odd_parameters,
                    &parameters.even_parameters,
                );
            }
            _ => unreachable!("Cannot have leaf at odd level"),
        }
    }
}

/// A rerandomized path in the tree going from root to leaf (excluding both root and leaf). Given to the verifier to verify the proof
/// The last element in `odd_commitments` is the rerandomized parent of the selected leaf.
/// The last element in `even_commitments` is the rerandomized parent of the last element in `odd_commitments`, etc.
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SelectAndRerandomizePath<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    /// Randomized leaf, i.e. if leaf is a group element `C` then this is `C + (B_blinding * r)`. This could be part of `even_commitments`
    pub re_randomized_leaf: Affine<P0>,
    // TODO: Why not add re_randomized_leaf to even_commitments as the last element?
    pub odd_commitments: Vec<Affine<P1>>,
    pub even_commitments: Vec<Affine<P0>>,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
/// A rerandomized multi path in the tree.
/// The elements in `selected_commitments` are the selected and rerandomized commitments.
/// The last element in `odd_commitments` is the rerandomized parent of the selected leaves.
/// The last element in `even_commitments` is the rerandomized parent of the last element in `odd_commitments`, etc.
pub struct SelectAndRerandomizeMultiPath<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig,
    P1: SWCurveConfig,
> {
    pub selected_commitments: [Affine<P0>; M],
    pub odd_commitments: Vec<Affine<P1>>,
    pub even_commitments: Vec<Affine<P0>>,
}
/// A list of `L` potential nodes
type Children<const L: usize, const M: usize, P0, P1> = [Option<CurveTreeNode<L, M, P1, P0>>; L];

/// Root node of the tree. Used by verifier to check proofs and refer to tree.
#[derive(Clone, PartialEq, Eq)]
pub enum Root<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    Even(RootNode<L, M, P0, P1>),
    Odd(RootNode<L, M, P1, P0>),
}

impl<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> core::fmt::Debug
    for Root<L, M, P0, P1>
{
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        match self {
            Self::Even(n) => fmt.debug_tuple("Even").field(&n).finish(),
            Self::Odd(n) => fmt.debug_tuple("Odd").field(&n).finish(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct RootNode<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    /// Commitment(s) to x-coordinates of the immediate children
    pub commitments: [Affine<P0>; M],
    /// x-coordinates of the immediate children
    pub x_coord_children: Vec<[P1::BaseField; L]>,
}

impl<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> core::fmt::Debug
    for RootNode<L, M, P0, P1>
{
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        fmt.debug_struct("RootNode")
            .field("commitments", &self.commitments)
            .field("x_coord_children", &self.x_coord_children)
            .finish()
    }
}

/// map L children to their x-coordinate with 0 representing the empty node.
pub fn x_coordinates<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    children: &Children<L, M, P0, P1>,
    delta: &Affine<P1>,
    tree_index: usize,
) -> [P1::BaseField; L] {
    children
        .iter()
        .map(|opt| match opt {
            None => P1::BaseField::zero(),
            Some(child) => (child.commitment(tree_index) + delta).into_affine().x,
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

#[derive(Clone)]
pub enum CurveTreeNode<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    InnerNode(InnerNode<L, M, P0, P1>),
    Leaf(Affine<P0>),
}

#[derive(Clone)]
pub struct InnerNode<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    /// the ith `commitments_to_children` is the commitment to the `children` when using the ith set of generators.
    pub commitments_to_children: [Affine<P0>; M],
    pub children: Box<Children<L, M, P0, P1>>,
    // Storing as vector as this is causing stack overflow in some tests
    // x_coord_children: [[P1::BaseField; L]; M],
    pub x_coord_children: Vec<[P1::BaseField; L]>,
    pub height: usize,
    /// number of (contained) elements in this inner node. For an immediate parent of leaves, this is just the number of leaves, else its counts all the grandchildren including the leaves
    pub elements: usize,
}

impl<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> core::fmt::Debug
    for InnerNode<L, M, P0, P1>
{
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        fmt.debug_struct("InnerNode")
            .field("commitments_to_children", &self.commitments_to_children)
            .field("children", &self.children)
            .field("x_coord_children", &self.x_coord_children)
            .field("height", &self.height)
            .field("elements", &self.elements)
            .finish()
    }
}
impl<
        const L: usize,
        const M: usize,
        P0: SWCurveConfig + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
    > InnerNode<L, M, P0, P1>
{
    pub fn get_child(&self, index: usize) -> &CurveTreeNode<L, M, P1, P0> {
        let child = match &self.children[index] {
            None => panic!("Child index out of bounds. Local index: {}", index),
            Some(child) => child,
        };
        child
    }

    pub fn get_child_mut(&mut self, index: usize) -> &mut CurveTreeNode<L, M, P1, P0> {
        let child = match &mut self.children[index] {
            None => panic!("Child index out of bounds. Local index: {}", index),
            Some(child) => child,
        };
        child
    }

    pub fn update_x_coord_and_commitment(
        &mut self,
        tree_index: usize,
        child_node_index_to_update: usize,
        child_commitment: Affine<P1>,
        current_level_parameters: &SingleLayerParameters<P0>,
        child_level_parameters: &SingleLayerParameters<P1>,
    ) {
        let old_x_coord = self.x_coord_children[tree_index][child_node_index_to_update].clone();
        let old_comm = self.commitments_to_children[tree_index].clone();
        let gen_iter = current_level_parameters
            .bp_gens
            .share(0)
            .G(L * (tree_index + 1))
            .skip(L * tree_index + child_node_index_to_update);
        let gen = gen_iter.copied().next().unwrap();
        let new_x_coord = (child_commitment + child_level_parameters.delta)
            .into_affine()
            .x;
        self.x_coord_children[tree_index][child_node_index_to_update] = new_x_coord;
        let comm_diff = gen * (new_x_coord - old_x_coord);
        self.commitments_to_children[tree_index] =
            (old_comm.into_group() + comm_diff).into_affine();
    }
}

impl<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> core::fmt::Debug
    for CurveTreeNode<L, M, P0, P1>
{
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        match self {
            Self::InnerNode(inner_node) => fmt.debug_tuple("InnerNode").field(&inner_node).finish(),
            Self::Leaf(c) => fmt.debug_tuple("Leaf").field(&c).finish(),
        }
    }
}

impl<
        const L: usize,
        const M: usize,
        P0: SWCurveConfig + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
    > CurveTreeNode<L, M, P0, P1>
{
    /// Returns the commitment in this node. The leaf is itself the commitment
    pub fn commitment(&self, tree_index: usize) -> Affine<P0> {
        match self {
            Self::InnerNode(inner_node) => inner_node.commitments_to_children[tree_index],
            Self::Leaf(c) => *c,
        }
    }

    /// Height of the node. Leaf has height 0
    pub fn height(&self) -> usize {
        match self {
            Self::InnerNode(inner_node) => inner_node.height,
            Self::Leaf(_) => 0,
        }
    }

    pub fn elements(&self) -> usize {
        match self {
            Self::InnerNode(inner_node) => inner_node.elements,
            Self::Leaf(_) => 1,
        }
    }

    /// Return the index of the immediate child of this node, one of whose children or grandchildren
    /// is the leaf with index `leaf_index`. The returned index is in the context of immediate children
    /// of this node. Returns None if the node is a leaf
    pub fn child_index(&self, leaf_index: usize) -> Option<usize> {
        let height = self.height() as u32;
        if height == 0 {
            None
        } else {
            let capacity = L.pow(height);
            let child_capacity = L.pow(height - 1);
            Some((leaf_index % capacity) / child_capacity)
        }
    }

    /// Combine up to L child nodes of level d into a single level d+1 node.
    /// The children are assumed to be of appropriate identical height.
    /// All but the last should be full.
    fn combine(
        children: Vec<CurveTreeNode<L, M, P1, P0>>,
        parameters: &SingleLayerParameters<P0>,
        delta: &Affine<P1>,
    ) -> Self {
        if children.len() > L {
            panic!(
                "Cannot combine more than the branching factor: {} into one node.",
                L
            )
        };

        let mut elements = 0;
        let mut cs: Vec<Option<CurveTreeNode<L, M, P1, P0>>> = Vec::with_capacity(L);
        for c in children {
            elements += c.elements();
            cs.push(Some(c));
        }
        // Let the rest of the children be dummy elements.
        while cs.len() < L {
            cs.push(None)
        }
        let children: [Option<CurveTreeNode<L, M, P1, P0>>; L] = cs.try_into().unwrap();
        let height = if let Some(c) = &children[0] {
            c.height() + 1
        } else {
            1
        };
        // For each set of generators commit to the children's x-coordinates with randomness zero.
        let mut commitments = [Affine::<P0>::zero(); M];
        let mut x_coords = vec![[P1::BaseField::zero(); L]; M];
        for (tree_index, (c, x)) in commitments.iter_mut().zip(x_coords.iter_mut()).enumerate() {
            *x = x_coordinates(&children, delta, tree_index);
            *c = parameters.commit(x, P0::ScalarField::zero(), tree_index);
        }
        Self::InnerNode(InnerNode {
            commitments_to_children: commitments,
            children: Box::new(children),
            x_coord_children: x_coords,
            height,
            elements,
        })
    }
}

impl<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig> SelectAndRerandomizePath<L, P0, P1> {
    /// Add the root node to this path and returns true if root is even, else false
    pub fn add_root(&mut self, root: &Root<L, 1, P0, P1>) -> bool {
        match root {
            Root::Odd(ct) => {
                assert_eq!(self.even_commitments.len(), self.odd_commitments.len());
                self.odd_commitments.insert(0, ct.commitments[0].clone());
                false
            }
            Root::Even(ct) => {
                assert_eq!(self.even_commitments.len() + 1, self.odd_commitments.len());
                self.even_commitments.insert(0, ct.commitments[0].clone());
                true
            }
        }
    }
}

impl<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> Valid
    for Root<L, M, P0, P1>
{
    fn check(&self) -> Result<(), SerializationError> {
        match self {
            Self::Even(n) => n.check(),
            Self::Odd(n) => n.check(),
        }
    }
}

impl<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> CanonicalSerialize
    for Root<L, M, P0, P1>
{
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        match self {
            Self::Even(n) => {
                CanonicalSerialize::serialize_with_mode(&0u8, &mut writer, compress)?;
                CanonicalSerialize::serialize_with_mode(n, &mut writer, compress)
            }
            Self::Odd(n) => {
                CanonicalSerialize::serialize_with_mode(&1u8, &mut writer, compress)?;
                CanonicalSerialize::serialize_with_mode(n, &mut writer, compress)
            }
        }
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        match self {
            Self::Even(n) => 1 + n.serialized_size(compress),
            Self::Odd(n) => 1 + n.serialized_size(compress),
        }
    }
}

impl<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> CanonicalDeserialize
    for Root<L, M, P0, P1>
{
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let t: u8 = CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        match t {
            0u8 => Ok(Self::Even(CanonicalDeserialize::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?)),
            1u8 => Ok(Self::Odd(CanonicalDeserialize::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?)),
            _ => Err(SerializationError::InvalidData),
        }
    }
}
