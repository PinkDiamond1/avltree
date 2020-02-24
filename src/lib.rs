//! An AVL Tree implemented on Kelvin
#![warn(missing_docs)]

use std::borrow::Borrow;
use std::io::{self};
use std::marker::PhantomData;
use std::mem;

use arrayvec::ArrayVec;

use kelvin::{
    Annotation, ByteHash, Compound, Content, Handle, HandleMut, HandleType, Method, SearchResult,
    Sink, Source, KV,
};

const N_NODES: usize = 2;

/// An AVL tree
/// First of it's kind as a self-balancing binary search tree
#[derive(Clone)]
pub struct AVL<K, V, A, H>(ArrayVec<[Handle<Self, H>; N_NODES]>)
where
    K: Content<H>,
    V: Content<H>,
    A: Annotation<KV<K, V>, H>,
    H: ByteHash;

impl<K, V, A, H> Default for AVL<K, V, A, H>
where
    K: Content<H>,
    V: Content<H>,
    A: Annotation<KV<K, V>, H>,
    H: ByteHash,
{
    fn default() -> Self {
        AVL(Default::default())
    }
}

impl<K, V, A, H> Content<H> for AVL<K, V, A, H>
where
    K: Content<H>,
    V: Content<H>,
    A: Annotation<KV<K, V>, H>,
    H: ByteHash,
{
    fn persist(&mut self, sink: &mut Sink<H>) -> io::Result<()> {
        self.0
            .iter_mut()
            .filter_map(|handle| {
                if handle.handle_type() == HandleType::None {
                    None
                } else {
                    Some(handle.persist(sink))
                }
            })
            .collect()
    }

    fn restore(source: &mut Source<H>) -> io::Result<Self> {
        let mut avl: AVL<K, V, A, H> = AVL::default();
        for _ in 0..len {
            avl.0.push(Handle::restore(source)?);
        }

        Ok(AVL::default())
    }
}

impl<K, V, A, H> Compound<H> for AVL<K, V, A, H>
where
    K: Content<H>,
    V: Content<H>,
    A: Annotation<KV<K, V>, H>,
    H: ByteHash,
{
    type Leaf = KV<K, V>;
    type Annotation = A;

    fn children(&self) -> &[Handle<Self, H>] {
        &self.0
    }

    fn children_mut(&mut self) -> &mut [Handle<Self, H>] {
        &mut self.0
    }
}

/// A helper to look up certain values in the AVL tree.
pub struct AVLSearch<K, H>(K, PhantomData<H>)
where
    K: Content<H> + Ord + Eq + PartialEq,
    H: ByteHash;

impl<K, V, A, H> Method<AVL<K, V, A, H>, H> for AVLSearch<K, H>
where
    K: Content<H> + Ord + Eq + PartialEq,
    V: Content<H>,
    A: Annotation<KV<K, V>, H> + AsRef<K>,
    H: ByteHash,
{
    fn select(&mut self, compound: &AVL<K, V, A, H>, _: usize) -> SearchResult
    where
        H: ByteHash,
    {
        let ann = compound.annotation();
        if let Some(a) = ann {
            if a.as_ref() == &self.0 {
                return SearchResult::Leaf(0);
            }

            if a.as_ref() > &self.0 {
                return SearchResult::Path(0);
            }

            return SearchResult::Path(1);
        }

        SearchResult::None
    }
}

impl<K, H> AVLSearch<K, H>
where
    K: Content<H> + Ord + Eq + PartialEq,
    H: ByteHash,
{
    fn new(k: K) -> Self {
        AVLSearch(k, PhantomData)
    }
}

impl<K, V, A, H> AVL<K, V, A, H>
where
    K: Content<H> + Ord + Eq + PartialEq,
    V: Content<H>,
    A: Annotation<KV<K, V>, H> + Borrow<K> + AsRef<K>,
    H: ByteHash,
{
    /// Create a new, empty, AVL tree.
    pub fn new() -> Self {
        AVL(Default::default())
    }

    /// Insert an item, consisting of a key and a value, into the AVL
    /// tree. The tree is then re-balanced.
    pub fn insert_and_rebalance(&mut self, k: K, v: V) -> io::Result<()> {
        self._insert_and_rebalance(KV::new(k, v))
    }

    // TODO: should we hash the key first?
    fn _insert_and_rebalance(&mut self, handle: KV<K, V>) -> io::Result<()> {
        /// Use an enum to get around borrow issues
        #[derive(Debug)]
        enum Action {
            InsertNode(usize),
            Placeholder,
        }

        let mut avl_search = AVLSearch::new(handle.key.clone());
        let mut action = Action::Placeholder;

        match avl_search.select(self, 0) {
            // We got a result for either of the branches of this node
            SearchResult::Path(i) => match &mut *self.0[i].inner_mut()? {
                HandleMut::None => unreachable!(),
                HandleMut::Leaf(_) => action = Action::InsertNode(i),
                HandleMut::Node(n) => {
                    n._insert_and_rebalance(handle)?;
                    return n.rebalance();
                }
            },
            // We got a result for this specific node/leaf
            _ => {
                let mut kv = self.annotation().expect("annotation should exist");
                mem::replace(&mut kv, A::from(&handle));
                return Ok(());
            }
        }

        match action {
            Action::InsertNode(i) => {
                let new_avl = AVL::default();
                let mut kv = new_avl.annotation().expect("annotation should exist");
                mem::replace(&mut kv, A::from(&handle));
                let h = Handle::new_node(new_avl);
                mem::replace(&mut self.0[i], h);
                return self.rebalance();
            }
            _ => return Ok(()),
        }
    }

    /// Delete a key from the AVL tree, and rebalance it afterwards.
    pub fn delete_and_rebalance(&mut self, k: K) -> io::Result<()> {
        let mut avl_search = AVLSearch::new(k.clone());

        /// Use an enum to get around borrow issues
        #[derive(Debug)]
        enum Action {
            RemoveLeaf(usize),
            Placeholder,
        }

        let mut action = Action::Placeholder;

        match avl_search.select(self, 0) {
            // We got a result for either of the branches of this node
            SearchResult::Path(i) => match &mut *self.0[i].inner_mut()? {
                HandleMut::None => unreachable!(),
                HandleMut::Leaf(_) => {
                    action = Action::RemoveLeaf(i);
                }
                HandleMut::Node(n) => {
                    n.delete_and_rebalance(k)?;
                    return n.rebalance();
                }
            },
            // We got a result for this specific node
            // Note that we should always get a node, as a leaf will be detected
            // and cleared in the previous match arm
            _ => {
                if self.0[0].is_none() && self.0[1].is_none() {
                    panic!("empty node");
                }

                // Both children are present
                if !self.0[0].is_none() && !self.0[1].is_none() {
                    /// Use an enum to get around borrow issues
                    #[derive(Debug)]
                    enum Action {
                        Replace,
                        Move,
                        Placeholder,
                    }

                    let mut action = Action::Placeholder;

                    // Find node that is closest to the one we're deleting
                    // This defaults to finding the minimum node on the right-hand side
                    // TODO: figure out if this is correct
                    match self.0[1].handle_type() {
                        HandleType::Node => {
                            // Find our successor
                            action = Action::Move;
                        }
                        HandleType::Leaf => {
                            // Just replace the current node annotation with this leaf
                            action = Action::Replace;
                        }
                        _ => panic!("right-hand child can not be none"),
                    }

                    match action {
                        Action::Replace => {
                            let leaf_kv = self.0[1].clone().into_leaf();
                            let mut kv = self.annotation().expect("annotation should exist");
                            mem::replace(&mut kv, A::from(&leaf_kv));
                        }
                        Action::Move => {
                            let successor = self.0[1].clone().into_node().min_node();
                            // Does this successor have a right-hand child?
                            // If so, it should replace the successor
                            match successor.handle_type() {
                                HandleType::Leaf => {
                                    let leaf_kv = successor.into_leaf();
                                    let mut kv =
                                        self.annotation().expect("annotation should exist");
                                    mem::replace(&mut kv, A::from(&leaf_kv));
                                }
                                HandleType::Node => {
                                    // Move the annotation first
                                    let node_kv = successor
                                        .clone()
                                        .into_node()
                                        .annotation()
                                        .expect("annotation should exist");
                                    let mut kv =
                                        self.annotation().expect("annotation should exist");
                                    mem::replace(&mut kv, node_kv);

                                    // Now, replace the successor with it's right-hand child
                                    let mut node = successor.into_node();
                                    match node.0[1].handle_type() {
                                        HandleType::Leaf => {
                                            let leaf_kv = node.0[1].clone().into_leaf();
                                            let mut kv =
                                                node.annotation().expect("annotation should exist");
                                            mem::replace(&mut kv, A::from(&leaf_kv));
                                        }
                                        HandleType::Node => {
                                            let replacement = node.0[1].clone().into_node();
                                            mem::replace(&mut node, replacement);
                                        }
                                        _ => panic!("successor should never be none"),
                                    }
                                }
                                _ => panic!("successor should never be none"),
                            }
                        }
                        _ => {}
                    }

                    return Ok(());
                }

                // Only the left child is present
                if !self.0[0].is_none() {
                    match self.0[0].handle_type() {
                        HandleType::Leaf => {
                            let new_avl: AVL<K, V, A, H> = AVL::default();
                            let mut kv = new_avl.annotation().expect("annotation should exist");
                            mem::replace(&mut kv, A::from(&self.0[0].clone().into_leaf()));
                            mem::replace(self, new_avl);
                        }

                        HandleType::Node => {
                            mem::replace(self, self.0[0].clone().into_node());
                        }
                        _ => unreachable!(),
                    }

                    return Ok(());
                }

                // Only the right child is present
                match self.0[1].handle_type() {
                    HandleType::Leaf => {
                        let new_avl: AVL<K, V, A, H> = AVL::default();
                        let mut kv = new_avl.annotation().expect("annotation should exist");
                        mem::replace(&mut kv, A::from(&self.0[1].clone().into_leaf()));
                        mem::replace(self, new_avl);
                    }

                    HandleType::Node => {
                        mem::replace(self, self.0[1].clone().into_node());
                    }
                    _ => unreachable!(),
                }
                return Ok(());
            }
        }

        match action {
            Action::RemoveLeaf(i) => {
                self.0.remove(i);
                return Ok(());
            }
            _ => return Ok(()),
        }
    }

    /// Find the node with the lowest key in the AVL tree
    fn min_node(&self) -> Handle<Self, H> {
        match self.0[0].handle_type() {
            HandleType::Leaf => {
                return self.0[0].clone();
            }
            HandleType::Node => {
                return self.0[0].clone().into_node().min_node();
            }
            _ => panic!("nope"),
        }
    }

    // NOTE: not sure if I need this
    // Find the node with the highest key in the AVL tree
    // fn max_node(&self) -> Handle<Self, H> {
    //     match self.0[1].handle_type() {
    //         HandleType::Leaf => {
    //             return self.0[1].clone();
    //         }
    //         HandleType::Node => {
    //             return self.0[1].clone().into_node().min_node();
    //         }
    //         _ => panic!("nope"),
    //     }
    // }

    /// Rebalance the tree to ensure that each node's balance factor is
    /// any of -1, 0, or 1.
    fn rebalance(&mut self) -> io::Result<()> {
        let balance_factor = self.get_balance_factor();

        // TODO: implement correct rotations based on balance factor
        if balance_factor < -1 {
            unimplemented!();
        }

        if balance_factor > 1 {
            unimplemented!();
        }

        Ok(())
    }

    /// Get the balance factor for a given node.
    /// balance_factor = depth_of_right_subtree - depth_of_left_subtree
    fn get_balance_factor(&self) -> isize {
        let mut left_right_depth = [0isize; N_NODES];

        for i in 0..N_NODES {
            let depths = get_depths(&self.0[i]);

            left_right_depth[i] = *depths.iter().max().expect("should always be two depths");
        }

        left_right_depth[1] - left_right_depth[0]
    }

    /// Put the right-hand child of `self` up by one level, making `self` the left-hand
    /// child of the elevated node.
    fn rotate_left(&mut self) -> io::Result<()> {
        enum Action {
            RotateLeaf,
            RotateNode,
            Placeholder,
        }

        let mut action = Action::Placeholder;
        match self.0[1].handle_type() {
            HandleType::Leaf => action = Action::RotateLeaf,
            HandleType::Node => action = Action::RotateNode,
            _ => panic!("no"),
        }

        match action {
            Action::RotateLeaf => {
                // Create a new node with this leaf's annotation
                let mut new_avl = AVL::default();
                let mut kv = new_avl.annotation().expect("annotation should exist");
                mem::replace(&mut kv, A::from(&self.0[1].clone().into_leaf()));

                // Remove the child from `self`
                self.0[1] = Handle::new_empty();

                // Place `self` as a left-hand node of this new node
                new_avl.0[0] = Handle::new_node(self.clone());

                // Move the new node to the place of `self`
                mem::replace(self, new_avl);
                return Ok(());
            }
            Action::RotateNode => {
                // Create a new AVL
                let mut new_node = self.0[1].clone().into_node();

                // `self` right-hand child should be `new_node` left-hand child (if any)
                if !new_node.0[0].is_none() {
                    self.0[1] = new_node.0[0].clone();
                }

                // `new_node` left-hand child should be `self`
                new_node.0[0] = Handle::new_node(self.clone());
                return Ok(());
            }
            _ => Ok(()),
        }
    }

    /// Put the left-hand child of `self` up by one level, making `self` the right-hand
    /// child of the elevated node.
    fn rotate_right(&mut self) -> io::Result<()> {
        enum Action {
            RotateLeaf,
            RotateNode,
            Placeholder,
        }

        let mut action = Action::Placeholder;
        match self.0[1].handle_type() {
            HandleType::Leaf => action = Action::RotateLeaf,
            HandleType::Node => action = Action::RotateNode,
            _ => panic!("no"),
        }

        match action {
            Action::RotateLeaf => {
                // Create a new node with this leaf's annotation
                let mut new_avl = AVL::default();
                let mut kv = new_avl.annotation().expect("annotation should exist");
                mem::replace(&mut kv, A::from(&self.0[0].clone().into_leaf()));

                // Remove the child from `self`
                self.0[0] = Handle::new_empty();

                // Place `self` as a right-hand node of this new node
                new_avl.0[1] = Handle::new_node(self.clone());

                // Move the new node to the place of `self`
                mem::replace(self, new_avl);
                return Ok(());
            }
            Action::RotateNode => {
                // Create a new AVL
                let mut new_node = self.0[0].clone().into_node();

                // `self` left-hand child should be `new_node` right-hand child (if any)
                if !new_node.0[1].is_none() {
                    self.0[0] = new_node.0[1].clone();
                }

                // `new_node` right-hand child should be `self`
                new_node.0[1] = Handle::new_node(self.clone());
                return Ok(());
            }
            _ => Ok(()),
        }
    }

    // TODO: implement LeftRight and RightLeft rotations
    fn rotate_left_right(&mut self) -> io::Result<()> {
        unimplemented!();
    }

    fn rotate_right_left(&mut self) -> io::Result<()> {
        unimplemented!();
    }
}

/// Recurse through the AVL tree, saving the maximum depth of each path
/// in a vector.
fn get_depths<K, V, A, H>(h: &Handle<AVL<K, V, A, H>, H>) -> Vec<isize>
where
    K: Content<H> + Ord + Eq + PartialEq,
    V: Content<H>,
    A: Annotation<KV<K, V>, H>,
    H: ByteHash,
{
    let mut depths: Vec<isize> = vec![];
    let mut depth: isize = 0;
    match h.handle_type() {
        HandleType::Leaf => {
            depth += 1;
            depths.push(depth);
        }
        HandleType::Node => {
            for i in 0..N_NODES {
                let node = h.clone().into_node();
                let mut node_depths = get_depths(&node.0[i]);
                depths.append(&mut node_depths);
            }
        }
        HandleType::None => {
            depths.push(depth);
        }
    }

    depths
}

#[cfg(test)]
mod test {}
