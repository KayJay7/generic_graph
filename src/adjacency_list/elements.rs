//!This module provides the implementation of the Edge type, the Vertex type and
//! the edges' key type, to use with the AdjacencyGraph type
//!
//!The implementation of the Vertex type consist of a simple rename of the SimpleVertex type,
//! as said type is suitable for this implementation

use crate::Edge;
pub use crate::SimpleVertex as DirectedVertex;
use std::hash::Hash;
use std::ops::{Add, Sub};

///The CompoundKey type is the type designated as edge key. It consist of two generic keys of the
/// same type, representing the key of two adjacent Vertexes.
///
///For two CompoundKey to be equal, the corresponding vertex key of the two must be equal as well.
/// If two CompoundKey contain the same vertex key, but in different order they are not considered equal
///
///This type can be constructed only via the generate_key() function associated to the type DirectedEdge
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct CompoundKey<K: Hash + Eq + Clone> {
    left: K,
    right: K,
}

///The DirectedEdge type is the implementation an implementation od the Edge trait that uses
/// CompoundKey as type, as such it also indicates the direction of the edge which lead from the
/// left vertex to the right one.
#[derive(Eq, PartialEq, Clone, Debug)]
pub struct DirectedEdge<K, W>
    where K: Hash + Eq + Clone,
          W: Add + Sub + Eq + Ord + Copy,
{
    left: K,
    right: K,
    weight: W,
}

impl<K: Hash + Eq + Clone, W: Add + Sub + Eq + Ord + Copy> DirectedEdge<K, W> {

    ///Returns an instance of Directed edge with the specified weight and pair of vertex keys
    pub fn new(left: K, right: K, weight: W) -> DirectedEdge<K, W> {
        DirectedEdge {
            left,
            right,
            weight,
        }
    }
}

impl<K: Hash + Eq + Clone, W: Add + Sub + Eq + Ord + Copy> Edge<K, W, CompoundKey<K>> for DirectedEdge<K, W> {

    ///Returns a copy of the weight (the weight type is required to implement Copy)
    fn get_weight(&self) -> W {
        self.weight
    }

    ///change the value of weight
    fn set_weight(&mut self, weight: W) {
        self.weight = weight;
    }

    ///Returns a reference to the key of the left hand vertex
    fn left(&self) -> &K {
        &self.left
    }

    ///Returns a reference to the key of the right hand vertex
    fn right(&self) -> &K {
        &self.right
    }

    ///Returns a pair of reference to the vertex keys. Ordered from left to right
    fn get_pair(&self) -> (&K, &K) {
        (&self.left, &self.right)
    }

    ///Returns a new instance of CompoundKey from a pair of reference to vertex keys
    ///
    /// # Example
    /// ```rust
    /// use generic_graph::adjacency_list::elements::DirectedEdge;
    /// use generic_graph::Edge;
    ///
    /// let edge = DirectedEdge::new(1, 2, 3);
    /// let key = DirectedEdge::<i32, i32>::generate_key(edge.get_pair());
    ///
    /// assert_eq!(key, edge.key());
    /// ```
    fn generate_key(pair: (&K, &K)) -> CompoundKey<K> {
        CompoundKey {
            left: pair.0.clone(),
            right: pair.1.clone()
        }
    }

    ///Returns an new instance of CompoundKey generated from the pair of keys stored isn the edge
    ///
    /// # Example
    /// ```rust
    /// use generic_graph::adjacency_list::elements::DirectedEdge;
    /// use generic_graph::Edge;
    ///
    /// let edge = DirectedEdge::new(1, 2, 3);
    /// let key = DirectedEdge::<i32, i32>::generate_key(edge.get_pair());
    ///
    /// assert_eq!(key, edge.key());
    /// ```
    fn key(&self) -> CompoundKey<K> {
        CompoundKey {
            left: self.left.clone(),
            right: self.right.clone()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn edge_construction() {
        let edge = DirectedEdge::new(1, 2, 3);

        assert_eq!(edge,
        DirectedEdge{ left: 1, right: 2, weight: 3});
    }

    #[test]
    fn edge_getters_setters() {
        let mut edge = DirectedEdge::new(1, 2, 3);
        assert_eq!((&1, &2, 3),
                   (edge.left(), edge.right(), edge.get_weight()));
        assert_eq!((&1, &2), edge.get_pair());

        edge.set_weight(4);
        assert_eq!(4, edge.get_weight());
    }

    #[test]
    fn key_generation() {
        let edge = DirectedEdge::new(1, 2, 3);
        let key = CompoundKey{left: 1, right: 2};

        assert_eq!(key, edge.key());
        assert_eq!(key, DirectedEdge::<i32, i32>::generate_key((&1, &2)));
    }

    #[test]
    fn key_equality() {
        let key1 = CompoundKey{left: 1, right: 2};
        let key2 = CompoundKey{left: 1, right: 2};
        let key3 = CompoundKey{left: 2, right: 1};

        assert_eq!(key1, key2);
        assert_ne!(key1, key3);
    }
}