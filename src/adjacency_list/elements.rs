use crate::Edge;
pub use crate::SimpleVertex as DirectedVertex;
use std::hash::Hash;
use std::iter::Sum;
use std::ops::Sub;

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct CompoundKey<K: Hash + Eq + Clone> {
    left: K,
    right: K,
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub struct DirectedEdge<K, W>
    where K: Hash + Eq + Clone,
          W: Sum + Sub + Eq + Ord + Copy,
{
    left: K,
    right: K,
    weight: W,
}

impl<K: Hash + Eq + Clone, W: Sum + Sub + Eq + Ord + Copy> DirectedEdge<K, W> {
    pub fn new(left: K, right: K, weight: W) -> DirectedEdge<K, W> {
        DirectedEdge {
            left,
            right,
            weight,
        }
    }
}

impl<K: Hash + Eq + Clone, W: Sum + Sub + Eq + Ord + Copy> Edge<K, W, CompoundKey<K>> for DirectedEdge<K, W> {
    fn get_weight(&self) -> W {
        self.weight
    }

    fn set_weight(&mut self, weight: W) {
        self.weight = weight;
    }

    fn left(&self) -> &K {
        &self.left
    }

    fn right(&self) -> &K {
        &self.right
    }

    fn get_pair(&self) -> (&K, &K) {
        (&self.left, &self.right)
    }

    fn generate_key(pair: (&K, &K)) -> CompoundKey<K> {
        CompoundKey {
            left: pair.0.clone(),
            right: pair.1.clone()
        }
    }

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