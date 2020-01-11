use super::{DirectedGraph, VariableEdges, VariableVertexes, SimpleVertex, Edge};
use std::collections::HashMap;
use std::hash::Hash;
use std::iter::Sum;

pub mod elements;
use elements::*;


struct AdjacencyList<K, V, W>
    where K: Hash + Eq + Clone,
          W: Sum + Eq + Ord + Copy,
{
    vertex: DirectedVertex<K, V>,
    list: HashMap<CompoundKey<K>, DirectedEdge<K, W>>,
}

pub struct AdjacencyGraph<K, V, W>
    where K: Hash + Eq + Clone,
          W: Sum + Eq + Ord + Copy,
{
    vertexes: HashMap<K, AdjacencyList<K, V, W>>,
}

impl<K: Hash + Eq + Clone, V, W: Sum + Eq + Ord + Copy> AdjacencyGraph<K, V, W> {
    pub fn new() -> AdjacencyGraph<K, V, W>{
        AdjacencyGraph {
            vertexes: HashMap::new()
        }
    }
}

impl<K: Hash + Eq + Clone, V, W: Sum + Eq + Ord + Copy> DirectedGraph<
    DirectedVertex<K, V>,
    DirectedEdge<K, W>,
    K, V, W,
    CompoundKey<K>
> for AdjacencyGraph<K, V, W> {
    fn adjacent(&self, from: &K, to: &K) -> bool {
        if let Some(adjacency) = self.vertexes.get(from) {
            if let Some(_) = adjacency.list.get(&DirectedEdge::<K, W>::generate_key((from, to))) {
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    fn neighbors(&self, from: &K) -> Vec<&K> {
        let mut neighbors = Vec::new();

        if let Some(adjacency) = self.vertexes.get(from) {
            for (_, edge) in &adjacency.list {
                neighbors.push(edge.right());
            }
        }

        neighbors
    }

    fn leading_to(&self, to: &K) -> Vec<&K> {
        let mut leading = Vec::new();

        for (from, adjacency) in &self.vertexes {
            if let Some(_) = adjacency.list.get(&DirectedEdge::<K, W>::generate_key((from, &to))){
                leading.push(from);
            }
        }

        leading
    }

    fn get_vertex(&self, key: &K) -> Option<&SimpleVertex<K, V>> {
        if let Some(adjacency) = self.vertexes.get(&key) {
            Some(&adjacency.vertex)
        } else {
            None
        }
    }

    fn get_mutable_vertex(&mut self, key: &K) -> Option<&mut SimpleVertex<K, V>> {
        if let Some(adjacency) = self.vertexes.get_mut(&key) {
            Some(&mut adjacency.vertex)
        } else {
            None
        }
    }

    fn get_edge(&self, pair: (&K, &K)) -> Option<&DirectedEdge<K, W>> {
        if let Some(adjacency) = self.vertexes.get(pair.0) {
            adjacency.list.get(&DirectedEdge::<K, W>::generate_key(pair))
        } else {
            None
        }
    }

    fn get_mutable_edge(&mut self, pair: (&K, &K)) -> Option<&mut DirectedEdge<K, W>> {
        if let Some(adjacency) = self.vertexes.get_mut(pair.0) {
            adjacency.list.get_mut(&DirectedEdge::<K, W>::generate_key(pair))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn getters() {
        let edge = DirectedEdge::new(1, 2, 3);
        assert_eq!((&1, &2, 3),
                   (edge.left(), edge.right(), edge.get_weight()));
    }
}