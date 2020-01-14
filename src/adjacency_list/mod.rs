//!This module provide an implementation of a growable directed graph.
//! The graph is implemented as a set of adjacency list (list of vertex adjacent to one vertex).
//!
//!These lists consists of HashMaps, allowing the graph to grow to a considerable size while still
//! maintaining a certain speed. Though it is not indicated for small or not growing graphs
use super::{DirectedGraph, VariableEdges, VariableVertexes, SimpleVertex, Edge};
use std::collections::HashMap;
use std::hash::Hash;
use std::ops::{Add, Sub};

pub mod elements;
use elements::*;
use crate::{Vertex, EdgeSide};

//The type AdjacencyList is a private type meant to associate a vertex
// to its adjacency list
struct AdjacencyList<K, V, W>
    where K: Hash + Eq + Clone,
          W: Add + Sub + Eq + Ord + Copy,
{
    vertex: DirectedVertex<K, V>,
    list: HashMap<CompoundKey<K>, DirectedEdge<K, W>>,
}

///`AdjacencyGraph` implements a DirectedGraph using a set (one for every vertex) of lists containing
/// edges leading from the vertex to another. This lists are stored as HashMaps, allowing fast access
/// to vertexes and edges even with a large number of them or when they change quickly in number
///
///for small graphs this might not be the ideal implementation
pub struct AdjacencyGraph<K, V, W>
    where K: Hash + Eq + Clone,
          W: Add + Sub + Eq + Ord + Copy,
{
    vertexes: HashMap<K, AdjacencyList<K, V, W>>,
}

impl<K: Hash + Eq + Clone, V, W: Add + Sub + Eq + Ord + Copy> AdjacencyGraph<K, V, W> {

    ///Returns a new empty graph
    pub fn new() -> AdjacencyGraph<K, V, W>{
        AdjacencyGraph {
            vertexes: HashMap::new()
        }
    }
}

///`AdjacencyGraph` implement the DirectedGraph trait Specifying the vertex type (DirectedVertex),
/// the edge type (Directed Edge), and the edge key type (CompoundKey). But the vertex key type,
/// the vertex value type and the edge weight type remain generics.
impl<K: Hash + Eq + Clone, V, W: Add + Sub + Eq + Ord + Copy> DirectedGraph<
    DirectedVertex<K, V>,
    DirectedEdge<K, W>,
    K, V, W,
    CompoundKey<K>
> for AdjacencyGraph<K, V, W> {

    ///Check if an edge going from the first to the second vertex exists
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

    ///Returns a Vector containing the keys of the vertexes reached by edges leaving from the vertex identified by the passed key
    fn neighbors(&self, from: &K) -> Vec<&K> {
        let mut neighbors = Vec::new();

        if let Some(adjacency) = self.vertexes.get(from) {
            for (_, edge) in &adjacency.list {
                neighbors.push(edge.right());
            }
        }

        neighbors
    }

    ///Returns a vector containing the keys of the Vertexes from  which an edge leave to reach the vertex identified by the passed key
    fn leading_to(&self, to: &K) -> Vec<&K> {
        let mut leading = Vec::new();

        for (from, adjacency) in &self.vertexes {
            if let Some(_) = adjacency.list.get(&DirectedEdge::<K, W>::generate_key((from, &to))){
                leading.push(from);
            }
        }

        leading
    }

    ///Returns a reference to the vertex identified by the passed key
    fn get_vertex(&self, key: &K) -> Option<&SimpleVertex<K, V>> {
        if let Some(adjacency) = self.vertexes.get(&key) {
            Some(&adjacency.vertex)
        } else {
            None
        }
    }

    ///Returns a mutable reference to the vertex identified by the passed key
    fn get_mutable_vertex(&mut self, key: &K) -> Option<&mut SimpleVertex<K, V>> {
        if let Some(adjacency) = self.vertexes.get_mut(&key) {
            Some(&mut adjacency.vertex)
        } else {
            None
        }
    }

    ///Returns a reference to the edge identified by the passed pair of keys
    fn get_edge(&self, pair: (&K, &K)) -> Option<&DirectedEdge<K, W>> {
        if let Some(adjacency) = self.vertexes.get(pair.0) {
            adjacency.list.get(&DirectedEdge::<K, W>::generate_key(pair))
        } else {
            None
        }
    }

    ///Returns a mutable reference to the edge identified by the passed pair of keys
    fn get_mutable_edge(&mut self, pair: (&K, &K)) -> Option<&mut DirectedEdge<K, W>> {
        if let Some(adjacency) = self.vertexes.get_mut(pair.0) {
            adjacency.list.get_mut(&DirectedEdge::<K, W>::generate_key(pair))
        } else {
            None
        }
    }
}

///`AdjacencyGraph` uses HashMaps to store vertexes, allowing fast insertion and removal of the latter
impl<K: Hash + Eq + Clone, V, W: Add + Sub + Eq + Ord + Copy> VariableVertexes<
    DirectedVertex<K, V>,
    DirectedEdge<K, W>,
    K, V, W,
    CompoundKey<K>
> for AdjacencyGraph<K, V, W>
{

    ///This method adds (or, if present, updates maintaining its edges) a vertex and returns None ore Some(old_vertex)
    ///
    /// # Examples
    /// ```rust
    /// use generic_graph::adjacency_list::AdjacencyGraph;
    /// use generic_graph::{SimpleVertex, VariableVertexes};
    /// let mut graph = AdjacencyGraph::<i32, i32, i32>::new();
    ///
    /// assert_eq!(None, graph.add_vertex(SimpleVertex::new(1, 2)));
    /// assert_eq!(None, graph.add_vertex(SimpleVertex::new(2, 3)));
    /// assert_eq!(Some(SimpleVertex::new(1, 2)), graph.add_vertex(SimpleVertex::new(1, 3)))
    /// ```
    fn add_vertex(&mut self, vertex: SimpleVertex<K, V>) -> Option<SimpleVertex<K, V>> {
        if let Some(
            AdjacencyList{
                vertex: old_vertex,
                list
            }) = self.vertexes.remove(&vertex.key()) {

            self.vertexes.insert(
                vertex.key(),
                AdjacencyList {
                    vertex,
                    list
                });

            Some(old_vertex)
        } else {

            self.vertexes.insert(
                vertex.key(),
                AdjacencyList {
                    vertex,
                    list: HashMap::new()
                });

            None
        }
    }

    ///This method removes a vertex and its edges from the graph and returns None ore Some(old_vertex)
    ///
    /// # Examples
    /// ```rust
    /// use generic_graph::adjacency_list::AdjacencyGraph;
    /// use generic_graph::{SimpleVertex, VariableVertexes};
    /// let mut graph = AdjacencyGraph::<i32, i32, i32>::new();
    /// graph.add_vertex(SimpleVertex::new(1, 2));
    /// graph.add_vertex(SimpleVertex::new(2, 3));
    ///
    /// assert_eq!(None, graph.remove_vertex(0));
    /// assert_eq!(Some(SimpleVertex::new(1, 2)), graph.remove_vertex(1));
    /// assert_eq!(Some(SimpleVertex::new(2, 3)), graph.remove_vertex(2));
    /// assert_eq!(None, graph.remove_vertex(1));
    /// ```
    fn remove_vertex(&mut self, key: K) -> Option<SimpleVertex<K, V>> {
        for (from, adjacency) in &mut self.vertexes {
            adjacency.list.remove(&DirectedEdge::<K, W>::generate_key((from, &key)));
        }

        if let Some(
            AdjacencyList{
                vertex: old_vertex,
                list: _
            }) = self.vertexes.remove(&key) {
            Some(old_vertex)
        } else {
            None
        }
    }
}

//TODO document the VariableEdges implementation for AdjacencyList
///`AdjacencyGraph` uses HashMaps to store edges, allowing fast insertion and removal of the latter
impl<K: Hash + Eq + Clone, V, W: Add + Sub + Eq + Ord + Copy> VariableEdges<
    DirectedVertex<K, V>,
    DirectedEdge<K, W>,
    K, V, W,
    CompoundKey<K>
> for AdjacencyGraph<K, V, W>
{

    ///The `add_edge()` method shall return `Ok(None)` if the element was not previously set. Otherwise the element shall be updated (but no the key)
    /// and the old element shall be returned as `Ok(Some(old_element))`. If one or both of the concerned vertexes are missing an error
    /// containing an enum specifying which side is missing (`Err(EdgeSide)`)
    ///
    /// # Examples
    /// ```rust
    /// use generic_graph::adjacency_list::AdjacencyGraph;
    /// use generic_graph::{SimpleVertex, VariableVertexes, VariableEdges};
    /// use generic_graph::adjacency_list::elements::DirectedEdge;
    /// use generic_graph::EdgeSide::Right;
    /// let mut graph = AdjacencyGraph::<i32, i32, i32>::new();
    /// graph.add_vertex(SimpleVertex::new(1, 2));
    /// graph.add_vertex(SimpleVertex::new(2, 3));
    /// graph.add_vertex(SimpleVertex::new(3, 4));
    ///
    /// assert_eq!(Ok(None), graph.add_edge(DirectedEdge::new(1, 2, 0)));
    /// assert_eq!(Ok(None), graph.add_edge(DirectedEdge::new(2, 1, 0)));
    /// assert_eq!(Ok(None), graph.add_edge(DirectedEdge::new(3, 2, 0)));
    /// assert_eq!(
    ///      Ok(Some(DirectedEdge::new(1, 2, 0))),
    ///      graph.add_edge(DirectedEdge::new(1, 2, 3))
    /// );
    /// assert_eq!(Err(Right), graph.add_edge(DirectedEdge::new(1, 4, 0)));
    /// ```
    fn add_edge(&mut self, edge: DirectedEdge<K, W>) -> Result<Option<DirectedEdge<K, W>>, EdgeSide> {
        if let Some(_) =  self.vertexes.get(&edge.right()) {
            if let Some(AdjacencyList {
                            vertex: _,
                            list
                        }) = self.vertexes.get_mut(&edge.left()) {

                Ok(if let Some(old_edge) = list.remove(&edge.key()) {
                    list.insert(edge.key(), edge);
                    Some(old_edge)
                } else {
                    list.insert(edge.key(), edge);
                    None
                })

            } else {
                Err(EdgeSide::Left)
            }
        } else {

            if let Some(_) =  self.vertexes.get(&edge.left()){
                Err(EdgeSide::Right)
            } else {
                Err(EdgeSide::Both)
            }

        }
    }

    fn remove_edge(&mut self, pair: (&K, &K)) -> Option<DirectedEdge<K, W>> {
        if let Some(adjacency) = self.vertexes.get_mut(pair.0) {
            adjacency.list.remove(&DirectedEdge::<K, W>::generate_key(pair))
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