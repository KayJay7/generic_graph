//! # generic_graph
//!
//!`generic_graph` defines a series of traits for the implementation of either directed and
//! non directed graphs. This library also provides a few default implementation if the programmer
//! doesn't have special requirements for his graphs.
//!
//!All traits make large use of generic types, allowing for deep customization of the graph structure
//!
use std::hash::Hash;
use std::ops::{Add, Sub};
pub mod adjacency_list;

///Generic behaviour of a vertex
///
/// Key type (K) must implement Hash, Eq and Clone
///
/// Value type is free
pub trait Vertex<K, V>
    where K: Hash + Eq + Clone
{
    fn get_value(&self) -> &V;

    fn get_mutable(&mut self) -> &mut V;

    fn key(&self) -> K;
}

///Generic behaviour of an edge
///
///Generic type C is the key type of the edge
///
///Generic type K is the key type of the vertexes connected by the edge
///
///Generic type W is
pub trait Edge<K, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Add + Sub + Eq + Ord + Copy
{
    fn get_weight(&self) -> W;

    fn set_weight(&mut self, weight: W);

    fn left(&self) -> &K;

    fn right(&self) -> &K;

    ///This pair must not be used as a key for the edge, this must instead be used to generate the key
    /// or to construct a new edge
    fn get_pair(&self) -> (&K, &K);

    ///An associated function constructing the edge key from a pair of
    /// vertex keys must be implemented for the edge tipe
    ///
    ///the key returned by the key(&self) method must correspond to the key generated by said function
    /// with the pair of keys returned by the method get_pair(&self)
    fn generate_key(pair: (&K, &K)) -> C;

    ///The key returned by this method must correspond to the key generated by passing the pair of keys
    /// returned by get_pair(&self) to rhe associated function generate_key(pair: (&T, &T))
    fn key(&self) -> C;
}


///This trait define the behaviour of a directed graph
/// it requires the for vertexes (T), edges (E), vertex's keys (K), vertex's values (v), edge's weights (W) and edge's keys (C)
pub trait DirectedGraph<T, E, K, V, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Add + Sub + Eq + Ord + Copy,
          T: Vertex<K, V>,
          E: Edge<K, W, C>
{
    ///This method returns a boolean stating if exist an edge from the first vertex to the other
    fn adjacent(&self, from: &K, to: &K) -> bool;

    ///This method returns a vector containing the keys of all the vertexes reached by edges starting from the argument
    fn neighbors(&self, from: &K) -> Vec<&K>;

    ///This method returns a vector containing the keys of all the vertexes with by edges leading to the argument
    fn leading_to(&self, to: &K) -> Vec<&K>;

    fn get_vertex(&self, key: &K) -> Option<&T>;

    fn get_mutable_vertex(&mut self, key: &K) -> Option<&mut T>;

    fn get_edge(&self, pair: (&K, &K)) -> Option<&E>;

    fn get_mutable_edge(&mut self, pair: (&K, &K)) -> Option<&mut E>;
}

///This trait adds to a Directed graph the methods to add and remove edges
pub trait VariableEdges<T, E, K, V, W, C>: DirectedGraph<T, E, K, V, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Add + Sub + Eq + Ord + Copy,
          T: Vertex<K, V>,
          E: Edge<K, W, C>
{
    ///If an edge with an equal key is already present, the edge is updated (not the key)
    /// and the old edge is returned ad Ok(Some(old_edge)). If not present OK(None) is returned.
    ///
    ///If one or both of the concerned vertexes are missing an error will be returned containing
    /// an enum specifying which side is missing
    fn add_edge(&mut self, edge: E) -> Result<Option<E>, EdgeSide>;

    ///If the removed edge was present it's removed and returned as Some(edge). Otherwise None is returned
    fn remove_edge(&mut self, pair: (&K, &K)) -> Option<E>;
}

///This trait adds to a Directed graph the methods to add and remove edges
pub trait VariableVertexes<T, E, K, V, W, C>: DirectedGraph<T, E, K, V, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Add + Sub + Eq + Ord + Copy,
          T: Vertex<K, V>,
          E: Edge<K, W, C>
{
    ///If a vertex with an equal key is already present, the vertex is updated (not the key)
    /// and the old vertex is returned ad Some(old_vertex). If not present None is returned.
    fn add_vertex(&mut self, vertex: T) -> Option<T>;

    ///If the removed vertex was present it's removed and returned as Some(vertex). Otherwise None is returned
    fn remove_vertex(&mut self, key: K) -> Option<T>;
}

///This trait does not add methods. It just indicates that the graph is not directed.
///
///As such, the vectors returned by the method neighbors(&self, from: &K) and leading_to(&self, to: &K)
/// contains the same keys, eventually in different order (Unless the graph muted between calls).
///
///Also the outcome the methods accepting a pair of keys (adjacent(...), get_edge(...), get_mutable_edge(...))
/// must not be influenced by the order of the keys.
pub trait Graph<T, E, K, V, W, C>: DirectedGraph<T, E, K, V, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Add + Sub + Eq + Ord + Copy,
          T: Vertex<K, V>,
          E: Edge<K, W, C>
{}

///A default implementation for vertexes. This implementation should be suitable for most of the
/// problem one can encounter requiring graph.
///
///Contrary to other graph implementation this library does not expect the vertexes to store if they
/// have been visited, or if they were marked. The reason for this is that the author believes such an
/// information should be stored in a structure extern and independent to the graph, this to ensure
/// consistency between threads and to allow different algorithms to use different structures according
/// to their needs
///
///methods are self explanatory
#[derive(Debug, Eq, PartialEq)]
pub struct SimpleVertex<K: Hash + Eq + Clone, V> {
    key: K,
    value: V,
}

impl<K: Hash + Eq + Clone, V> SimpleVertex<K, V> {

    ///Creates a new instance of SimpleVertex
    pub fn new(key: K, value: V) -> SimpleVertex<K, V> {
        SimpleVertex {
            key,
            value,
        }
    }
}

///`EdgeSide` is used to indicate which side of the edge caused an error.
/// Usually returned as Result::Err(EdgeSide) by the VariableEdges::add_edge() method when
/// it was impossible to add the edge due to the absence of one of the concerned vertexes.
///
///Can be used by user defined functions or types for error handling.
#[derive(Debug, Eq, PartialEq)]
pub enum EdgeSide {
    Left,
    Right,
    Both
}

///`SimpleVertex` implement the Vertex trait maintaining the key type and the value type generics
impl<K: Hash + Eq + Clone, V> Vertex<K, V> for SimpleVertex<K, V> {

    ///Get the value stored in a vertex
    fn get_value(&self) -> &V {
        &(self.value)
    }

    ///Get the value as mutable reference
    fn get_mutable(&mut self) -> &mut V {
        &mut (self.value)
    }

    ///Returns the key of the vertex
    fn key(&self) -> K {
        self.key.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_vertex_construction() {
        let vertex = SimpleVertex::new(1,0);

        assert_eq!(vertex, SimpleVertex {key: 1, value: 0});
    }

    #[test]
    fn simple_vertex_getters() {
        let mut vertex = SimpleVertex::new(1,0);

        assert_eq!(vertex.get_value(), &0);
        assert_eq!(vertex.key(), 1);

        *vertex.get_mutable() += 3;
        assert_eq!(vertex.get_value(), &3);
    }
}