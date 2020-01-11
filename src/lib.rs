use std::hash::Hash;
use std::iter::Sum;

pub mod adjacency_list;

pub trait Vertex<K, V>
    where K: Hash + Eq + Clone
{
    fn get_value(&self) -> &V;

    fn get_mutable(&mut self) -> &mut V;

    fn key(&self) -> K;
}

pub trait Edge<K, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Sum + Eq + Ord + Copy
{
    fn get_weight(&self) -> W;

    fn set_weight(&mut self, weight: W);

    fn left(&self) -> &K;

    fn right(&self) -> &K;

    fn get_pair(&self) -> (&K, &K);

    fn generate_key(pair: (&K, &K)) -> C;

    fn key(&self) -> C;
}

pub trait DirectedGraph<T, E, K, V, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Sum + Eq + Ord + Copy,
          T: Vertex<K, V>,
          E: Edge<K, W, C>
{
    fn adjacent(&self, from: &K, to: &K) -> bool;

    fn neighbors(&self, from: &K) -> Vec<&K>;

    fn leading_to(&self, to: &K) -> Vec<&K>;

    fn get_vertex(&self, key: &K) -> Option<&T>;

    fn get_mutable_vertex(&mut self, key: &K) -> Option<&mut T>;

    fn get_edge(&self, pair: (&K, &K)) -> Option<&E>;

    fn get_mutable_edge(&mut self, pair: (&K, &K)) -> Option<&mut E>;
}

pub trait VariableEdges<T, E, K, V, W, C>: DirectedGraph<T, E, K, V, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Sum + Eq + Ord + Copy,
          T: Vertex<K, V>,
          E: Edge<K, W, C>
{
    fn add_edge(&mut self, edge: E);

    fn remove_edge(&mut self, pair: (&K, &K));
}

pub trait VariableVertexes<T, E, K, V, W, C>: DirectedGraph<T, E, K, V, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Sum + Eq + Ord + Copy,
          T: Vertex<K, V>,
          E: Edge<K, W, C>
{
    fn add_vertex(&mut self, vertex: T);

    fn remove_vertex(&mut self, key: K);
}

pub trait Graph<T, E, K, V, W, C>: DirectedGraph<T, E, K, V, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Sum + Eq + Ord + Copy,
          T: Vertex<K, V>,
          E: Edge<K, W, C>
{}

pub struct SimpleVertex<K: Hash + Eq + Clone, V> {
    key: K,
    value: V,
}

impl<K: Hash + Eq + Clone, V> SimpleVertex<K, V> {
    pub fn new(key: K, value: V) -> SimpleVertex<K, V> {
        SimpleVertex {
            key,
            value,
        }
    }
}

impl<K: Hash + Eq + Clone, V> Vertex<K, V> for SimpleVertex<K, V> {
    fn get_value(&self) -> &V {
        &(self.value)
    }

    fn get_mutable(&mut self) -> &mut V {
        &mut (self.value)
    }

    fn key(&self) -> K {
        self.key.clone()
    }
}