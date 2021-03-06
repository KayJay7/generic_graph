# generic_graph

A rust library providing traits for the implementation graphs.

All traits are defined using generics. Giving programmers more freedom in their implementation.

The default implementations provided are written with standard use cases in mind and should be suitable for most situations

## traits descriptions

### DirectedGraph

```rust
pub trait DirectedGraph<T, E, K, V, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Add + Sub + Eq + Ord + Copy,
          T: Vertex<K, V>,
          E: Edge<K, W, C>
{
    fn adjacent(&self, from: &K, to: &K) -> bool;

    fn neighbors(&self, from: &K) -> Vec<&K>;

    fn leading_to(&self, to: &K) -> Vec<&K>;

    fn get_all_keys(&self) -> Vec<&K>;

    fn get_all_pairs(&self) -> Vec<(&K, &K)>;

    fn get_vertex(&self, key: &K) -> Option<&T>;

    fn get_mut_vertex(&mut self, key: &K) -> Option<&mut T>;

    fn get_edge(&self, pair: (&K, &K)) -> Option<&E>;

    fn get_mut_edge(&mut self, pair: (&K, &K)) -> Option<&mut E>;
}
```

This is the main trait defined in this library. It is intended for implementing graphs with directed edges. 

* `adjacent` Takes the key of two vertexes and returns a boolean stating if exists an arc going from the first to the second
* `neighbors` Takes the key of a vertex and returns a vector containing the keys of all adjacent vertexes (reachable from the passed vertex)
* `leading_to` Takes the key of a vertex and returns a vector of the vertexes with the passed as neighbor
* The remaining are just getters

### Graph

```rust
pub trait Graph<T, E, K, V, W, C>: DirectedGraph<T, E, K, V, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Add + Sub + Eq + Ord + Copy,
          T: Vertex<K, V>,
          E: Edge<K, W, C>
{}
```

This traits does not define methods. It only specify that the graph is not directed.

This following properties must be held true:

* `graph.neighbors().sort() == graph.leading_to().sort()`
* `graph.get_edge((a, b)) == graph.get_edge((b, a))` (valid also for `get_mutable_edge()`)
* `graph.adjacent(a, b) == graph.adjacent(b, a)`

### VariableVertexes

```rust
pub trait VariableVertexes<T, E, K, V, W, C>: DirectedGraph<T, E, K, V, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Add + Sub + Eq + Ord + Copy,
          T: Vertex<K, V>,
          E: Edge<K, W, C>
{
    fn add_vertex(&mut self, vertex: T)  -> Option<T>;

    fn remove_vertex(&mut self, key: K) -> Option<T>;
}
```

This trait adds the add and remove methods for vertexes. Must be implemented in graphs with a variable number of vertexes

The `add_vertex()` method shall return None if the element was not previously set. Otherwise the element shall be updated (but no the key) 
and the old element shall be returned as `Some(old_element)`. 

The `remove_vertex()` method shall return None if the element was not found, or `Some(element)` if it was found.

### VariableEdges

```rust
pub trait VariableEdges<T, E, K, V, W, C>: DirectedGraph<T, E, K, V, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Add + Sub + Eq + Ord + Copy,
          T: Vertex<K, V>,
          E: Edge<K, W, C>
{
    fn add_edge(&mut self, edge: E) -> Result<Option<E>, EdgeSide>;

    fn remove_edge(&mut self, pair: (&K, &K)) -> Option<E>;
}

```

This trait adds the add and remove methods for edges. Must be implemented in graphs with a variable number of edges

The `add_edge()` method shall return `Ok(None)` if the element was not previously set. Otherwise the element shall be updated (but no the key) 
and the old element shall be returned as `Ok(Some(old_element))`. If one or both of the concerned vertexes are missing an error
containing an enum specifying which side is missing (`Err(EdgeSide)`)

The `remove_edge()` method shall return `None` if the element was not found, or `Some(element)` if it was found and removed.

### Vertex

```rust
pub trait Vertex<K, V>
    where K: Hash + Eq + Clone
{
    fn get_value(&self) -> &V;

    fn get_mut_value(&mut self) -> &mut V;

    fn key(&self) -> K;
}
```

This is the trait defining vertexes' behaviour. The Key type (`K`) must be hashable, equable (non just partially) and cloneable.
It is not required to implement copy, but it's suggested.

### Edge

```rust
pub trait Edge<K, W, C>
    where K: Hash + Eq + Clone,
          C: Hash + Eq + Clone,
          W: Add + Sub + Eq + Ord + Copy
{
    fn get_weight(&self) -> W;

    fn set_weight(&mut self, weight: W);

    fn left(&self) -> &K;

    fn right(&self) -> &K;

    fn get_pair(&self) -> (&K, &K);

    fn generate_key(pair: (&K, &K)) -> C;

    fn key(&self) -> C;
}
```

This trait defines the behaviour of edges. It needs two key types, one for vertexes (`K`) an one for edges (`C`). 
it also require a Weight type to be summable, subtractable, equable, ordered and copiable.

An edge must implement an associated function to generate a key from a pair of vertex's keys. 
The key of an edge must be generated by a pair of vertex keys and nothing else.

## default implementations

The library provides modules with a few default implementations, optimized for standard use cases. 
Check the objective of the implementations before choosing which to use, or if you should implement your own.

### AdjacencyList

A directed graph with mutable number of both vertexes and edges, meant for working with large growing graphs.

Vertexes' key and value types and edges' weight type are generics.

Its implemented using HashMaps to keep the structure fast still allowing it to grow in size

### AdjacencyMatrix (future implementation)

A directed graph meant for working with small fast graphs. Vertexes number is fixed, but edges can be added or deleted

Vertexes' key type is usize, Vertexes' value type and Edges' weight type are still generics.

This is implemented using a two dimensional matrix storing weights allowing direct access to edges 
at the cost of preventing mutability in the number of Vertexes

### (yet to be defined non directed graph)

A non directed implementation of graphs will be added in future

## Additional types

### SimpleVertex

```rust
pub struct SimpleVertex<K: Hash + Eq + Clone, V> {
    key: K,
    value: V,
}

impl<K: Hash + Eq + Clone, V> SimpleVertex<K, V> {
    pub fn new(key: K, value: V) -> SimpleVertex<K, V> {}
}

impl<K: Hash + Eq + Clone, V> Vertex<K, V> for SimpleVertex<K, V> {}
```

This type provides a simple default implementation for `Vertex` and should be adequate for most use cases

It comes with a `new()` associated function which is not defined by the trait

### EdgeSide

```rust
pub enum EdgeSide {
    Left,
    Right,
    Both
}
```

The `EdgeSide` type is simply an enum used to specify which side of an edge caused a particular situation. It is 
returned by the `add_edge()` method inside of a `Result::Err()` when the program is trying to add an edge to a graph but
one or both the vertex concerned are missing. Specifying which is missing.

It's intended to be used by user implemented functions for handling this type of situations. 