use std::{
    collections::{BinaryHeap, HashMap},
    hash::Hash,
};

/// A trait for types that can represent a graph edge.
pub trait GraphEdge<K>: Clone
where
    K: Copy,
{
    fn from(&self) -> K;
    fn to(&self) -> K;
}

/// A trait for types that can represent the maximum value.
pub trait Maximum {
    fn maximum() -> Self;
}

/// A trait for types that can represent the zero value (additive identity).
pub trait Zero {
    fn zero() -> Self;
}

/// A trait for weighted edges.
pub trait WeightedEdge<K>: GraphEdge<K>
where
    K: Copy,
{
    type Weight: std::ops::Add<Self::Weight, Output = Self::Weight> + Ord + Maximum + Zero + Copy;

    fn weight(&self) -> Self::Weight;
}

/// A trait for graph nodes.
pub trait GraphNode<K, E>: Default
where
    K: Copy + Eq + Hash,
    E: GraphEdge<K>,
{
    /// The key of the node.
    fn key(&self) -> K;

    /// Add an edge to the node.
    fn add_edge(&mut self, edge: E);

    /// Iterate over the edges of the node.
    fn for_each_edge<F>(&self, f: F)
    where
        F: FnMut(&E);

    /// Iterate over the edges of the node that go to a specific key.
    fn for_each_edge_to<F>(&self, key: K, mut f: F)
    where
        F: FnMut(&E),
    {
        self.for_each_edge(|e| {
            if e.to() == key {
                f(e)
            }
        })
    }
}

/// A graph data structure.
pub struct Graph<K, N, E>
where
    K: Copy + Eq + Hash,
    N: GraphNode<K, E>,
    E: GraphEdge<K>,
{
    nodes: HashMap<K, N>,

    _edge: std::marker::PhantomData<E>,
}

impl<K, N, E> Default for Graph<K, N, E>
where
    K: Copy + Eq + Hash,
    N: GraphNode<K, E>,
    E: GraphEdge<K>,
{
    fn default() -> Self {
        Self {
            nodes: HashMap::new(),
            _edge: std::marker::PhantomData,
        }
    }
}

impl<K, N, E> Graph<K, N, E>
where
    K: Copy + Eq + Hash,
    N: GraphNode<K, E>,
    E: GraphEdge<K>,
{
    /// Add a node to the graph.
    pub fn add_node(&mut self, node: N) { self.nodes.insert(node.key(), node); }

    pub fn add_node_by_key(&mut self, key: K) { self.nodes.entry(key).or_insert_with(N::default); }

    /// Get a node from the graph.
    pub fn node(&self, key: K) -> Option<&N> { self.nodes.get(&key) }

    /// Get a mutable node from the graph.
    pub fn node_mut(&mut self, key: K) -> Option<&mut N> { self.nodes.get_mut(&key) }

    /// Add an edge to the graph.
    pub fn add_edge(&mut self, edge: E) {
        let from = edge.from();
        self.nodes
            .entry(from)
            .or_insert_with(N::default)
            .add_edge(edge);
    }

    /// Iterate over the nodes of the graph with DFS.
    pub fn dfs<F>(&self, key: K, mut f: F)
    where
        F: FnMut(&N),
    {
        let mut visited = self
            .nodes
            .keys()
            .map(|k| (*k, false))
            .collect::<HashMap<_, _>>();

        fn dfs_helper<K, N, E, F>(
            graph: &Graph<K, N, E>,
            key: K,
            visited: &mut HashMap<K, bool>,
            f: &mut F,
        ) where
            K: Copy + Eq + Hash,
            N: GraphNode<K, E>,
            E: GraphEdge<K>,
            F: FnMut(&N),
        {
            if visited[&key] {
                return;
            }

            visited.insert(key, true);

            if let Some(node) = graph.node(key) {
                f(node);

                node.for_each_edge(|edge| {
                    dfs_helper(graph, edge.to(), visited, f);
                });
            }
        }

        dfs_helper(self, key, &mut visited, &mut f);
    }

    /// Iterate over the nodes of the graph with BFS.
    pub fn bfs<F>(&self, key: K, mut f: F)
    where
        F: FnMut(&N),
    {
        let mut visited = self
            .nodes
            .keys()
            .map(|k| (*k, false))
            .collect::<HashMap<_, _>>();

        let mut queue = std::collections::VecDeque::new();
        queue.push_back(key);

        while let Some(key) = queue.pop_front() {
            if visited[&key] {
                continue;
            }

            visited.insert(key, true);

            if let Some(node) = self.node(key) {
                f(node);

                node.for_each_edge(|edge| {
                    queue.push_back(edge.to());
                });
            }
        }
    }
}

impl<K, N, E> Graph<K, N, E>
where
    K: Copy + Eq + Hash,
    N: GraphNode<K, E>,
    E: WeightedEdge<K>,
{
    /// Dijkstra's algorithm.
    ///
    /// This will produce the shortest path from the start node to the end node,
    /// with a vector of nodes in between and the total weight of the path.
    pub fn dijkstra(&self, from: K) -> HashMap<K, (Vec<K>, E::Weight)> {
        struct State<K, W>
        where
            K: Copy + Eq + Hash,
            W: Ord + Copy,
        {
            key: K,
            weight: W,
        }

        impl<K, W> Ord for State<K, W>
        where
            K: Copy + Eq + Hash,
            W: Ord + Copy,
        {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering { other.weight.cmp(&self.weight) }
        }

        impl<K, W> PartialOrd for State<K, W>
        where
            K: Copy + Eq + Hash,
            W: Ord + Copy,
        {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl<K, W> Eq for State<K, W>
        where
            K: Copy + Eq + Hash,
            W: Ord + Copy,
        {
        }

        impl<K, W> PartialEq for State<K, W>
        where
            K: Copy + Eq + Hash,
            W: Ord + Copy,
        {
            fn eq(&self, other: &Self) -> bool { self.weight == other.weight }
        }

        impl<K, W> State<K, W>
        where
            K: Copy + Eq + Hash,
            W: Ord + Copy,
        {
            fn new(key: K, weight: W) -> Self { Self { key, weight } }
        }

        let mut prev: HashMap<K, K> = self.nodes.keys().map(|k| (*k, from)).collect();
        let mut heap = BinaryHeap::new();
        let mut dist = self
            .nodes
            .keys()
            .map(|k| (*k, E::Weight::maximum()))
            .collect::<HashMap<_, _>>();
        let mut visited = self
            .nodes
            .keys()
            .map(|k| (*k, false))
            .collect::<HashMap<_, _>>();

        dist.insert(from, E::Weight::zero());
        heap.push(State::new(from, E::Weight::zero()));

        while let Some(State { key, weight }) = heap.pop() {
            if visited[&key] {
                continue;
            }

            visited.insert(key, true);

            self.node(key).unwrap().for_each_edge(|edge| {
                let to = edge.to();
                let new_weight = weight + edge.weight();

                if new_weight < *dist.get(&to).unwrap() {
                    dist.insert(to, new_weight);
                    prev.insert(to, key);
                    heap.push(State::new(to, new_weight));
                }
            });
        }

        let mut result = HashMap::new();

        for (key, weight) in dist {
            let mut path = vec![];
            let mut current = key;

            while current != from {
                path.push(current);
                current = *prev.get(&current).unwrap();
            }

            path.push(from);
            path.reverse();

            result.insert(key, (path, weight));
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug)]
    struct Edge {
        from: i32,
        to: i32,
        weight: i32,
    }

    impl Edge {
        fn new(from: i32, to: i32, weight: i32) -> Self { Self { from, to, weight } }
    }

    impl GraphEdge<i32> for Edge {
        fn from(&self) -> i32 { self.from }

        fn to(&self) -> i32 { self.to }
    }

    impl Maximum for i32 {
        fn maximum() -> Self { Self::MAX }
    }

    impl Zero for i32 {
        fn zero() -> Self { 0 }
    }

    impl WeightedEdge<i32> for Edge {
        type Weight = i32;

        fn weight(&self) -> Self::Weight { self.weight }
    }

    #[derive(Default)]
    struct Node {
        key: i32,
        edges: Vec<Edge>,
    }

    impl GraphNode<i32, Edge> for Node {
        fn key(&self) -> i32 { self.key }

        fn add_edge(&mut self, edge: Edge) { self.edges.push(edge); }

        fn for_each_edge<F>(&self, f: F)
        where
            F: FnMut(&Edge),
        {
            self.edges.iter().for_each(f);
        }
    }

    #[test]
    fn test_graph() {
        let mut graph = Graph::<i32, Node, Edge>::default();

        let nodes = vec![
            Node {
                key: 0,
                edges: vec![Edge::new(0, 1, 1), Edge::new(0, 2, 4)],
            },
            Node {
                key: 1,
                edges: vec![Edge::new(1, 2, 2), Edge::new(1, 3, 5)],
            },
            Node {
                key: 2,
                edges: vec![Edge::new(2, 3, 1)],
            },
            Node {
                key: 3,
                edges: vec![Edge::new(3, 0, 3)],
            },
        ];

        for node in nodes {
            graph.add_node(node);
        }

        let result = graph.dijkstra(0);

        assert_eq!(result[&0].0, vec![0]);
        assert_eq!(result[&0].1, 0);
        assert_eq!(result[&1].0, vec![0, 1]);
        assert_eq!(result[&1].1, 1);
        assert_eq!(result[&2].0, vec![0, 1, 2]);
        assert_eq!(result[&2].1, 3);
        assert_eq!(result[&3].0, vec![0, 1, 2, 3]);
        assert_eq!(result[&3].1, 4);
    }
}
