
use std::collections::HashMap;
use std::fmt;

#[derive(Default)]
pub struct DirectedGraph {
  /// indexes self
  pub vertex_edges : Vec<Vec<usize>>
}

impl DirectedGraph {
  pub fn edges(&self, i : usize) -> &[usize] {
    self.vertex_edges[i].as_slice()
  }

  pub fn vertex_count(&self) -> usize {
    self.vertex_edges.len()
  }
}

impl  fmt::Display for DirectedGraph {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    writeln!(f, "DirectedGraph{{")?;
    for (i, edges) in self.vertex_edges.iter().enumerate() {
      writeln!(f, "  {}: {:?}", i, edges)?;
    }
    writeln!(f, "}}")
  }
}

#[derive(Copy, Clone)]
struct VertFlag {
  complete : bool,
  active : bool,
}

/// Returns a valid topological ordering if the graph is a DAG. Returns an error if the graph contains cycles.
pub fn valid_topological_ordering(g : &DirectedGraph) -> Result<Vec<usize>, ()> {
  fn visit(ordering : &mut Vec<usize>, flags : &mut [VertFlag], g : &DirectedGraph, i : usize) -> Result<(), ()> {
    if flags[i].complete { return Ok(()) }
    if flags[i].active { return Err(()) };
    flags[i].active = true;
    for &w in g.edges(i) {
      visit(ordering, flags, g, w)?;
    }
    flags[i].active = false;
    flags[i].complete = true;
    ordering.push(i);
    Ok(())
  }

  let mut ordering = vec![];
  let mut flags = vec![ VertFlag{ complete: false, active: false }; g.vertex_count() ];
  for i in 0..g.vertex_count() {
    visit(&mut ordering, flags.as_mut_slice(), g, i)?;
  }
  ordering.reverse();
  Ok(ordering)
}

/// Builds a graph based on the connectivity between disjoint subgraphs. Will behave incorrectly
/// if the subgraphs are not disjoint.
pub fn graph_of_disjoint_subgraphs(subgraphs : &[Vec<usize>], g : &DirectedGraph) -> DirectedGraph {
  let mut vert_map = HashMap::new();
  for (b, subgraph) in subgraphs.iter().enumerate() {
    for &a in subgraph {
      vert_map.insert(a, b);
    }
  }
  let mut new_graph : DirectedGraph = Default::default();
  for (new_a, subgraph) in subgraphs.iter().enumerate() {
    let mut edges = vec![];
    for &old_a in subgraph {
      for old_b in g.edges(old_a) {
        let new_b = *vert_map.get(&old_b).unwrap();
        if new_a != new_b {
          edges.push(new_b);
        }
      }
    }
    edges.sort();
    edges.dedup();
    new_graph.vertex_edges.push(edges);
  }
  new_graph
}

/// Vertices should be numbered from `0` to `vertex_count - 1`. Edges should index this range.
/// Uses tarjan's algorithm. A component is a connected subgraph. A strongly-connected component
/// is a subgraph in which every node is reachable from every other node.
pub fn get_strongly_connected_components(g : &DirectedGraph) -> Vec<Vec<usize>> {
  let mut vs =
    (0..g.vertex_count())
      .map(|i| TarjanVert { index: i, lowlink: i, on_stack: false, visited: false })
      .collect::<Vec<_>>();
  let tarjan = Tarjan {
    stack: vec![],
    strongly_connected_components: vec![],
    verts: vs.as_mut_slice(),
    g,
  };
  tarjan.to_strongly_connected_components()
}

#[derive(Copy, Clone)]
struct TarjanVert {
  index : usize,
  lowlink : usize,
  on_stack : bool,
  visited : bool,
}

struct Tarjan<'l> {
  stack : Vec<usize>,
  strongly_connected_components : Vec<Vec<usize>>,
  verts : &'l mut [TarjanVert],
  g : &'l DirectedGraph,
}

impl <'l> Tarjan<'l> {
  
  fn to_strongly_connected_components(mut self) -> Vec<Vec<usize>> {
    for v in 0..self.verts.len() {
      if !self.verts[v].visited {
        self.strong_connect(v);
      }
    }
    self.strongly_connected_components
  }

  fn strong_connect(&mut self, v : usize) {
    use std::cmp::min;

    self.verts[v].visited = true;
    self.stack.push(v);
    self.verts[v].on_stack = true;
  
    for &w in self.g.edges(v) {
      if !self.verts[w].visited {
        // Successor w has not yet been visited; recurse on it
        self.strong_connect(w);
        self.verts[v].lowlink =
          min(self.verts[v].lowlink, self.verts[w].lowlink);
      }
      else if self.verts[w].on_stack {
        // Successor w is in stack S and hence in the current SCC
        // If w is not on stack, then (v, w) is a cross-edge in the
        // depth-first-search tree and must be ignored.
        self.verts[v].lowlink =
          min(self.verts[v].lowlink, self.verts[w].index);
      }
    }
  
    // If v is a root node, pop the stack and generate an SCC
    if self.verts[v].lowlink == self.verts[v].index {
      let mut scc = vec![]; // start a new strongly connected component
      loop {
        let w = self.stack.pop().unwrap();
        self.verts[w].on_stack = false;
        scc.push(w);
        if w == v { break }
      }
      // output the current strongly connected component
      self.strongly_connected_components.push(scc);
    }
  }
}
