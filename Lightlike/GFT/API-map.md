# Colored graphs of group field theory

## Abstract (Alpha)

This API treats the combinatorics of colored graphs, the Feynman graphs of the colored group field
theory. A colored graph has vertices of two orientations and lines of one of several colors, with
exactly one line of each color at every vertex and every line joining opposite orientations. Its
connected pieces made of a given set of colors are the bubbles, and the graph is dual to a
triangulated pseudo-manifold whose simplices are the bubbles. In dimension two the Euler
characteristic of the dual, and so its genus, is computed from the number of vertices and of
bicolored cycles.

## Content (Alpha)

A colored graph of dimension `D` is given by one involution per color without fixed points and an
orientation that every involution flips [1]. The bubble of a vertex for a set of colors is the set of
vertices reachable along lines of those colors, and the `0`-bubbles are the vertices [1]. In
dimension two the dual complex has one triangle for each vertex, one edge for each line and one
vertex for each bicolored cycle, so its Euler characteristic is the number of bicolored cycles
minus half the number of vertices [1]. The graph with two vertices gives the 2-sphere and a graph
with six vertices gives the torus [1]. A graph with two lines of one color at a vertex is not a
colored graph [1]. That the dual of every colored graph is a normal simplicial pseudo-manifold, and
the identification of the bubbles with the links of the dual simplices, are due to Gurau {1}; they
are [TODO] here.

## Lean References

1. Lightlike/GFT/ColoredGraph.lean - `GFT.ColoredGraph`, `GFT.ColoredGraph.inv_ne`,
   `GFT.ColoredGraph.bubble`, `GFT.ColoredGraph.nBubbles`, `GFT.ColoredGraph.mem_bubble_iff`, `GFT.ColoredGraph.nBubbles_empty`, `GFT.ColoredGraph.even_card`,
   `GFT.not_nonempty_coloredGraph_fin3`,
   `GFT.ColoredGraph.twoChi2`, `GFT.theta`, `GFT.twoChi2_theta`, `GFT.torus`, `GFT.twoChi2_torus`,
   `GFT.IsProper`, `GFT.badLines_not_proper`

## References

1. R. Gurau, Lost in translation: topological singularities in group field theory, *Class. Quantum
   Grav.* 27 (2010) 235023, arXiv:1006.0714.
