# Logica kernel: two-hop graph reachability (nonrecursive SQL lowering).
Edge("ada", "bob");
Edge("bob", "cy");
Edge("cy", "dee");

Reach2(x, y) :- Edge(x, y);
Reach2(x, z) :- Edge(x, y), Edge(y, z);

@OrderBy(Reach2, "x, y");
