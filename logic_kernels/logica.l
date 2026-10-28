# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright Ahmad Ali Parr
# Logica kernel: two-hop graph reachability (nonrecursive SQL lowering).
Edge("ada", "bob");
Edge("bob", "cy");
Edge("cy", "dee");

Reach2(x, y) :- Edge(x, y);
Reach2(x, z) :- Edge(x, y), Edge(y, z);

@OrderBy(Reach2, "x, y");
