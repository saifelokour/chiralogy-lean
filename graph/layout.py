#!/usr/bin/env python3
"""Compute the frozen layout once, from the spine alone.

Positions are a DERIVED artifact like the spine and the labelings, and once written they are not
recomputed by anything downstream. The renderer reads them and never reflows: layout stability is what
makes an invariant visible, since a subset that stays lit is only legible if nothing has moved.

The embedding is force directed on the undirected spine with a fixed seed. It is CENTER FREE: no radial
or centrality based placement is used, and distance from the middle of the frame carries no meaning. The
structure has no center to encode, so none is invented.

Deterministic: nodes and edges sorted before layout, seed fixed, coordinates rounded.

Run from the repo root:  python3 graph/layout.py
"""
import json, os

import networkx as nx

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GRAPH = os.path.join(ROOT, "graph")

spine = json.load(open(os.path.join(GRAPH, "spine.json")))
nodes = sorted(spine["nodes"])
edges = sorted((e["source"], e["target"]) for e in spine["edges"])

G = nx.Graph()
G.add_nodes_from(nodes)
G.add_edges_from(edges)

# Components are laid out separately so that the fifty small ones and the thirty six isolates cannot
# compress the one that carries the structure. Order is deterministic: size descending, then least name.
comps = sorted(nx.connected_components(G), key=lambda c: (-len(c), min(c)))
main, rest = comps[0], comps[1:]

sub = G.subgraph(sorted(main)).copy()
raw = nx.spring_layout(sub, seed=1, iterations=400, k=2.6 / (len(main) ** 0.5))
xs = [p[0] for p in raw.values()]
ys = [p[1] for p in raw.values()]
x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
span = max(x1 - x0, y1 - y0) or 1.0
MAIN_W = 0.80
pos = {n: [(raw[n][0] - x0) / span * MAIN_W, (raw[n][1] - y0) / span] for n in main}

# The remainder occupies a reserved band at the right, in a deterministic grid, so it is present and
# separable rather than flung through the middle.
band = [n for c in rest for n in sorted(c)]
cols = 6
for i, n in enumerate(band):
    r, c = divmod(i, cols)
    pos[n] = [MAIN_W + 0.04 + 0.028 * c, 0.02 + 0.036 * r]


def norm(p):
    return [round(p[0], 6), round(p[1], 6)]


out = {
    "layout": "spine-force-seed1",
    "title": "Frozen positions for the spine, computed once and never reflowed.",
    "derivedFrom": "spine",
    "derivation": "Components sorted by size then least name. The largest is embedded force directed with "
                  "seed 1 and 400 iterations and normalised into the left four fifths of the frame; the "
                  "remaining components and isolates fill a reserved band at the right in a deterministic "
                  "grid. Center free: no radial or centrality placement, and distance from the middle "
                  "carries no meaning.",
    "positions": {n: norm(pos[n]) for n in nodes},
}
with open(os.path.join(GRAPH, "layout.json"), "w") as f:
    json.dump(out, f, indent=1, sort_keys=True)
    f.write("\n")
print(f"layout: {len(nodes)} positions, frozen")
