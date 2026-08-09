#!/usr/bin/env python3
"""Compute the frozen layout once, from the spine and the derived territory decomposition.

POSITION ENCODES STRUCTURE. A declaration sits inside the region of the territory it belongs to, and
within that region its place is fixed by dependency depth from the territory's root. The territory
decomposition is the one the graph findings already use: a root is a sink whose territory reaches at
least ten declarations, and its territory is everything depending on it transitively. That assignment is
a labeling, graph/labelings/territory.json, derived and fixed like every other; this file consumes it
and invents nothing.

NO EMBEDDING. There is no force layout here. An iterative embedding places nodes by an algorithm's
accident rather than by the structure, and it proved irreproducible across processes even with the
initial state pinned, which a frozen artifact cannot be. Every coordinate below is closed form and
derived. The cost is real and worth stating: proximity no longer indicates adjacency, so local edge
structure has to be read from the edges themselves rather than from where things sit.

CENTER FREE. Regions are packed to fill the frame. No region is at a center, no radius is used, and
distance from the middle of the frame carries no meaning. Region AREA encodes territory size, which is
derived structure; region POSITION encodes nothing beyond the packing order.

NO SEGREGATED BAND. Declarations no root reaches are not parked somewhere separate: unrooted is a region
like the others, named and packed alongside them, because being reached by no root is a structural fact
and not a leftover.

FROZEN. Once written these positions are read and never recomputed. Layout stability is what makes an
invariant visible: a subset that stays lit is only legible if nothing has moved.

Deterministic: no randomness and no iteration anywhere. Verified byte identical across processes.

Run from the repo root:  python3 graph/layout.py
"""
import json, os
from collections import defaultdict

import networkx as nx

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GRAPH = os.path.join(ROOT, "graph")

spine = json.load(open(os.path.join(GRAPH, "spine.json")))
territory = json.load(open(os.path.join(GRAPH, "labelings", "territory.json")))["values"]
weight = json.load(open(os.path.join(GRAPH, "labelings", "load-bearing-weight.json")))["values"]

nodes = sorted(spine["nodes"])
edges = sorted((e["source"], e["target"]) for e in spine["edges"])

members = defaultdict(list)
for n in nodes:
    members[territory[n]].append(n)
regions = sorted(members, key=lambda t: (-len(members[t]), t))


def squarify(items, x, y, w, h):
    """Squarified treemap. Deterministic: consumes items in the order given."""
    out = {}
    total = sum(s for _, s in items)
    if total <= 0:
        return out
    items = list(items)
    while items:
        if len(items) == 1:
            out[items[0][0]] = (x, y, w, h)
            break
        short = min(w, h)
        row, best, rest = [], None, items[:]
        while rest:
            trial = row + [rest[0]]
            s = sum(v for _, v in trial)
            length = ((s / total) * (w * h)) / short if short else 0
            worst = (max(max(length / ((v / s) * short), ((v / s) * short) / length)
                         for _, v in trial) if length and s else float("inf"))
            if best is None or worst <= best:
                best, row = worst, trial
                rest.pop(0)
            else:
                break
        s = sum(v for _, v in row)
        if w >= h:
            rw = (s / total) * w
            oy = y
            for k, v in row:
                rh = h * (v / s)
                out[k] = (x, oy, rw, rh)
                oy += rh
            x, w, total = x + rw, w - rw, total - s
        else:
            rh = (s / total) * h
            ox = x
            for k, v in row:
                rw = w * (v / s)
                out[k] = (ox, y, rw, rh)
                ox += rw
            y, h, total = y + rh, h - rh, total - s
        items = items[len(row):]
    return out


rects = squarify([(t, len(members[t])) for t in regions], 0.0, 0.0, 1.0, 1.0)

G = nx.Graph()
G.add_nodes_from(nodes)
G.add_edges_from(edges)

pred = defaultdict(list)
for a, b in edges:
    pred[b].append(a)


def depth_from(root, ns):
    """How many steps of being depended on separate a declaration from the territory's root."""
    inside, d, frontier = set(ns), {root: 0}, [root]
    while frontier:
        nxt = []
        for m in frontier:
            for p in sorted(pred[m]):
                if p in inside and p not in d:
                    d[p] = d[m] + 1
                    nxt.append(p)
        frontier = nxt
    return d


comp_index = {}
for i, c in enumerate(sorted(nx.connected_components(G), key=lambda c: (-len(c), min(c)))):
    for n in sorted(c):
        comp_index[n] = i

pos = {}
for t in regions:
    ns = sorted(members[t])
    x, y, w, h = rects[t]
    mx, my = w * 0.09, h * 0.09
    ix, iy, iw, ih = x + mx, y + my, max(w - 2 * mx, 1e-9), max(h - 2 * my, 1e-9)
    # Order within a region is derived. A territory has a root, so its declarations are ordered by
    # dependency depth from that root, then by how much rests on them. The unrooted region has no root
    # to measure depth from, so its declarations are ordered by connected component instead.
    if t == "unrooted":
        order = sorted(ns, key=lambda n: (comp_index[n], -weight.get(n, 0), n))
    else:
        d = depth_from(t, ns)
        order = sorted(ns, key=lambda n: (d.get(n, 10 ** 6), -weight.get(n, 0), n))
    m = len(order)
    cols = max(1, round((m * (iw / ih)) ** 0.5))
    rows = -(-m // cols)
    for i, n in enumerate(order):
        r, c = divmod(i, cols)
        pos[n] = [ix + ((c + 0.5) / cols) * iw, iy + (1 - (r + 0.5) / rows) * ih]

out = {
    "layout": "territory-packed",
    "title": "Frozen positions, packed by territory, computed once and never reflowed.",
    "derivedFrom": ["spine", "labeling:territory", "labeling:load-bearing-weight"],
    "derivation": "Territories from the territory labeling, ordered by size then name, packed as a "
                  "squarified treemap of the unit square with area proportional to territory size. "
                  "Within a region the order is closed form and carries structure rather than an "
                  "embedding: declarations are sorted by dependency depth from that territory's root, "
                  "then by how much rests on them, then by name, and filled into a grid. The unrooted "
                  "region has no root to measure depth from, so its declarations are ordered by "
                  "connected component. No iterative embedding is used anywhere, so the result is "
                  "reproducible across processes. Center free: no region is central, no radius is used, "
                  "and distance from the middle carries no meaning. Declarations no root reaches form "
                  "the unrooted region, packed alongside the others rather than set apart.",
    "regions": {t: [round(v, 6) for v in rects[t]] for t in regions},
    "positions": {n: [round(pos[n][0], 6), round(pos[n][1], 6)] for n in nodes},
}
with open(os.path.join(GRAPH, "layout.json"), "w") as f:
    json.dump(out, f, indent=1, sort_keys=True)
    f.write("\n")
print(f"layout: {len(nodes)} positions across {len(regions)} territory regions, frozen")
