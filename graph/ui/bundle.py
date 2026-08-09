#!/usr/bin/env python3
"""Bundle the fixed data and the authored config into one file the renderer can load.

A build product, nothing more: it copies graph/spine.json, graph/layout.json, every labeling and
graph/viewpoints.json into graph/ui/data.js as a single global, so the page opens from the filesystem
without a server. It adds nothing and decides nothing.

Deterministic: sorted keys, no timestamps.

Run from the repo root:  python3 graph/ui/bundle.py
"""
import glob, json, os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
GRAPH = os.path.join(ROOT, "graph")

labelings = {}
for p in sorted(glob.glob(os.path.join(GRAPH, "labelings", "*.json"))):
    d = json.load(open(p))
    labelings[d["labeling"]] = d

bundle = {
    "spine": json.load(open(os.path.join(GRAPH, "spine.json"))),
    "layout": json.load(open(os.path.join(GRAPH, "layout.json"))),
    "labelings": labelings,
    "viewpoints": json.load(open(os.path.join(GRAPH, "viewpoints.json"))),
}

out = os.path.join(GRAPH, "ui", "data.js")
with open(out, "w") as f:
    f.write("window.CHIRALOGY = ")
    json.dump(bundle, f, sort_keys=True, separators=(",", ":"))
    f.write(";\n")

print(f"bundle: {len(bundle['spine']['nodes'])} nodes, {len(bundle['spine']['edges'])} edges, "
      f"{len(labelings)} labelings, {len(bundle['viewpoints']['viewpoints'])} viewpoints")
