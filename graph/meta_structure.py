#!/usr/bin/env python3
"""Meta-structure render: the 19 roots and the two spines.

Regenerates the root-level meta-structure from graph/depgraph-proof.json (never
hand maintained) and emits graph/meta-structure.dot (+ .svg via dot) and a
Mermaid block on stdout for the README. All edges are computed, drawn as-is:
no hand-placed adjacency. Deterministic (Louvain seed=1).

Run from repo root:  python3 graph/meta_structure.py
"""
import json, subprocess, sys
from collections import defaultdict
import networkx as nx
import community as louvain

G = json.load(open('graph/depgraph-proof.json'))
N = {n['name']: n for n in G['nodes']}
S = lambda x: x.replace('Chiralogy.', '')
D = nx.DiGraph()
[D.add_node(n) for n in N]
for e in G['edges']:
    D.add_edge(e['source'], e['target'])
Drev = D.reverse(copy=True)
outdeg = dict(D.out_degree())
terr = lambda r: set(nx.descendants(Drev, r))            # who depends on r

# ---- ROOT SET: sinks with territory >= 10 ----
sinks = [n for n in N if outdeg[n] == 0]
roots = sorted([r for r in sinks if len(terr(r)) >= 10], key=lambda r: -len(terr(r)))
T = {r: terr(r) for r in roots}
short = {r: S(r) for r in roots}
by = lambda tok: next(r for r in roots if S(r) == tok)   # find root by short label

# ---- functional clusters (shared-territory Louvain, seed=1) ----
W = nx.Graph()
[W.add_node(r) for r in roots]
for i in range(len(roots)):
    for j in range(i + 1, len(roots)):
        s = len(T[roots[i]] & T[roots[j]])
        if s > 0:
            W.add_edge(roots[i], roots[j], weight=s)
part = louvain.best_partition(W, weight='weight', random_state=1)
comm = defaultdict(list)
[comm[part[r]].append(r) for r in roots]

def cluster_name(members):
    ms = {S(m) for m in members}
    if 'fixedPoint_of_surjection' in ms: return 'kernel-base'
    if 'Obj' in ms: return 'tower'
    if ms == {'agreementLE'}: return 'island'
    return 'application'

cname = {}
for members in comm.values():
    nm = cluster_name(members)
    for m in members:
        cname[m] = nm

# ---- the two spine systems ----
bridges = lambda n: [r for r in roots if n in T[r]]
spine = [n for n in N if len(bridges(n)) >= 3 and n not in roots]
def kind(n):
    s = n.lower()
    if any(k in s for k in ['chiasm', 'inversions', 'center', 'arms_invert', 'braid']): return 'chiasm'
    if any(k in s for k in ['register', 'physics', 'typesystem', 'conform', 'immun', 'cognition', 'chemistry', 'trust']): return 'register'
    return 'other'
chi = [n for n in spine if kind(n) == 'chiasm']
reg = [n for n in spine if kind(n) == 'register']
chiR = set(); [chiR.update(bridges(n)) for n in chi]
regR = set(); [regR.update(bridges(n)) for n in reg]
chiR &= set(roots); regR &= set(roots)
both = chiR & regR
chi_only = chiR - regR
reg_only = regR - chiR
federated = chiR | regR
isolates = [r for r in roots if r not in federated]

# ---- nestings (territory containment >= 0.7, smaller under bigger) ----
nest = []   # (child, parent, frac)
for a in roots:
    for b in roots:
        if a == b: continue
        frac = len(T[a] & T[b]) / len(T[a])
        if frac >= 0.7 and len(T[a]) < len(T[b]):
            nest.append((a, b, round(frac, 2)))

# ---- verification against the recorded meta-probe ----
print("VERIFY", file=sys.stderr)
print(f"  roots: {len(roots)}", file=sys.stderr)
print(f"  chi_only:  {sorted(S(r) for r in chi_only)}", file=sys.stderr)
print(f"  reg_only:  {sorted(S(r) for r in reg_only)}", file=sys.stderr)
print(f"  both:      {sorted(S(r) for r in both)}", file=sys.stderr)
print(f"  isolates:  {sorted(S(r) for r in isolates)}", file=sys.stderr)
print(f"  nestings:  {[(S(a),S(b),f) for a,b,f in nest]}", file=sys.stderr)

# ---- palette ----
CHI_COL, REG_COL = '#2266CC', '#DD7711'      # the two spines
NEST_COL = '#556070'                          # containment
TINT = {'kernel-base': '#E8EDF4', 'application': '#F5EEE6',
        'tower': '#E9F2E9', 'island': '#F1EAF2'}
child_of = {a for a, _, _ in nest}

def nid(r):
    return 'n_' + S(r).replace('.', '_').replace("'", '_')

def wsize(r):
    return round(0.42 + len(T[r]) * 0.021, 3)   # 10 -> 0.63, 69 -> 1.87 (area ~ territory)

def node_line(r):
    # circle sized by territory, number inside; name as an outside label so the
    # size channel stays proportional and the (sometimes long) name stays legible.
    style = 'filled,dashed' if r in isolates else 'filled'
    pen = '2.2' if r in isolates else '1.0'
    bcol = '#888888' if r in isolates else '#33383F'
    return (f'  {nid(r)} [label="{len(T[r])}", xlabel="{short[r]}", shape=circle, '
            f'fixedsize=true, width={wsize(r)}, style="{style}", '
            f'fillcolor="{TINT[cname[r]]}", color="{bcol}", penwidth={pen}, '
            f'fontsize=11, fontcolor="#222222"];')

# ---- emit DOT ----
L = []
L.append('digraph MetaStructure {')
L.append('  layout=fdp; bgcolor="white"; splines=true; overlap=false; forcelabels=true; K=1.05; sep="+10";')
L.append('  fontname="Helvetica"; node [fontname="Helvetica"]; edge [fontname="Helvetica"];')
L.append('  labelloc="t"; fontsize=13;')
L.append('  label="Chiralogy: 19 roots, two spines. Node size = territory; tint = functional cluster;\\n'
         'blue = self-description (chiasm) spine, orange = application (register) spine; '
         'the crossing = roots bridged by both;\\n'
         'diamond = contains (nesting); dashed = isolate, reached by neither spine.";')
# the two anchors
L.append(f'  SELFDESC [label="self-description\\nspine (chiasm)", shape=box, style="filled,rounded", '
         f'fillcolor="{CHI_COL}", fontcolor="white", penwidth=0, fontsize=12];')
L.append(f'  APPLIC  [label="application\\nspine (register)", shape=box, style="filled,rounded", '
         f'fillcolor="{REG_COL}", fontcolor="white", penwidth=0, fontsize=12];')

def sortT(rs): return sorted(rs, key=lambda r: -len(T[r]))
for r in roots:
    L.append(node_line(r))

# spine edges (computed): each root to the spine system(s) that bridge it.
# fdp pulls doubly-bridged roots (the crossing) between the two poles on its own.
for r in sortT(chiR):
    L.append(f'  {nid(r)} -> SELFDESC [color="{CHI_COL}", penwidth=1.6, arrowsize=0.7, dir=none];')
for r in sortT(regR):
    L.append(f'  {nid(r)} -> APPLIC [color="{REG_COL}", penwidth=1.6, arrowsize=0.7, dir=none];')

# nestings as containment (filled diamond at the container)
for a, b, f in nest:
    L.append(f'  {nid(b)} -> {nid(a)} [dir=back, arrowtail=diamond, arrowsize=1.1, '
             f'color="{NEST_COL}", penwidth=1.3, constraint=false, '
             f'label="contains", fontsize=8, fontcolor="{NEST_COL}"];')

# isolates as an outer archipelago
L.append('  subgraph cluster_iso {')
L.append('    label="isolates: reached by neither spine"; fontsize=11; fontcolor="#777777";')
L.append('    style="dashed,rounded"; color="#AAAAAA"; margin=12;')
for r in sortT(isolates):
    L.append(f'    {nid(r)};')
L.append('  }')

L.append('}')
open('graph/meta-structure.dot', 'w').write('\n'.join(L) + '\n')
# fdp (force-directed) render: like depgraph-proof.svg, the .dot is the deterministic
# source of truth (poles, edges, sizes all computed); the .svg is a force layout of it.
subprocess.run(['fdp', '-Tsvg', 'graph/meta-structure.dot', '-o', 'graph/meta-structure.svg'], check=True)
print("wrote graph/meta-structure.dot and graph/meta-structure.svg", file=sys.stderr)

# ---- emit Mermaid block for the README (stdout) ----
def mid(r): return 'r_' + S(r).replace('.', '_').replace("'", '_')
m = ['```mermaid', 'graph LR']
m.append(f'  CHI(["self-description spine<br/>chiasm"])')
m.append(f'  APP(["application spine<br/>register"])')
# nestings as containment subgraphs; others plain
nested_children = {a for a, _, _ in nest}
for a, b, f in nest:
    m.append(f'  subgraph {mid(b)}_box["{short[b]} {len(T[b])} contains {short[a]}"]')
    m.append(f'    {mid(b)}["{short[b]} {len(T[b])}"]')
    m.append(f'    {mid(a)}["{short[a]} {len(T[a])}"]')
    m.append(f'  end')
nest_parents = {b for _, b, _ in nest}
placed = nested_children | nest_parents | set(isolates)
for r in roots:
    if r in placed:
        continue
    m.append(f'  {mid(r)}["{short[r]} {len(T[r])}"]')
# isolates as their own archipelago box
m.append('  subgraph iso_box["isolates: reached by neither spine"]')
for r in sortT(isolates):
    m.append(f'    {mid(r)}["{short[r]} {len(T[r])}"]')
m.append('  end')
# spine edges, tracking indices for linkStyle coloring
edges = []
for r in sortT(chiR): edges.append((mid(r), 'CHI', 'chi'))
for r in sortT(regR): edges.append((mid(r), 'APP', 'reg'))
for i, (a, b, tag) in enumerate(edges):
    m.append(f'  {a} --- {b}')
# link styling
for i, (a, b, tag) in enumerate(edges):
    col = CHI_COL if tag == 'chi' else REG_COL
    m.append(f'  linkStyle {i} stroke:{col},stroke-width:2px')
# classes for anchors and isolates
m.append(f'  classDef spineC fill:{CHI_COL},color:#fff,stroke-width:0px')
m.append(f'  classDef spineA fill:{REG_COL},color:#fff,stroke-width:0px')
m.append(f'  classDef iso fill:#F1EAF2,stroke:#999,stroke-dasharray:4 3')
m.append('  class CHI spineC')
m.append('  class APP spineA')
if isolates:
    m.append('  class ' + ','.join(mid(r) for r in sortT(isolates)) + ' iso')
m.append('```')
print('\n'.join(m))
