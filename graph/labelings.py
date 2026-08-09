#!/usr/bin/env python3
"""Derive the spine and its labelings from canonical. Nothing here is authored.

Reads graph/depgraph-proof.json, the extraction `lake exe depgraph-proof` produces from the compiled
environment, and a type dump it generates and runs itself. Emits graph/spine.json and one file per
labeling under graph/labelings/. Deterministic: every ordering sorted, no timestamps, no randomness.

Run from the repo root:  python3 graph/labelings.py
"""
import json, os, re, subprocess, sys
from collections import defaultdict, deque

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GRAPH = os.path.join(ROOT, "graph")
LAB = os.path.join(GRAPH, "labelings")
SRC = os.path.join(GRAPH, "depgraph-proof.json")


def emit(obj, path):
    with open(path, "w") as f:
        json.dump(obj, f, indent=1, sort_keys=True, ensure_ascii=False)
        f.write("\n")


def labeling(lid, title, derived_from, derivation, kind, rng, values, keyed="node"):
    return {
        "labeling": lid,
        "kind": keyed,
        "title": title,
        "derivedFrom": derived_from,
        "derivation": derivation,
        "attribute": {"kind": kind, "range": rng},
        "keyedBy": "canonical-name" if keyed == "node" else "canonical-name-pair",
        "values": values,
    }


# ---------------------------------------------------------------- the spine
G = json.load(open(SRC))
names = sorted(n["name"] for n in G["nodes"])
nodeset = set(names)
edges = sorted(
    {(e["source"], e["target"]) for e in G["edges"]
     if e["source"] in nodeset and e["target"] in nodeset}
)
os.makedirs(LAB, exist_ok=True)
emit({"nodes": names, "edges": [{"source": s, "target": t} for s, t in edges]},
     os.path.join(GRAPH, "spine.json"))

byname = {n["name"]: n for n in G["nodes"]}

# ------------------------------------------------- the type dump (for 3c/4b)
check = os.path.join(GRAPH, "types-check.lean")
with open(check, "w") as f:
    f.write("import Chiralogy\nset_option maxRecDepth 20000\n")
    for n in names:
        f.write(f"#check @{n}\n")
out = subprocess.run(["lake", "env", "lean", check], cwd=ROOT,
                     capture_output=True, text=True).stdout
entries, cur = [], None
for line in out.splitlines():
    if re.match(r"^@?[A-Za-z_]", line):
        if cur is not None:
            entries.append(cur)
        cur = line
    elif cur is not None:
        cur += " " + line.strip()
if cur is not None:
    entries.append(cur)
if len(entries) != len(names):
    sys.exit(f"type dump misaligned: {len(entries)} types for {len(names)} nodes")
types = {}
for n, e in zip(names, entries):
    if not e.lstrip("@").startswith(n):
        sys.exit(f"type dump misaligned at {n}")
    types[n] = e.split(" : ", 1)[1] if " : " in e else ""

# ----------------------------------------------- per declaration facts (Lean)
facts_out = subprocess.run(["lake", "env", "lean", os.path.join(GRAPH, "decl-facts.lean")],
                           cwd=ROOT, capture_output=True, text=True).stdout
typehash, proofhead, extdeps, extmod = {}, {}, {}, {}
for line in facts_out.splitlines():
    parts = line.split("\t")
    if parts[0] == "MODULE" and len(parts) == 3:
        extmod[parts[1]] = parts[2]
        continue
    if len(parts) != 4:
        continue
    nm, th, hd, ext = parts
    typehash[nm] = th
    proofhead[nm] = hd
    extdeps[nm] = sorted(x for x in ext.split(",") if x)
if not typehash:
    sys.exit("declaration facts empty")

# ------------------------------------------------------- 3a import stratum
emit(labeling(
    "import-stratum", "The layer of the framework a declaration lives in.",
    "canonical", "The stratum the extraction assigns from the declaring module's path.",
    "categorical", sorted({n["stratum"] for n in G["nodes"]}),
    {n: byname[n]["stratum"] for n in names}),
    os.path.join(LAB, "import-stratum.json"))

# --------------------------------------------------- 3b dependency topology
outdeg, indeg = defaultdict(int), defaultdict(int)
for s, t in edges:
    outdeg[s] += 1
    indeg[t] += 1
role = {}
for n in names:
    if byname[n].get("isRoot"):
        role[n] = "root"
    elif outdeg[n] == 0:
        role[n] = "base"
    elif indeg[n] == 0:
        role[n] = "leaf"
    else:
        role[n] = "interior"
emit(labeling(
    "dependency-topology", "The node's role in the proof dependency graph.",
    "canonical",
    "Root as the extraction marks it; otherwise base when nothing is depended on, "
    "leaf when nothing depends on it, interior when both.",
    "categorical", ["root", "base", "leaf", "interior"], role),
    os.path.join(LAB, "dependency-topology.json"))

# ------------------------------------------------------- 3c conditionality
# A statement is CONDITIONAL when it names a concrete instance: a carrier at a numeral, or a named
# object of the register layer. Otherwise every carrier in it is universally quantified and it is
# UNCONDITIONAL. The value space Option Bool is masked first: it is a value space, not a carrier.
CONCRETE = re.compile(r"Fin\s+\d|\bimprecise\b|Physics\.|TypeSystem\.|GroundStructures\.|\bcfamS\b")
cond = {}
for n in names:
    probe = types[n].replace("Option Bool", "OPTB")
    cond[n] = "conditional" if CONCRETE.search(probe) else "unconditional"
emit(labeling(
    "conditionality", "Whether the statement is quantified over all carriers or names a concrete one.",
    "canonical",
    "The printed type is searched for a concrete instance: a carrier at a numeral, or a named object of "
    "the register layer. The value space Option Bool is masked first.",
    "categorical", ["unconditional", "conditional"], cond),
    os.path.join(LAB, "conditionality.json"))

# ------------------------------------------------- 4a load bearing weight
rev = defaultdict(list)
for s, t in edges:
    rev[t].append(s)
weight = {}
for n in names:
    seen, stack = set(), list(rev[n])
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(rev[m])
    weight[n] = len(seen)
emit(labeling(
    "load-bearing-weight", "How many declarations depend on this one, directly or through others.",
    "canonical", "Transitive closure of the reversed edge set of the spine.",
    "scalar", {"min": min(weight.values()), "max": max(weight.values())}, weight),
    os.path.join(LAB, "load-bearing-weight.json"))

# ------------------------------- 5 satisfaction family, one labeling per register
# A node is LIT under a register when nothing in its statement ties it to a different one: either it is
# unconditional, or the concrete instance it names is this register's.
REGISTERS = {
    "physics": ("Chiralogy.Registers.Physics", re.compile(r"\bimprecise\b|Physics\.")),
    "type-system": ("Chiralogy.Registers.TypeSystem", re.compile(r"TypeSystem\.")),
}
regmods = {m for m, _ in REGISTERS.values()}
sat_ids = []
for reg, (mod, pat) in sorted(REGISTERS.items()):
    others = [p for r, (_, p) in sorted(REGISTERS.items()) if r != reg]
    vals = {}
    for n in names:
        home = byname[n]["module"]
        if home in regmods:
            # a declaration of a register layer belongs to that register and to no other
            vals[n] = home == mod
        elif cond[n] == "unconditional":
            vals[n] = True
        elif pat.search(types[n]):
            vals[n] = True
        else:
            vals[n] = False
    lid = f"satisfaction-{reg}"
    sat_ids.append(lid)
    emit(labeling(
        lid, f"Whether the declaration lights up for the {reg} register.",
        ["labeling:conditionality"],
        "A declaration of a register layer belongs to that register alone. Otherwise an unconditional "
        "declaration lights for every register, and a conditional one lights only for the register whose "
        "objects its statement names.",
        "boolean", None, vals),
        os.path.join(LAB, f"{lid}.json"))

# ------------------------------------------- 4b invariance under instantiation
# A REDUCTION over labelings, not an extraction from canonical. Three valued on purpose, so that a
# finite register sample can never be mistaken for the unconditional core.
inv = {}
sat = {i: json.load(open(os.path.join(LAB, f"{i}.json")))["values"] for i in sat_ids}
for n in names:
    lit_everywhere = all(sat[i][n] for i in sat_ids)
    if not lit_everywhere:
        inv[n] = "varies"
    elif cond[n] == "unconditional":
        inv[n] = "unconditional"
    else:
        inv[n] = "invariant-across-sample"
emit(labeling(
    "invariance-under-instantiation",
    "Whether the declaration survives instantiation at every register, and on what grounds.",
    ["labeling:conditionality"] + [f"labeling:{i}" for i in sat_ids],
    "Invariance is decided by the family: lit under every satisfaction labeling. The quantifier records only "
    "the GROUNDS, unconditional when the statement also names no concrete carrier, invariant-across-sample "
    "when it does. The two are kept apart so a finite register sample is never read as the unconditional core.",
    "categorical", ["unconditional", "invariant-across-sample", "varies"], inv),
    os.path.join(LAB, "invariance-under-instantiation.json"))

# --------------------------------------------- A2 edge provenance and derivation
edgekind = {}
for e in G["edges"]:
    if e["source"] in nodeset and e["target"] in nodeset:
        edgekind[f"{e['source']}|{e['target']}"] = (
            "proof-only" if e["kind"] == "proofOnly" else "statement")
emit(labeling(
    "edge-provenance", "Whether the dependency shows in the target's statement or only in its proof.",
    "canonical",
    "The extraction marks an edge proofOnly when the dependency is absent from the statement and present "
    "in the proof term; statement otherwise.",
    "categorical", ["statement", "proof-only"], edgekind, keyed="edge"),
    os.path.join(LAB, "edge-provenance.json"))

deriv = {}
for s_, t_ in edges:
    if proofhead.get(s_) == t_:
        deriv[f"{s_}|{t_}"] = ("restatement" if typehash.get(s_) == typehash.get(t_)
                               else "specialisation")
    else:
        deriv[f"{s_}|{t_}"] = "derived"
emit(labeling(
    "edge-derivation", "How the source stands to the target it depends on.",
    "canonical",
    "Restatement when the source's proof is headed by the target and the two types have the same "
    "structural hash, so they state one proposition; specialisation when the proof is headed by the target "
    "and the types differ, so the source is one application of it; derived otherwise.",
    "categorical", ["restatement", "specialisation", "derived"], deriv, keyed="edge"),
    os.path.join(LAB, "edge-derivation.json"))

# ------------------------------------------------ territory, by root reachability
# The decomposition the graph findings already use: a ROOT is a sink whose territory reaches at least
# ten declarations, and the territory of a root is everything that depends on it, transitively. A node
# lies in as many territories as there are roots reaching it, so for a single valued labeling one is
# chosen: the nearest root by dependency distance, then the smaller territory, then the least name.
succ = defaultdict(list)
pred = defaultdict(list)
for s_, t_ in edges:
    succ[s_].append(t_)
    pred[t_].append(s_)
sinks = [n for n in names if not succ[n]]


def reach_up(r):
    seen, q = set(), deque([r])
    while q:
        m = q.popleft()
        for p in pred[m]:
            if p not in seen:
                seen.add(p)
                q.append(p)
    return seen


terr = {r: reach_up(r) for r in sinks}
troots = sorted((r for r in sinks if len(terr[r]) >= 10), key=lambda r: (-len(terr[r]), r))
dist = {}
for r in troots:
    d, q = {r: 0}, deque([r])
    while q:
        m = q.popleft()
        for p in pred[m]:
            if p not in d:
                d[p] = d[m] + 1
                q.append(p)
    dist[r] = d
holders = defaultdict(list)
for r in troots:
    for n in terr[r]:
        holders[n].append(r)
territory, sharing = {}, {}
for n in names:
    hs = holders.get(n, [])
    if not hs:
        territory[n] = "unrooted"
        sharing[n] = "unrooted"
    else:
        territory[n] = min(hs, key=lambda r: (dist[r].get(n, 10 ** 6), len(terr[r]), r))
        sharing[n] = "private" if len(hs) == 1 else "shared"
for r in troots:
    territory[r] = r
    sharing.setdefault(r, "private")
emit(labeling(
    "territory", "The root territory a declaration is placed in.",
    "canonical",
    "A root is a sink whose territory reaches at least ten declarations; its territory is everything "
    "depending on it transitively. Where several roots reach a declaration, the nearest by dependency "
    "distance is chosen, then the smaller territory, then the least name. Declarations no root reaches "
    "are unrooted.",
    "categorical", sorted(set(territory.values())), territory),
    os.path.join(LAB, "territory.json"))
emit(labeling(
    "territory-sharing", "Whether a declaration lies in one territory, several, or none.",
    "canonical",
    "Private when exactly one root reaches it, shared when more than one, unrooted when none.",
    "categorical", ["private", "shared", "unrooted"], sharing),
    os.path.join(LAB, "territory-sharing.json"))

# ------------------------------------- B substrate check, one level below canonical
# A substrate PARENT is a library result. A core primitive, a type former or an elimination rule from
# Lean's own prelude, is not an ancestor in any structural sense: everything mentions it.
def mathlib_parents(n):
    return sorted(d for d in extdeps.get(n, []) if extmod.get(d, "").startswith("Mathlib"))

roots = sorted(n for n in names if byname[n].get("isRoot"))
shared = defaultdict(set)
for r in roots:
    for d in mathlib_parents(r):
        shared[d].add(r)
prov = {}
for r in roots:
    partners = sorted({q for d in mathlib_parents(r) for q in shared[d] if q != r})
    prov[r] = partners
emit({"diagnostic": "root-provenance",
      "title": "Whether a canonical root stays independent when one level of substrate is shown.",
      "derivedFrom": "canonical",
      "derivation": "For each root, the library results it uses directly, one substrate level only, and "
                    "the other roots sharing any of them. Constants from Lean's own prelude are excluded: "
                    "a type former is not an ancestor, since everything mentions it.",
      "keyedBy": "canonical-name",
      "roots": len(roots),
      "mathlibParents": {r: mathlib_parents(r) for r in roots},
      "allExternalParents": {r: extdeps.get(r, []) for r in roots},
      "sharesWith": prov},
     os.path.join(GRAPH, "root-provenance.json"))

os.remove(check)
print(f"spine: {len(names)} nodes, {len(edges)} edges")
for f in sorted(os.listdir(LAB)):
    d = json.load(open(os.path.join(LAB, f)))
    print(f"  {d['labeling']:34s} {d['attribute']['kind']:12s} {len(d['values'])} values")
