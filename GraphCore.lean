import Lean
import Chiralogy

/-! # Dependency graph extraction core (v0.5)

Shared logic for the `depgraph` (canonical spine) and `depgraph-preview` (canonical plus one
experiment, marked un-graduated) targets. Reads the environment, adds nothing to it. No dashes.
-/

open Lean

namespace GraphCore

def containsSub (s t : String) : Bool := (s.splitOn t).length > 1

def lastComp : Name → String
  | .str _ s => s
  | _ => ""

/-- Generated declarations identified by an exact final component. -/
def genExactSuffix : List String :=
  ["mk", "rec", "recOn", "recAux", "casesOn", "below", "ibelow", "brecOn", "brecOnₓ",
   "binductionOn", "ind", "inj", "injEq", "ext", "ext_iff", "elim", "ctorElim",
   "ctorIdx", "toCtorIdx", "fromCtorIdx", "noConfusion", "noConfusionType", "sizeOf",
   "eq_def", "fwd", "ofNat"]

/-- Generated declarations identified by a substring inside the final component. -/
def genInComp : List String :=
  ["match_", "proof_", "eq_", "ctorIdx", "enumList", "getElem?", "sizeOf",
   "brecOn", "noConfusion", "_sunfold", "_cstage", "_elam", "_lam"]

/-- Strong markers that never occur in an authored name, safe to match anywhere. -/
def strongMarkers : List String :=
  ["brecOn", "match_", "proof_", "noConfusion", "sizeOf", "casesOn", "binductionOn"]

def isGenerated (n : Name) : Bool :=
  n.isInternalDetail
  || strongMarkers.any (containsSub n.toString)
  || genExactSuffix.contains (lastComp n)
  || genInComp.any (containsSub (lastComp n))

def underChiralogy (n : Name) : Bool := (`Chiralogy).isPrefixOf n

def stratumOf (mod : Name) : String :=
  let s := mod.toString
  if containsSub s "Kernel" then "kernel"
  else if containsSub s "Protocol" then "protocol"
  else if containsSub s "Experiments" && containsSub s "archive" then "archive"
  else if containsSub s "Experiments" then "experiment"
  else if containsSub s "Registers" then "register"
  else if containsSub s "Model" then "model"
  else "core"

def moduleNameOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => Name.anonymous

partial def stripForall : Expr → Expr
  | .forallE _ _ b _ => stripForall b
  | e => e

def isInstanceType (env : Environment) (t : Expr) : Bool :=
  match (stripForall t).getAppFn.constName? with
  | some c => isClass env c
  | none => false

/-- Declaration kind for the node marker: theorem, def, abbrev, structure, inductive, instance, axiom. -/
def kindOf (env : Environment) (n : Name) : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .inductInfo _ => if isStructure env n then "structure" else "inductive"
  | .defnInfo v =>
      if isInstanceType env v.type then "instance"
      else match v.hints with
        | .abbrev => "abbrev"
        | _ => "def"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-! ## Derived semantic properties: modality and axis (v1)

Both computed from the declaration's type structure and dependencies, re-computed every run, never
asserted. Modality applies to theorems and axioms; other kinds are `na` by kind. -/

partial def stripForallResult : Expr → Expr
  | .forallE _ _ b _ => stripForallResult b
  | e => e

def sortIsProp : Expr → Bool
  | .sort .zero => true
  | _ => false

/-- Whether an expression is a proposition, judged structurally: a Pi ending in `Prop`, or an
application whose head constant returns `Prop`. No whnf, so folded `Not`/`Ne` read as their heads. -/
partial def resultIsProp (env : Environment) : Expr → Bool
  | .forallE _ _ b _ => resultIsProp env b
  | .sort _ => false
  | e =>
    match e.getAppFn with
    | .const c _ => match env.find? c with
        | some ci => sortIsProp (stripForallResult ci.type)
        | none => false
    | _ => false

/-- Walk the forall telescope. Returns the count of failable propositional antecedents (non
dependent, propositional domain, ordinary hypothesis or instance) and, separately, how many of
those are instance binders. A propositional instance class (e.g. `Subsingleton _`,
`IsLeftAdjoint _`) is a failable constraint on the carrier, not ambient object structure; the
ambient object-structure classes (`DecidableEq`, `Category`) are `Type` valued, so their domains
are not propositions and are excluded here by construction. -/
partial def scanBinders (env : Environment) : Expr → Nat × Nat
  | .forallE _ dom body bi =>
      let (n, p) := scanBinders env body
      let failable := resultIsProp env dom && !body.hasLooseBVar 0
      let inst := bi == BinderInfo.instImplicit
      (n + (if failable then 1 else 0), p + (if failable && inst then 1 else 0))
  | _ => (0, 0)

partial def telescopeBody : Expr → Expr
  | .forallE _ _ b _ => telescopeBody b
  | e => e

/-- A statement whose telescope conclusion is `False` is a negation `H₁ → ... → Hₙ → False`, a
forced impossibility, not a caller supplied conditional. -/
def bodyIsFalse (t : Expr) : Bool := (telescopeBody t).isConstOf `False

/-- Modality: `forced` if the statement is a negation or carries no failable propositional
antecedent, `conditional` if it carries a real one. Only theorem and axiom kinds; else `na`. -/
def modalityOf (env : Environment) (kind : String) (ci : ConstantInfo) : String :=
  if kind == "theorem" || kind == "axiom" then
    if bodyIsFalse ci.type then "forced"
    else if (scanBinders env ci.type).1 > 0 then "conditional" else "forced"
  else "na"

/-- The constants used for the axis judgment: a theorem or axiom is judged by what it states (its
type); a def is judged by what it constructs (type and value). -/
def axisConsts (ci : ConstantInfo) : Array Name :=
  match ci with
  | .defnInfo _ => ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
  | _ => ci.type.getUsedConstants

/-- Axis (four values). `inter-cross`: the assemblage sense, the assemblage primitive or a product
carrier that is not an object (the between-two-classifications cross-region). `inter-categorical`:
the tower sense, a relation between objects via morphisms (`Hom`/`Obj`) without the assemblage.
`intra`: a single classifier (`Option Bool` value space, reflexive `Equiv`, or `NonDegenerate`).
`na`: no classification carrier. A node carrying both senses lands `inter-cross` and is reported. -/
def axisOf (ci : ConstantInfo) : String :=
  let uc := axisConsts ci
  let hasAssemble := uc.contains `Chiralogy.assembleClassify
  let hasProd := uc.contains `Prod
  let hasObj := uc.contains `Chiralogy.Obj
  let hasHom := uc.contains `Chiralogy.Hom
  let crossSense := hasAssemble || (hasProd && !hasObj && !hasHom)
  let catSense := (hasHom || hasObj) && !hasAssemble
  let classif := uc.contains `Bool || uc.contains `Equiv || uc.contains `Chiralogy.NonDegenerate
  if crossSense then "inter-cross"
  else if catSense then "inter-categorical"
  else if classif then "intra"
  else "na"

/-- The declaration's defining term, INCLUDING theorem proofs. `ConstantInfo.value?` excludes
theorems by design (proofs are irrelevant for unfolding), so proof-level extraction needs this.
`importModules` does carry the proofs; only the accessor differs. -/
def declValue : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- A node carrying both the assemblage and the categorical senses. -/
def axisBothSenses (ci : ConstantInfo) : Bool :=
  let uc := axisConsts ci
  uc.contains `Chiralogy.assembleClassify && (uc.contains `Chiralogy.Hom || uc.contains `Chiralogy.Obj)

/-- Kept kinds: source level declarations the author wrote, now including authored axioms. -/
def keepKind : ConstantInfo → Bool
  | .thmInfo _ | .defnInfo _ | .inductInfo _ | .axiomInfo _ => true
  | _ => false

/-- Reason a Chiralogy declaration is dropped, `none` if kept. -/
def dropReason (env : Environment) (n : Name) (ci : ConstantInfo) : Option String :=
  if isGenerated n then some "generated"
  else if (env.getProjectionFnInfo? n).isSome then some "projection"
  else match ci with
    | .thmInfo _ | .defnInfo _ | .inductInfo _ | .axiomInfo _ => none
    | .ctorInfo _ => some "constructor"
    | .recInfo _ => some "recursor"
    | .opaqueInfo _ => some "opaque"
    | .quotInfo _ => some "quot"

/-- Resolve a used constant to a kept node. Kept names map to themselves; a dropped projection
or constructor re-points to its parent structure/inductive when that parent is kept; anything
else is dropped. -/
def resolveDep (env : Environment) (keptSet : NameSet) (n d : Name) : Option Name :=
  if d == n then none
  else if keptSet.contains d then some d
  else if underChiralogy d
      && ((env.getProjectionFnInfo? d).isSome
          || (match env.find? d with | some (.ctorInfo _) => true | _ => false)) then
    let p := d.getPrefix
    if keptSet.contains p then some p else none
  else none

def nameLt (a b : Name) : Bool := a.toString < b.toString

def edgeLt (a b : Name × Name) : Bool :=
  if a.1 == b.1 then nameLt a.2 b.2 else nameLt a.1 b.1

def quote (n : Name) : String := "\"" ++ n.toString ++ "\""

def strataOrder : List String :=
  ["kernel", "protocol", "model", "register", "experiment", "archive", "core"]

/-- Emission order top to bottom: register at top, model, protocol lateral, kernel at bottom. The
dependency edges enforce the vertical ordering; this only fixes cluster emission order. -/
def strataRenderOrder : List String :=
  ["register", "model", "protocol", "kernel", "experiment", "archive", "core"]

def axisOrder : List String := ["inter-cross", "inter-categorical", "intra", "na"]

/-- Color encodes modality (Paul Tol, accessible in grayscale and for colour vision deficiency):
forced blue, conditional orange, na light grey (recedes). -/
def modalityColor : String → String
  | "forced" => "#4477AA"
  | "conditional" => "#EE7733"
  | _ => "#DDDDDD"

def modalityFont : String → String
  | "forced" => "white"
  | _ => "black"

/-- Shape encodes kind, subordinate to colour: axioms diamonds (visible), theorems ellipses,
everything else a box. -/
def kindShape : String → String
  | "axiom" => "diamond"
  | "theorem" => "ellipse"
  | _ => "box"

def sanitize (s : String) : String := (s.replace "-" "_")

/-- A DOT attribute list for a node: colour by modality, shape by kind, dashed if un-graduated. -/
def nodeAttrs (kind modality stratum : String) : String :=
  let style := if stratum == "experiment" || stratum == "archive" then "\"filled,dashed\"" else "filled"
  " [shape=" ++ kindShape kind ++ ", fillcolor=\"" ++ modalityColor modality
    ++ "\", fontcolor=" ++ modalityFont modality ++ ", style=" ++ style ++ "]"

/-- The apophatic/cataphatic hand of a node, from its module (the measured structural axis, community
purity 0.82). Apophatic covers the hole and the empty center; cataphatic the free constructions. -/
def characterOf (mod : Name) : String :=
  let s := mod.toString
  if containsSub s "Apophatic" then "apophatic"
  else if containsSub s "Cataphatic" then "cataphatic"
  else if s.endsWith ".Center" then "apophatic"
  else if containsSub s "Boundary" then "seam"
  else "neutral"

/-- Colour encodes character (the two hands): apophatic blue (the larger hand), cataphatic orange,
neutral scaffolding grey, seam purple. -/
def charColor : String → String
  | "apophatic" => "#4477AA"
  | "cataphatic" => "#EE7733"
  | "seam" => "#AA4499"
  | _ => "#CCCCCC"

/-- The structural base: the two kernel absences and the diagonal-argument taproot, pinned low. -/
def baseNodes : List Name :=
  [`Chiralogy.fixedPoint_of_surjection, `Chiralogy.no_reflexive_object, `Chiralogy.hole_uniform]

def taproot : Name := `Chiralogy.fixedPoint_of_surjection

/-- The peripheral empty center, pinned far from the base. -/
def peripheralCenter : Name := `Chiralogy.center_is_empty

/-- Reverse reachability: all nodes that transitively depend on the frontier, via the predecessor
map. Used to compute a root's territory (everything that depends on it). -/
partial def revReach (predMap : NameMap (Array Name)) : Array Name → NameSet → NameSet
  | frontier, visited =>
    if frontier.isEmpty then visited
    else
      let step := frontier.foldl (fun (acc : Array Name × NameSet) n =>
        ((predMap.find? n).getD #[]).foldl (fun (a : Array Name × NameSet) p =>
          if a.2.contains p then a else (a.1.push p, a.2.insert p)) acc) ((#[] : Array Name), visited)
      revReach predMap step.1 step.2

/-- A categorical palette so each of the ~19 roots' territories reads as a distinct tint (the
forest-of-territories default view). Cycled by root index. -/
def rhizomePalette : Array String :=
  #["#4477AA", "#EE7733", "#228833", "#AA4499", "#CCBB44", "#66CCEE", "#EE6677", "#997700",
    "#BBBBBB", "#0077BB", "#EE3377", "#009988", "#CC6677", "#88CCEE", "#DDCC77", "#117733",
    "#882255", "#44AA99", "#999933", "#AA4466"]

def rhizomeColor (i : Nat) : String := rhizomePalette[i % rhizomePalette.size]!

/-- Extract the graph from `env` over the imported modules, emit `{outBase}.dot` and
`{outBase}.json`, and print a report. -/
def run (imports : Array Name) (outBase : String)
    (proofLevel : Bool := false) (emitData : Bool := true) (renderSvg : Bool := true)
    (selfImage : Bool := false) (charColorMode : Bool := false) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules (imports.map (fun m => { module := m })) {} (trustLevel := 1024)
  -- Pass 1: classify Chiralogy constants.
  let mut kept : Array (Name × ConstantInfo) := #[]
  let mut dropCounts : Std.HashMap String Nat := {}
  let mut dropExamples : Std.HashMap String Name := {}
  for (n, ci) in env.constants.toList do
    if underChiralogy n then
      match dropReason env n ci with
      | none => kept := kept.push (n, ci)
      | some r =>
        dropCounts := dropCounts.insert r ((dropCounts.getD r 0) + 1)
        if !dropExamples.contains r then dropExamples := dropExamples.insert r n
  let keptSet : NameSet := kept.foldl (fun s (n, _) => s.insert n) {}
  let mut stratMap : NameMap String := {}
  let mut modMap : NameMap Name := {}
  let mut kindMap : NameMap String := {}
  let mut charMap : NameMap String := {}
  let mut modalityMap : NameMap String := {}
  let mut axisMap : NameMap String := {}
  let mut propInstNodes : Array Name := #[]
  let mut bothSenses : Array Name := #[]
  for (n, ci) in kept do
    let k := kindOf env n ci
    stratMap := stratMap.insert n (stratumOf (moduleNameOf env n))
    modMap := modMap.insert n (moduleNameOf env n)
    kindMap := kindMap.insert n k
    charMap := charMap.insert n (characterOf (moduleNameOf env n))
    modalityMap := modalityMap.insert n (modalityOf env k ci)
    axisMap := axisMap.insert n (axisOf ci)
    if (k == "theorem" || k == "axiom") && (scanBinders env ci.type).2 > 0 then
      propInstNodes := propInstNodes.push n
    if axisBothSenses ci then
      bothSenses := bothSenses.push n
  -- Pass 2: edges, re-pointed and filtered to kept targets, deduped, no self loops. Each edge is
  -- tagged proof-only when the dependency is in the proof term but not the statement type (an
  -- implicit dependency the statement does not declare).
  let resolveInto := fun (used : Array Name) (n : Name) => used.foldl
    (fun s d => match resolveDep env keptSet n d with | some t => s.insert t | none => s) (NameSet.empty)
  let mut edges : Array (Name × Name × Bool) := #[]
  for (n, ci) in kept do
    let val := if proofLevel then declValue ci else ci.value?
    let typeDeps : NameSet := resolveInto ci.type.getUsedConstants n
    let allDeps : NameSet := resolveInto (ci.type.getUsedConstants ++ (val.map (·.getUsedConstants)).getD #[]) n
    -- proof-only (implicit) is a THEOREM whose proof uses a dependency its statement type omits; a
    -- def's body deps are the definition's declared content, not implicit.
    let isThm := (kindMap.find? n).getD "" == "theorem"
    for d in allDeps.toList do
      edges := edges.push (n, d, isThm && !typeDeps.contains d)
  let nodes := (kept.map (·.1)).qsort nameLt
  edges := edges.qsort (fun a b => if a.1 == b.1 then nameLt a.2.1 b.2.1 else nameLt a.1 b.1)
  -- Multi-center analysis: reverse adjacency, out-degree, then each pure sink's territory (everything
  -- that depends on it). Roots are sinks with territory >= 10 (the natural cutoff the probe found).
  -- Each node's home root is the smallest territory containing it; shared count is how many roots
  -- reach it (the >= 3 nodes are the lateral spine). This is the acentric forest, computed from edges.
  let mut predMap : NameMap (Array Name) := {}
  let mut outCnt : NameMap Nat := {}
  for (s, t, _) in edges do
    predMap := predMap.insert t (((predMap.find? t).getD #[]).push s)
    outCnt := outCnt.insert s (((outCnt.find? s).getD 0) + 1)
  let sinks := nodes.filter (fun n => ((outCnt.find? n).getD 0) == 0)
  let rootTerr := (sinks.filterMap (fun s =>
    let terr := revReach predMap #[s] {}
    if terr.size ≥ 10 then some (s, terr) else none)).qsort (fun a b => a.2.size > b.2.size)
  let mut rootIndex : NameMap Nat := {}
  for i in [0:rootTerr.size] do rootIndex := rootIndex.insert (rootTerr[i]!).1 i
  let mut rootMap : NameMap Name := {}        -- home root of each node (smallest territory wins)
  let mut sharedMap : NameMap Nat := {}       -- how many territories reach it
  -- rootTerr is sorted by territory size descending, so iterating in order and overwriting means
  -- the last (smallest) territory containing a node becomes its home: the most specific tree.
  for (r, terr) in rootTerr do
    rootMap := rootMap.insert r r
    for n in terr.toList do
      sharedMap := sharedMap.insert n (((sharedMap.find? n).getD 0) + 1)
      rootMap := rootMap.insert n r
  let rootLabel := fun (n : Name) =>
    match rootMap.find? n with
    | some r => r.toString.replace "Chiralogy." ""
    | none => "unrooted"
  let isSpine := fun (n : Name) => ((sharedMap.find? n).getD 0) ≥ 3
  let isRoot := fun (n : Name) => (rootIndex.find? n).isSome
  let mut dot : Array String := #[]
  if selfImage then
    -- The self-image: the MEASURED shape. Base (two absences + diagonal taproot) pinned low,
    -- colour = character (the two hands, apophatic the larger), the empty center pinned peripheral.
    -- The acentric rhizome: the multi-center probe found a forest of ~19 roots (sinks with
    -- territory >= 10), each a co-equal growth point, laterally stitched by a thin shared spine
    -- (nodes in >= 3 territories: the chiasm statements and register instances). No single base,
    -- no pins; force-directed scatter so no root is the origin.
    let sname := fun (n : Name) => n.toString.replace "Chiralogy." ""
    let hdr := "Chiralogy self-image (proof-level, acentric rhizome). Regenerated by `lake exe depgraph-proof`."
      ++ "\\lThe measured shape: a forest of ~19 co-equal roots (labelled growth points, each a distinct"
      ++ " territory tint), not one base. The absences are the largest territory but one among many, not"
      ++ " central. Gold boxes and edges = the lateral spine (chiasm statements and register instances) that"
      ++ " threads the otherwise disjoint trees. Red dashed = proof-only (implicit). Modular by repetition,"
      ++ " not fractal, not centred.\\l"
    dot := #[
      "digraph SelfImage {", "  overlap=prism; splines=true; outputorder=edgesfirst; sep=\"+6\";",
      "  graph [fontname=\"Helvetica\", labelloc=t, label=\"" ++ hdr ++ "\"];",
      "  node [style=filled, fontname=\"Helvetica\", fontsize=6, penwidth=0.3, shape=ellipse];",
      "  edge [arrowsize=0.3];",
      "  subgraph cluster_legend {", "    label=\"legend\"; fontsize=16; style=rounded; color=\"#888888\";",
      "    \"L_root\" [label=\"a root (growth point); absences largest\", shape=ellipse, fillcolor=\"#4477AA\", fontcolor=white, penwidth=1.8, color=\"#222222\"];",
      "    \"L_terr\" [label=\"each colour = one root territory (~19)\", shape=plaintext];",
      "    \"L_spine\" [label=\"gold = lateral spine (chiasm + registers)\", shape=box, fillcolor=\"#CCBB44\", penwidth=3, color=\"#886600\"];",
      "    \"L_proof\" [label=\"red dashed edge = proof-only (implicit)\", shape=plaintext, fontcolor=\"#CC3311\"];",
      "    \"L_root\" -> \"L_spine\" [style=invis];", "  }"]
    let nodeLine := fun (n : Name) (tint : String) (isR : Bool) (sp : Bool) =>
      if sp then
        "    " ++ quote n ++ " [shape=box, fillcolor=\"" ++ tint ++ "\", penwidth=3, color=\"#886600\", fontsize=8, label=\"" ++ sname n ++ "\"];"
      else if isR then
        let sz := if baseNodes.contains n then "16" else "12"
        "    " ++ quote n ++ " [shape=ellipse, fillcolor=\"" ++ tint ++ "\", penwidth=1.8, color=\"#222222\", fontsize=" ++ sz ++ ", label=\"" ++ sname n ++ "\"];"
      else
        "    " ++ quote n ++ " [shape=point, width=0.07, color=\"" ++ tint ++ "\"];"
    for i in [0:rootTerr.size] do
      let r := (rootTerr[i]!).1
      let tsize := (rootTerr[i]!).2.size
      let tint := rhizomeColor i
      let members := nodes.filter (fun n => rootMap.find? n == some r)
      dot := dot.push ("  subgraph cluster_root" ++ toString i ++ " { label=\"" ++ sname r ++ " ("
        ++ toString tsize ++ ")\"; color=\"" ++ tint ++ "\"; style=rounded; fontsize=13;")
      for n in members do dot := dot.push (nodeLine n tint (n == r) (isSpine n))
      dot := dot.push "  }"
    -- uncovered nodes (in no root territory): loose grey scatter
    for n in nodes.filter (fun n => (rootMap.find? n).isNone) do
      dot := dot.push (nodeLine n "#DDDDDD" false (isSpine n))
    for (s, t, po) in edges do
      let attr := if isSpine s || isSpine t then "color=\"#997700\", penwidth=0.9"
        else if po then "color=\"#CC3311\", style=dashed, penwidth=0.4"
        else "color=\"#E4E4E4\", penwidth=0.25"
      dot := dot.push ("  " ++ quote s ++ " -> " ++ quote t ++ " [" ++ attr ++ "];")
    dot := dot.push "}"
  else
    -- The statement-level data DOT (colour = modality, cluster = stratum then axis). Data source
    -- for the interactive viewer; the retired probe SVG is no longer rendered from it.
    let hdr := "Chiralogy dependency graph. Regenerated by `lake exe depgraph`, do not edit."
      ++ "\\lColour = modality (blue forced, orange conditional, grey na). Shape = kind (diamond axiom,"
      ++ " ellipse theorem, box def/structure). Cluster = stratum then axis.\\l"
    dot := #[
      "digraph Chiralogy {", "  rankdir=TB;", "  compound=true;", "  newrank=true;",
      "  graph [fontname=\"Helvetica\", labelloc=t, label=\"" ++ hdr ++ "\"];",
      "  node [style=filled, fontname=\"Helvetica\", fontsize=9, penwidth=0.6];",
      "  edge [arrowsize=0.5];"]
    for strat in strataRenderOrder do
      let sn := nodes.filter (fun n => stratMap.find? n == some strat)
      if sn.size > 0 then
        dot := dot.push ("  subgraph cluster_" ++ strat ++ " {")
        dot := dot.push ("    label=\"" ++ strat ++ "\"; style=rounded; color=\"#888888\"; fontsize=16;")
        for ax in axisOrder do
          let an := sn.filter (fun n => axisMap.find? n == some ax)
          if an.size > 0 then
            dot := dot.push ("    subgraph cluster_" ++ strat ++ "_" ++ sanitize ax ++ " {")
            dot := dot.push ("      label=\"" ++ ax ++ "\"; style=dashed; color=\"#CCCCCC\"; fontsize=11;")
            for n in an do
              let k := (kindMap.find? n).getD "def"
              if charColorMode then
                let c := (charMap.find? n).getD "neutral"
                let fc := if c == "cataphatic" || c == "neutral" then "black" else "white"
                dot := dot.push ("      " ++ quote n ++ " [shape=" ++ kindShape k ++ ", fillcolor=\""
                  ++ charColor c ++ "\", fontcolor=" ++ fc ++ ", style=filled];")
              else
                let md := (modalityMap.find? n).getD "na"
                dot := dot.push ("      " ++ quote n ++ nodeAttrs k md strat ++ ";")
            dot := dot.push "    }"
        dot := dot.push "  }"
    for (s, t, po) in edges do
      let joint := stratMap.find? s != stratMap.find? t
      let attr := if po then "color=\"#CC3311\", style=dashed"
        else if joint then "color=\"#555555\"" else "color=\"#E2E2E2\""
      dot := dot.push ("  " ++ quote s ++ " -> " ++ quote t ++ " [" ++ attr ++ "];")
    dot := dot.push "}"
  -- JSON, each node tagged with kind, stratum, module.
  let nodeJson := nodes.map (fun n =>
    "{\"name\":\"" ++ n.toString ++ "\",\"kind\":\"" ++ (kindMap.find? n).getD "def"
      ++ "\",\"stratum\":\"" ++ (stratMap.find? n).getD "core"
      ++ "\",\"character\":\"" ++ (charMap.find? n).getD "neutral"
      ++ "\",\"modality\":\"" ++ (modalityMap.find? n).getD "na"
      ++ "\",\"axis\":\"" ++ (axisMap.find? n).getD "na"
      ++ "\",\"root\":\"" ++ rootLabel n
      ++ "\",\"shared\":" ++ toString (((sharedMap.find? n).getD 0))
      ++ ",\"isRoot\":" ++ (if isRoot n then "true" else "false")
      ++ ",\"module\":\"" ++ ((modMap.find? n).getD Name.anonymous).toString ++ "\"}")
  let edgeJson := edges.map (fun (s, t, po) =>
    "{\"source\":\"" ++ s.toString ++ "\",\"target\":\"" ++ t.toString
      ++ "\",\"kind\":\"" ++ (if po then "proofOnly" else "type") ++ "\"}")
  let json := "{\n  \"nodes\": [\n    " ++ String.intercalate ",\n    " nodeJson.toList
    ++ "\n  ],\n  \"edges\": [\n    " ++ String.intercalate ",\n    " edgeJson.toList ++ "\n  ]\n}\n"
  IO.FS.createDirAll "graph"
  IO.FS.writeFile (outBase ++ ".dot") (String.intercalate "\n" dot.toList ++ "\n")
  IO.FS.writeFile (outBase ++ ".json") json
  if emitData then
    -- A JS wrapped copy of the same data so the interactive viewer loads on file:// without a
    -- server (script tags are not CORS blocked). Regenerated from the JSON, do not hand edit.
    IO.FS.writeFile (outBase ++ "-data.js") ("window.DEPGRAPH = " ++ json ++ ";\n")
  if renderSvg then
    -- The byte-deterministic source of truth is the `.dot` and `.json`; the `.svg` is a force
    -- directed render (fdp), its encoding fixed by the `.dot`, exact coordinates vary by platform.
    -- The self-image pins the base and center, so it does not use a fixed start.
    let renderArgs := if selfImage
      then #["-Tsvg", "-Goverlap=prism", outBase ++ ".dot", "-o", outBase ++ ".svg"]
      else #["-Tsvg", "-Goverlap=prism", "-Gstart=self", outBase ++ ".dot", "-o", outBase ++ ".svg"]
    let rendered ← (IO.Process.output { cmd := "fdp", args := renderArgs }).toBaseIO
    match rendered with
    | Except.ok r =>
      if r.exitCode == 0 then IO.println s!"RENDERED {outBase}.svg"
      else IO.println s!"RENDER_FAILED fdp exit {r.exitCode}; run: fdp -Tsvg -Goverlap=prism {outBase}.dot -o {outBase}.svg"
    | Except.error _ =>
      IO.println s!"RENDER_SKIPPED graphviz not found; run: fdp -Tsvg -Goverlap=prism {outBase}.dot -o {outBase}.svg"
  -- Report.
  let targets : NameSet := edges.foldl (fun s e => s.insert e.2.1) {}
  IO.println s!"NODES {nodes.size}"
  for strat in strataOrder do
    let c := (nodes.filter (fun n => stratMap.find? n == some strat)).size
    if c > 0 then IO.println s!"  {strat} {c}"
  let axioms := nodes.filter (fun n => kindMap.find? n == some "axiom")
  IO.println s!"AXIOMS {axioms.size}"
  for n in axioms do IO.println s!"  {n}"
  let proofOnly := edges.filter (fun e => e.2.2)
  IO.println s!"EDGES {edges.size} (proof-only implicit {proofOnly.size})"
  let cross := edges.filter (fun e => stratMap.find? e.1 != stratMap.find? e.2.1)
  IO.println s!"CROSS {cross.size}"
  for (s, t, _) in cross do
    let ss := (stratMap.find? s).getD "?"
    let ts := (stratMap.find? t).getD "?"
    IO.println s!"  {s} -> {t}  ({ss} -> {ts})"
  let leaves := nodes.filter (fun n => !targets.contains n)
  IO.println s!"LEAVES {leaves.size}"
  IO.println "DROPPED"
  for (r, c) in dropCounts.toList.toArray.qsort (fun a b => a.1 < b.1) do
    let ex := (dropExamples.get? r).map (·.toString) |>.getD ""
    IO.println s!"  {r} {c}  e.g. {ex}"
  -- Modality tally (theorems and axioms).
  let assertional := nodes.filter (fun n =>
    kindMap.find? n == some "theorem" || kindMap.find? n == some "axiom")
  let forced := assertional.filter (fun n => modalityMap.find? n == some "forced")
  let conditional := assertional.filter (fun n => modalityMap.find? n == some "conditional")
  IO.println s!"MODALITY forced {forced.size} conditional {conditional.size} (of {assertional.size} assertional)"
  IO.println s!"PROP_INSTANCE_NODES {propInstNodes.size} (theorems with a failable propositional instance binder)"
  for n in propInstNodes.qsort nameLt do
    let md := (modalityMap.find? n).getD "na"
    IO.println s!"  {n} :: {md}"
  -- Axis tally (all nodes, four values).
  for ax in ["intra", "inter-cross", "inter-categorical", "na"] do
    IO.println s!"AXIS {ax} {(nodes.filter (fun n => axisMap.find? n == some ax)).size}"
  IO.println s!"AXIS_BOTH_SENSES {bothSenses.size} (assemblage and categorical at once)"
  for n in bothSenses.qsort nameLt do IO.println s!"  {n}"
  IO.println "INTER_CATEGORICAL"
  for n in nodes.filter (fun n => axisMap.find? n == some "inter-categorical") do IO.println s!"  {n}"
  -- Cross-check against known difference-lattice cells.
  IO.println "CROSSCHECK"
  let known : List Name :=
    [`Chiralogy.center_is_empty, `Chiralogy.NonDegenerate, `Chiralogy.four_quadrants,
     `Chiralogy.nondegenerate_iff_not_degenerate, `Chiralogy.exceeds,
     `Chiralogy.exceeding_requires_location, `Chiralogy.located, `Chiralogy.no_factor_forces_the_cross,
     `Chiralogy.inter_object_forced_cell_is_empty, `Chiralogy.floor_of_an_assemblage,
     `Chiralogy.survives_totalization, `Chiralogy.saturation_is_free,
     `Chiralogy.collapse_at_trivial_factor]
  for n in known do
    match kindMap.find? n with
    | some k =>
      let md := (modalityMap.find? n).getD "na"
      let ax := (axisMap.find? n).getD "na"
      IO.println s!"  {n} :: {k} / {md} / {ax}"
    | none => IO.println s!"  {n} :: (absent)"
  -- Nodes na on both modality and axis: should be non-lattice (defs, structures, pure categorical).
  let naBoth := nodes.filter (fun n => modalityMap.find? n == some "na" && axisMap.find? n == some "na")
  IO.println s!"NA_BOTH {naBoth.size} (expected non-lattice: defs, structures, pure categorical)"
  IO.println s!"FILES {outBase}.dot {outBase}.json"

end GraphCore
