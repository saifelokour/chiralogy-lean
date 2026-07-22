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
  -- Pass 2: edges, re-pointed and filtered to kept targets, deduped, no self loops.
  let mut edges : Array (Name × Name) := #[]
  for (n, ci) in kept do
    let val := if proofLevel then declValue ci else ci.value?
    let used := ci.type.getUsedConstants ++ (val.map (·.getUsedConstants)).getD #[]
    let deps : NameSet := used.foldl
      (fun s d => match resolveDep env keptSet n d with | some t => s.insert t | none => s) {}
    for d in deps.toList do
      edges := edges.push (n, d)
  let nodes := (kept.map (·.1)).qsort nameLt
  edges := edges.qsort edgeLt
  let mut dot : Array String := #[]
  if selfImage then
    -- The self-image: the MEASURED shape. Base (two absences + diagonal taproot) pinned low,
    -- colour = character (the two hands, apophatic the larger), the empty center pinned peripheral.
    let special := baseNodes ++ [peripheralCenter]
    let hdr := "Chiralogy self-image (proof-level). Regenerated by `lake exe depgraph-proof`, do not edit."
      ++ "\\lThe measured shape: the two kernel absences and the diagonal-argument taproot at the base;"
      ++ " colour = character (blue apophatic, the larger hand; orange cataphatic; grey scaffolding; purple seam);"
      ++ " the empty center peripheral; the register and filling instances a symmetric family.\\l"
    dot := #[
      "digraph SelfImage {", "  overlap=prism; splines=true; outputorder=edgesfirst;",
      "  graph [fontname=\"Helvetica\", labelloc=t, label=\"" ++ hdr ++ "\"];",
      "  node [style=filled, fontname=\"Helvetica\", fontsize=6, penwidth=0.3, shape=ellipse];",
      "  edge [arrowsize=0.3, color=\"#DFDFDF\"];",
      "  subgraph cluster_legend {", "    label=\"legend\"; fontsize=16; style=rounded; color=\"#888888\";",
      "    \"L_apophatic\" [label=\"apophatic\", shape=box, fillcolor=\"#4477AA\", fontcolor=white];",
      "    \"L_cataphatic\" [label=\"cataphatic\", shape=box, fillcolor=\"#EE7733\"];",
      "    \"L_neutral\" [label=\"scaffolding\", shape=box, fillcolor=\"#CCCCCC\"];",
      "    \"L_seam\" [label=\"seam\", shape=box, fillcolor=\"#AA4499\", fontcolor=white];",
      "    \"L_base\" [label=\"base: absences + taproot\", shape=hexagon, fillcolor=\"#4477AA\", fontcolor=white];",
      "    \"L_center\" [label=\"empty center (peripheral)\", shape=ellipse, fillcolor=\"#EEEEEE\"];",
      "    \"L_apophatic\" -> \"L_cataphatic\" -> \"L_neutral\" -> \"L_seam\" [style=invis];", "  }"]
    for ch in ["apophatic", "cataphatic", "neutral", "seam"] do
      let label := match ch with
        | "apophatic" => "apophatic (the larger hand)" | "neutral" => "scaffolding (neutral)" | s => s
      let cn := nodes.filter (fun n => charMap.find? n == some ch && !special.contains n)
      if cn.size > 0 then
        dot := dot.push ("  subgraph cluster_" ++ ch ++ " { label=\"" ++ label
          ++ "\"; color=\"" ++ charColor ch ++ "\"; fontsize=20; style=rounded;")
        for n in cn do dot := dot.push ("    " ++ quote n ++ " [fillcolor=\"" ++ charColor ch ++ "\"];")
        dot := dot.push "  }"
    dot := dot.push ("  " ++ quote taproot ++ " [pos=\"0,-46!\", fillcolor=\"#4477AA\", shape=doublecircle,"
      ++ " penwidth=3, width=0.5, fontsize=11, fontcolor=white, label=\"fixedPoint_of_surjection\\n(diagonal-argument taproot)\"];")
    dot := dot.push ("  " ++ quote (`Chiralogy.no_reflexive_object) ++ " [pos=\"-22,-40!\", fillcolor=\"#4477AA\","
      ++ " shape=hexagon, penwidth=2.5, width=0.5, fontsize=11, fontcolor=white, label=\"no_reflexive_object\\n(kernel absence)\"];")
    dot := dot.push ("  " ++ quote (`Chiralogy.hole_uniform) ++ " [pos=\"22,-40!\", fillcolor=\"#4477AA\","
      ++ " shape=hexagon, penwidth=2.5, width=0.5, fontsize=11, fontcolor=white, label=\"hole_uniform\\n(kernel absence)\"];")
    dot := dot.push ("  " ++ quote peripheralCenter ++ " [pos=\"52,40!\", fillcolor=\"#EEEEEE\", shape=ellipse,"
      ++ " penwidth=0.6, fontsize=9, label=\"center_is_empty\\n(peripheral empty center)\"];")
    for (s, t) in edges do dot := dot.push ("  " ++ quote s ++ " -> " ++ quote t ++ ";")
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
    for (s, t) in edges do
      let joint := stratMap.find? s != stratMap.find? t
      let col := if joint then "#555555" else "#E2E2E2"
      dot := dot.push ("  " ++ quote s ++ " -> " ++ quote t ++ " [color=\"" ++ col ++ "\"];")
    dot := dot.push "}"
  -- JSON, each node tagged with kind, stratum, module.
  let nodeJson := nodes.map (fun n =>
    "{\"name\":\"" ++ n.toString ++ "\",\"kind\":\"" ++ (kindMap.find? n).getD "def"
      ++ "\",\"stratum\":\"" ++ (stratMap.find? n).getD "core"
      ++ "\",\"character\":\"" ++ (charMap.find? n).getD "neutral"
      ++ "\",\"modality\":\"" ++ (modalityMap.find? n).getD "na"
      ++ "\",\"axis\":\"" ++ (axisMap.find? n).getD "na"
      ++ "\",\"module\":\"" ++ ((modMap.find? n).getD Name.anonymous).toString ++ "\"}")
  let edgeJson := edges.map (fun (s, t) =>
    "{\"source\":\"" ++ s.toString ++ "\",\"target\":\"" ++ t.toString ++ "\"}")
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
  let targets : NameSet := edges.foldl (fun s (_, t) => s.insert t) {}
  IO.println s!"NODES {nodes.size}"
  for strat in strataOrder do
    let c := (nodes.filter (fun n => stratMap.find? n == some strat)).size
    if c > 0 then IO.println s!"  {strat} {c}"
  let axioms := nodes.filter (fun n => kindMap.find? n == some "axiom")
  IO.println s!"AXIOMS {axioms.size}"
  for n in axioms do IO.println s!"  {n}"
  IO.println s!"EDGES {edges.size}"
  let cross := edges.filter (fun (s, t) => stratMap.find? s != stratMap.find? t)
  IO.println s!"CROSS {cross.size}"
  for (s, t) in cross do
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
