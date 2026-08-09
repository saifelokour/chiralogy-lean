import Chiralogy

/-! Per declaration facts the labeling driver needs and the dependency extraction does not carry.

For every canonical declaration, one tab separated line:

  name <tab> typeHash <tab> proofHead <tab> externalDeps

followed by one line per external constant seen:

  MODULE <tab> constant <tab> declaring module

typeHash is the structural hash of the declaration's type, so two declarations stating the same
proposition agree on it. proofHead is the head constant of the declaration's value after stripping
binders, or a dash when there is none. externalDeps are the constants the declaration uses directly,
from its type and its value, that lie outside the framework's own namespace, comma separated.

Regenerable: reads the compiled environment, sorts by name, no timestamps. Run with

  lake env lean graph/decl-facts.lean
-/

open Lean

private def isChir (n : Name) : Bool := (`Chiralogy).isPrefixOf n

private partial def stripBinders : Expr → Expr
  | .lam _ _ b _ => stripBinders b
  | .letE _ _ _ b _ => stripBinders b
  | .mdata _ b => stripBinders b
  | e => e

private def headOf (e : Expr) : String :=
  match (stripBinders e).getAppFn with
  | .const n _ => n.toString
  | _ => "-"

private def externalOf (ci : ConstantInfo) : Array Name :=
  let fromType := ci.type.getUsedConstants
  let fromVal := match ci.value? with | some v => v.getUsedConstants | none => #[]
  let all := fromType ++ fromVal
  let ext := all.filter fun n => !isChir n && !n.isInternal && n != `sorryAx
  ext.qsort (fun a b => a.toString < b.toString) |>.foldl
    (fun acc n => if acc.back? == some n then acc else acc.push n) #[]

#eval show CoreM Unit from do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    if isChir n && !n.isInternal then
      let hd := match ci.value? with | some v => headOf v | none => "-"
      let ext := String.intercalate "," ((externalOf ci).toList.map Name.toString)
      rows := rows.push s!"{n}\t{ci.type.hash}\t{hd}\t{ext}"
  for r in rows.qsort (fun a b => a < b) do
    IO.println r
  -- the declaring module of every external constant used, so a substrate primitive can be told from a
  -- library result: MODULE <tab> constant <tab> module
  let mut ext : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if isChir n && !n.isInternal then
      for e in externalOf ci do
        ext := ext.push e
  let exts := ext.qsort (fun a b => a.toString < b.toString)
  let mut prev : Option Name := none
  for e in exts do
    if prev != some e then
      prev := some e
      let m := match env.getModuleIdxFor? e with
        | some idx => (env.header.moduleNames[idx.toNat]!).toString
        | none => "-"
      IO.println s!"MODULE\t{e}\t{m}"
