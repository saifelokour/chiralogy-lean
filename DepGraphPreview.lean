import GraphCore

/-! Preview target: `lake exe depgraph-preview <ExperimentShortName>`.

Emits `graph/preview-<name>.{dot,json}`: the canonical spine plus one experiment, the experiment
nodes rendered dashed (un-graduated). The experiment must be listed in the committed
`graph/experiment-set.txt`, so the preview is deterministic. Its olean must be built first
(`lake build Chiralogy.Experiments.<name>`). On demand for graduation planning, never the
committed reference graph. -/

open Lean

def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.eprintln "usage: depgraph-preview <ExperimentShortName> (from graph/experiment-set.txt)"
  | name :: _ =>
    let setTxt ← IO.FS.readFile "graph/experiment-set.txt"
    let allowed := ((setTxt.splitOn "\n").map (fun s => s.trimAscii.toString)).filter
      (fun s => s != "" && !s.startsWith "#")
    if !allowed.contains name then
      IO.eprintln s!"'{name}' is not in graph/experiment-set.txt (the committed preview set)"
    else
      let mod := (`Chiralogy.Experiments).str name
      -- Proof-level, coloured by character (the measured encoding), consistent with the self-image.
      GraphCore.run #[`Chiralogy, mod] s!"graph/preview-{name}"
        (proofLevel := true) (charColorMode := true)
