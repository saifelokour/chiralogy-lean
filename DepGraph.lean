import GraphCore

/-! Statement-level data target: `lake exe depgraph`. Emits `graph/depgraph.{dot,json}` and
`graph/depgraph-data.js` (the interactive viewer loads the JS wrapper). The retired probe SVG is no
longer rendered; the repo picture is the proof-level self-image (`lake exe depgraph-proof`). -/

def main : IO Unit := GraphCore.run #[`Chiralogy] "graph/depgraph" (emitData := true) (renderSvg := false)
