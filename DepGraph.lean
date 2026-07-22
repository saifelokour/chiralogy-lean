import GraphCore

/-! Canonical dependency graph target: `lake exe depgraph`. Emits `graph/depgraph.{dot,json}`. -/

def main : IO Unit := GraphCore.run #[`Chiralogy] "graph/depgraph"
