import GraphCore

/-! Proof-level dependency graph target: `lake exe depgraph-proof`. Edges are extracted from proof
terms and definition bodies (via `declValue`, which unlike `value?` includes theorem proofs), not
just statement types. Distinct outputs `graph/depgraph-proof.{dot,json}`; the committed statement-
level `depgraph` is untouched. No render this pass (extraction and gate check only). -/

def main : IO Unit := GraphCore.run #[`Chiralogy] "graph/depgraph-proof" (proofLevel := true) (render := false)
