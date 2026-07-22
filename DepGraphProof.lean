import GraphCore

/-! Proof-level self-image target: `lake exe depgraph-proof`. Edges from proof terms (via `declValue`).
Emits `graph/depgraph-proof.{dot,json}` (the data) and renders `graph/depgraph-proof.svg`, the repo
self-image: base = the two absences and the diagonal-argument taproot; colour = character (the two
hands, apophatic larger); the empty center peripheral. Distinct from the statement-level `depgraph`. -/

def main : IO Unit :=
  GraphCore.run #[`Chiralogy] "graph/depgraph-proof" (proofLevel := true) (emitData := false)
    (renderSvg := true) (selfImage := true)
