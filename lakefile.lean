import Lake
open Lake DSL

package «chiralogy» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.31.0"

@[default_target]
lean_lib «Chiralogy»

lean_lib «GraphCore» where
  roots := #[`GraphCore]

lean_exe depgraph where
  root := `DepGraph

lean_exe «depgraph-preview» where
  root := `DepGraphPreview

lean_exe «depgraph-proof» where
  root := `DepGraphProof
