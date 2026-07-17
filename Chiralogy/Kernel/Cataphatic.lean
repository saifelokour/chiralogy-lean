import Chiralogy.Kernel.Apophatic

/-! # Kernel: the cataphatic end (the build at the domain)

The build lives at the domain, and it is free: the transpose of any `c` always exists, so this arm is thin
(its theorems are `⟨c, rfl⟩`-shaped, no obstruction to prove). `spine_cataphatic_is_transpose` gives the free
transpose slot; `cataphatic_kernel_has_one_inversion` records the single inversion (so no cataphatic kernel
chiasm). The end-namings (`apophatic_center_is_codomain`, `cataphatic_center_is_domain`) and the unifying
`one_map_two_ends` live in `Center` (they are the relation between the ends, not the build alone). -/

namespace Chiralogy
/-- **The spine's cataphatic slot is the transpose.** For the bare map `c : X → X → B`, the cataphatic
end is exactly `c`'s transpose, a map `X → (X → B)`. -/
theorem spine_cataphatic_is_transpose {X B : Type} (c : X → X → B) :
    ∃ build : X → (X → B), build = c :=
  ⟨c, rfl⟩

/-- **One inversion, no kernel chiasm.** The cataphatic kernel has a single move, the free transpose (the
account is `c` read as a build). With one inversion there is no two-armed crossing at the kernel. -/
theorem cataphatic_kernel_has_one_inversion {X B : Type} (c : X → X → B) :
    ∃ build : X → (X → B), build = c :=
  ⟨c, rfl⟩
end Chiralogy
