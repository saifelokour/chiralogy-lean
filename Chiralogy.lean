import Chiralogy.Kernel.Apophatic
import Chiralogy.Kernel.Center
import Chiralogy.Kernel.Cataphatic
import Chiralogy.Protocol.Membership
import Chiralogy.Model.Apophatic
import Chiralogy.Model.Boundary
import Chiralogy.Model.Cataphatic
import Chiralogy.Model.Cataphatic.Instances
import Chiralogy.Registers.Physics

/-! # Chiralogy

The category of two-ended self-classifying maps `c : X → X → B` around an empty center: two ends (apophatic
codomain, cataphatic domain), `op`-related but non-superimposable. Lopsided: the apophatic hole is owned, the
cataphatic build is free.

- `Kernel/Apophatic` the hole at the codomain.
- `Kernel/Center` the empty center between the ends.
- `Kernel/Cataphatic` the build at the domain.
- `Protocol/Membership` the object condition.
- `Model/Apophatic` `Kl(Maybe)`, keep-the-none.
- `Model/Boundary` the in-between.
- `Model/Cataphatic` the free skeleton.
- `Model/Cataphatic/Instances` the borrowed fillings.
- `Registers/Physics` a shared domain.

`Experiments/` is the record, not built. Renamed from Autology. -/
