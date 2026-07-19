import Chiralogy.Kernel.Apophatic
import Chiralogy.Kernel.Center
import Chiralogy.Kernel.Cataphatic
import Chiralogy.Model.Apophatic
import Chiralogy.Model.Apophatic.Instances
import Chiralogy.Model.Cataphatic
import Chiralogy.Model.Cataphatic.Instances
import Chiralogy.Model.Boundary
import Chiralogy.Protocol.Membership
import Chiralogy.Registers.Physics
import Chiralogy.Registers.TypeSystem

/-! # Chiralogy

The category of two-ended self-classifying maps `c : X → X → B` around an empty center: two ends (apophatic
codomain, cataphatic domain), `op`-related but non-superimposable. Lopsided: the apophatic hole is owned, the
cataphatic build is free.

The structural spine is kernel, model, boundary. The protocol is the conformance interface a domain enters
through, sitting beside the spine rather than between its parts: its only dependency is the kernel (it needs
the payload's hypothesis) and its only dependent is a register.

- `Kernel/Apophatic` the hole at the codomain.
- `Kernel/Center` the empty center between the ends.
- `Kernel/Cataphatic` the build at the domain.
- `Model/Apophatic` the absence-structure skeleton and the Maybe base.
- `Model/Apophatic/Instances` the tower of levels over Kl(Maybe).
- `Model/Cataphatic` the free skeleton.
- `Model/Cataphatic/Instances` the borrowed fillings.
- `Model/Boundary` the in-between.
- `Protocol/Membership` the conformance interface a domain submits to.
- `Registers/Physics` a domain entering through the protocol, at the base.
- `Registers/TypeSystem` a second domain entering, at a level.

`Experiments/` is the record, not built. Renamed from Autology. -/
