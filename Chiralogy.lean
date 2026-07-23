import Chiralogy.Kernel.Apophatic
import Chiralogy.Kernel.Center
import Chiralogy.Kernel.Cataphatic
import Chiralogy.Model.Apophatic
import Chiralogy.Model.Apophatic.Instances
import Chiralogy.Model.InformationOrder
import Chiralogy.Model.NaryAssemblage
import Chiralogy.Model.AssemblageRelations
import Chiralogy.Model.Grounds
import Chiralogy.Model.Cataphatic
import Chiralogy.Model.Cataphatic.Instances
import Chiralogy.Model.Boundary
import Chiralogy.Model.Permitted
import Chiralogy.Model.Tower
import Chiralogy.Model.GroundForensics
import Chiralogy.Model.Assemblage
import Chiralogy.Protocol.Membership
import Chiralogy.Protocol.GroundTemplates
import Chiralogy.Registers.Physics
import Chiralogy.Registers.TypeSystem
import Chiralogy.Registers.GroundStructures

/-! # Chiralogy

The category of two-ended self-classifying maps `c : X → X → B` around an empty center: two ends (apophatic
codomain, cataphatic domain), `op`-related but non-superimposable. Lopsided: the apophatic hole is owned, the
cataphatic build is free.

The spine is kernel, model, boundary. `Model/` is two pairs, each one layer of the same question. Tower and
Grounds, what there is: the categories of objects, and the structures those objects can present. Boundary and
Permitted, the interface and its ethics: where the arms meet and the limit sits, and what may be done there. The
arms sit between. Assemblage is lateral to the tower: the tower relates an object to itself with more or less
structure, an assemblage relates several objects to a new one alongside them. The protocol is the conformance
interface a domain enters through, beside the spine rather than between its parts: its only dependency is the
kernel and its only dependent a register.

The hole's no-final-coalgebra reading is a theorem: `no_final_coalgebra_for_the_classifier`, no `X ≅ X → B`, so
that functor has no final coalgebra as powerset has none by Cantor, which selects the available dynamics. READING
(a reading, not a theorem): each arm is algebraic or observational in flavour, cataphatic building and apophatic
observing. This is a characterization, not the algebra/coalgebra duality for a shared functor, which is refuted:
the cataphatic arm spans multiple signature functors, so it is no single `Alg F`, and `F X = X → B` is
contravariant, not an endofunctor (the classification map is a coalgebra structure map for that contravariant
functor, which is why the Lambek route works while the duality does not). A ground reads as a way of failing to
produce, the guard as an observation seeing one bit (`guard_uniformity_is_observational_coarseness`).

- `Kernel/Apophatic` the hole at the codomain.
- `Kernel/Center` the empty center between the ends.
- `Kernel/Cataphatic` the build at the domain.
- `Model/Apophatic` the absence-structure skeleton and the Maybe base.
- `Model/Apophatic/Instances` the levels over Kl(Maybe).
- `Model/Grounds` the ground-structures a domain's prerequisites present.
- `Model/Tower` the categories of objects and their forgetful functors.
- `Model/Assemblage` the construction relating several objects to a new one alongside them.
- `Model/Cataphatic` the free skeleton.
- `Model/Cataphatic/Instances` the borrowed fillings.
- `Model/Boundary` the interface where the arms meet.
- `Model/Permitted` the ethics on the declared grounds.
- `Protocol/Membership` the conformance interface a domain submits to.
- `Protocol/GroundTemplates` the occupancy specifications, model-free.
- `Registers/Physics` a domain entering at the base.
- `Registers/TypeSystem` a second domain entering, at a level.

`Experiments/` is the record, not built. Renamed from Autology. -/
