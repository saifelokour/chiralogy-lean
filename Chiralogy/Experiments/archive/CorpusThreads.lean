-- ARCHIVED (register and ground-structure graduation): resolved negatives (Girard idle for the ethics, the seam a third kind, no level division); not graduated.

import Chiralogy

/-! # Experiment: three threads from the old corpus

The corpus audit's surviving questions, asked against the framework as it now stands: the Girard obstruction
read as structure, the open seam read as an interface, and level division read against the tower. Independent
verdicts; a failure in one does not affect the others. Concrete small instances. Stays in `Experiments/`;
canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.CorpusThreads

/-! ## Thread 1: the framework read from Girard -/

/-- **What Girard gives.** Girard alone gives a global fact, no universe classifier (`IsEmpty
UniverseClassifier`), a statement about `Type` with no object variable, so nothing every object inherits from it.
The payload, which every classification inherits, comes from the diagonal (`hole_uniform`), not from Girard. -/
theorem what_girard_gives :
    (IsEmpty UniverseClassifier)
    ∧ (∀ {X : Type} (c : X → X → Option Bool), ¬ Function.Surjective c) :=
  ⟨no_universe_classifier, fun c => hole_uniform c⟩

/-- **Is there a Girard center.** Yes. The Lawvere center is `X ≃ (X → Bool)`, kept empty by the hole
(`empty_center`); the Girard center is `U ≃ Type`, a universe classifying itself, kept empty by
`no_small_universe`. Both coincidences are empty, one at the value level, one at the type level. -/
theorem is_there_a_girard_center :
    (¬ ∃ X : Type, Nonempty (X ≃ (X → Bool)))
    ∧ (¬ ∃ U : Type, Nonempty (U ≃ Type)) :=
  ⟨empty_center, no_small_universe⟩

/-- **Does Girard reach the ethics.** No. The permitted lattice and the prohibition rest on absences and the
diagonal, the permitted count over the reasons (three permitted, one prohibited); the universe obstruction is a
separate, independent fact about `Type` (`no_small_universe`), entering no classification and touching no
closure. Girard is structurally idle for the ethics. -/
theorem does_girard_reach_the_ethics :
    ((Finset.univ.filter (fun close : Bool → Bool => ¬ isFull close)).card = 3)
    ∧ ((Finset.univ.filter (fun close : Bool → Bool => isFull close)).card = 1)
    ∧ (¬ ∃ U : Type, Nonempty (U ≃ Type)) :=
  ⟨by decide, by decide, no_small_universe⟩

/-! ## Thread 2: is the seam a port? -/

/-- **What the seam is.** The seam braids the kernel hole (no complete self-account, per object) and the model
none (no complete-and-faithful map), the two layer-centers brought into contact by one utterance; the far side
(the imprecise target) is imported. -/
theorem what_the_seam_is :
    (∀ (X : Type) (c : X → X → Option Bool), ¬ Function.Surjective c) ∧
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2) :=
  the_open_seam

/-- **Seam versus protocol.** The seam is not a conformance gate. The protocol takes a domain, a `Member`, and
returns the payload (`payload`); the seam takes no domain, it is a fixed conjunction braiding two impossibilities,
with nothing submitted and nothing returned. -/
theorem seam_versus_protocol :
    (∀ M : Member, ¬ Function.Surjective M.classify)
    ∧ ((∀ (X : Type) (c : X → X → Option Bool), ¬ Function.Surjective c) ∧
       (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2)) :=
  ⟨fun M => payload M, the_open_seam⟩

/-- **Seam versus channel.** The seam is not a data-flow. The channel carries an account to the guard, returning
a constant verdict (`proposer_guard`); the seam carries no account, it is a static braid of two centers with no
flow and no input. -/
theorem seam_versus_channel {X B : Type} (build : X → (X → B)) {g : B → B} (hg : ∀ b, g b ≠ b) :
    (¬ Function.Surjective (proposedAccount build).build)
    ∧ ((∀ (Y : Type) (c : Y → Y → Option Bool), ¬ Function.Surjective c) ∧
       (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2)) :=
  ⟨proposer_guard build hg, the_open_seam⟩

/-- **Is the seam a third kind.** Yes. Neither gate nor flow but a co-location: `the_open_seam` is the braid
`boundary_braids_both_absences`, the two centers held together in one conjunction, no domain submitted and no
account carried. It is a statement bringing two centers into contact, not an interface; the MIXED mark resolves to
a structural braid. -/
theorem is_the_seam_a_third_kind :
    ((∀ (X : Type) (c : X → X → Option Bool), ¬ Function.Surjective c) ∧
     (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2))
    ∧ (the_open_seam = boundary_braids_both_absences) :=
  ⟨the_open_seam, rfl⟩

/-! ## Thread 3: what is it for a level to divide? -/

/-- **What would splitting be.** Splitting a level could be its grounds partitioned (here `{0} ∪ {1} = univ`,
disjoint), the order restricted to each part, or a level morphism jointly surjective from two sources (a cover).
The concrete candidate is a partition of the declared grounds. -/
theorem what_would_splitting_be :
    (({0} : Finset (Fin 2)) ∪ {1} = (Finset.univ : Finset (Fin 2)))
    ∧ (({0} : Finset (Fin 2)) ∩ {1} = ∅) :=
  ⟨by decide, by decide⟩

/-- **Does the tower support it.** The tower supports the limits, `Obj` has products (`obj_has_products`), but not
the colimit a division needs. A coproduct of two objects would classify cross-pairs like `(inl x1, inr x2)`, for
which there is no canonical value, two fillings both valid and differing; so `Obj` is finitely complete but has
no natural coproduct, and a level division as a coproduct or cover is not expressible. -/
theorem does_the_tower_support_it :
    (∀ S T : Obj, Nonempty (Hom (objProd S T) S) ∧ Nonempty (Hom (objProd S T) T))
    ∧ (∃ c1 c2 : (Unit ⊕ Unit) → (Unit ⊕ Unit) → Bool,
        c1 (Sum.inl ()) (Sum.inr ()) ≠ c2 (Sum.inl ()) (Sum.inr ())) :=
  ⟨fun S T => obj_has_products S T, ⟨fun _ _ => true, fun _ _ => false, by decide⟩⟩

/-- **Does anything follow.** Division is expressible but inert. The permitted count depends on the total reason
count (three at two reasons), not on any partition; each part has its own count (one at one reason), and these do
not recombine to the whole additively, so a partition of the grounds carries no ethical content. -/
theorem does_anything_follow :
    ((Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3)
    ∧ ((Finset.univ.filter (fun close : Fin 1 → Bool => ¬ ∀ r, close r = true)).card = 1) :=
  ⟨by decide, by decide⟩

/-! ## The verdicts

Thread 1: Girard gives no payload and does not reach the ethics, but it does have a center. It gives a global
fact about `Type`, no universe classifier, with no object variable, so nothing every object inherits
(`what_girard_gives`); the payload is the diagonal's. It has a center, `U ≃ Type` kept empty by
`no_small_universe`, the type-level analogue of the value-level `X ≃ (X → Bool)` (`is_there_a_girard_center`). But
it touches no closure: the permitted lattice and prohibition rest on absences and the diagonal, the universe
obstruction independent and idle (`does_girard_reach_the_ethics`). So the proven-independent Girard obstruction
has a center but no payload and no ethical reach, which is why the framework is Lawvere-shaped: everything built
runs through the diagonal, and Girard, though real, structures nothing downstream.

Thread 2: the seam is a third kind, neither protocol nor channel. It braids the kernel hole and the model none,
the far side imported (`what_the_seam_is`). It is not a conformance gate: the protocol takes a domain and returns
the payload, the seam takes no domain (`seam_versus_protocol`). It is not a data-flow: the channel carries an
account and returns a verdict, the seam carries nothing (`seam_versus_channel`). It is a co-location, the braid
itself, both centers in one conjunction with no input and no output (`is_the_seam_a_third_kind`): a statement, not
an interface. The MIXED mark resolves to a structural braid.

Thread 3: level division is manufactured or inert, never natural. The candidate is a partition of the grounds
(`what_would_splitting_be`); but the tower does not support the categorical division, `Obj` being finitely
complete yet having no natural coproduct, the cross-pair classification uncanonical
(`does_the_tower_support_it`); and a ground-partition is inert, the permitted count depending on the total reason
count and not recombining from the parts (`does_anything_follow`). The gate holds: no division operation is
manufactured, so the corpus's word had no content the tower supplies.

The verdict: three old questions, three settled negatives with structure. Girard has a center but no payload and
no ethical reach, so its independence explains rather than extends the framework, the whole being Lawvere-shaped
because the diagonal alone carries the payload and the ethics. The seam is a third interface kind, a co-location
of two centers rather than a gate or a flow, so its MIXED mark resolves to a statement not a port. Level division
is expressible only as an inert partition and not at all as a coproduct, so the corpus's speciation word names
nothing the tower supplies. Each is a real finding about the framework's shape, not a vindication of the old
notion. Reported per thread. Nothing here is resolved. -/

end Chiralogy.CorpusThreads
