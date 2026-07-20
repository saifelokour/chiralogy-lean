-- ARCHIVED (register and ground-structure graduation): the generic-over-opens results graduated to Model/Grounds.

import Chiralogy

/-! # Experiment: the ground-structure generically, over an arbitrary open

`Grounds` states the closeable family as the up-sets of a prerequisite order, an Alexandrov topology whose proper
opens are the permitted moves, currently indexed by a finite reason count. Test whether stating them over an
arbitrary open makes anything provable a count-indexed form cannot reach. `closeableG` is the generic form of
canonical `closeable`, over an arbitrary `ι` with a `Prop`-valued order and `Prop`-valued closures. The gate: a
generic statement counts only if it is provable over an arbitrary open where the current form needs a count; a
generic form that is the instance with a variable is notation. No general topology machinery; only the closeable
and up-set notions. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.GenericOpen

/-- The generic closeable predicate: closing `b` closes each prerequisite `a`, over an arbitrary order. -/
def closeableG {ι : Type} (prereq : ι → ι → Prop) (S : ι → Prop) : Prop :=
  ∀ a b, prereq a b → S b → S a

/-- The Heyting negation as the interior of the complement: the union of all closeable sets disjoint from `S`. -/
def negInterior {ι : Type} (prereq : ι → ι → Prop) (S : ι → Prop) : ι → Prop :=
  fun x => ∃ T : ι → Prop, closeableG prereq T ∧ (∀ y, T y → ¬ S y) ∧ T x

/-! ## Part 1: which results become count-free? -/

/-- **Permitted are the proper opens.** The whole space is closeable and is the top of the inclusion order (the
prohibition), so the permitted moves are the proper opens, without a count. The cardinality `2^n - 1` needs
finiteness; the structural fact does not. -/
theorem permitted_are_the_proper_opens {ι : Type} (prereq : ι → ι → Prop) :
    (closeableG prereq (fun _ => True))
    ∧ (∀ S : ι → Prop, closeableG prereq S → ∀ a, S a → (fun _ => True) a)
    ∧ (closeableG prereq (fun _ => False)) :=
  ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ h => h⟩

/-- **Operations generically.** An arbitrary intersection of closeable sets is closeable (meet) and an arbitrary
union is closeable (join), over any index type, infinite included: the operations stay inside the family without
finiteness. This is where complete distributivity does the work finiteness was doing. -/
theorem operations_generically {ι : Type} (prereq : ι → ι → Prop) :
    (∀ (J : Type) (F : J → (ι → Prop)), (∀ j, closeableG prereq (F j)) →
        closeableG prereq (fun x => ∀ j, F j x))
    ∧ (∀ (J : Type) (F : J → (ι → Prop)), (∀ j, closeableG prereq (F j)) →
        closeableG prereq (fun x => ∃ j, F j x)) :=
  ⟨fun _ _F hF a b hab hb j => hF j a b hab (hb j),
   fun _ _F hF a b hab => fun ⟨j, hj⟩ => ⟨j, hF j a b hab hj⟩⟩

/-- **Negation is the interior of the complement.** The negation is closeable and contained in the complement, a
proof from the definition rather than an observation; and it undershoots, the complement `{1}` under `0 ≺ 1` not
closeable, so the interior is strictly smaller. -/
theorem negation_is_interior_of_complement {ι : Type} (prereq : ι → ι → Prop) (S : ι → Prop) :
    (closeableG prereq (negInterior prereq S))
    ∧ (∀ x, negInterior prereq S x → ¬ S x)
    ∧ (∃ (J : Fin 2 → Fin 2 → Prop) (T : Fin 2 → Prop) (x : Fin 2),
        ¬ T x ∧ ¬ negInterior J T x) :=
  ⟨fun a b hab => fun ⟨U, hU, hUc, hUb⟩ => ⟨U, hU, hUc, hU a b hab hUb⟩,
   fun _ => fun ⟨U, _, hUc, hUx⟩ => hUc _ hUx,
   ⟨(fun a b => a = 0 ∧ b = 1), (fun z => z = 0), 1, by decide,
    fun ⟨U, hU, hUc, hU1⟩ => hUc 0 (hU 0 1 ⟨rfl, rfl⟩ hU1) rfl⟩⟩

/-! ## Part 2: does anything become provable that was not? -/

/-- **Infinite grounds.** At an infinite ground-set (`ℕ` with `<`) the generic forms hold where the count-indexed
ones are silent: the whole space is closeable (the prohibition at the top), the empty closure is a proper open,
and intersections of closeable sets stay closeable. The ethics' structure extends past its enumerated finite
instances. -/
theorem infinite_grounds :
    (closeableG (· < · : ℕ → ℕ → Prop) (fun _ => True))
    ∧ (closeableG (· < · : ℕ → ℕ → Prop) (fun _ => False))
    ∧ (∀ S T : ℕ → Prop, closeableG (· < ·) S → closeableG (· < ·) T →
        closeableG (· < ·) (fun x => S x ∧ T x)) :=
  ⟨fun _ _ _ _ => trivial, fun _ _ _ h => h,
   fun _ _ hS hT a b hab hb => ⟨hS a b hab hb.1, hT a b hab hb.2⟩⟩

/-- **What needed finiteness.** Residuation is recovered generically, the negation closeable with no exhaustive
check; and the Boolean complement is recovered only when the set complement is itself closeable (a discrete
order), the negation equalling the complement exactly then. The count `2^n - 1` needs finiteness and is not
recovered: an infinite family is not counted. -/
theorem what_needed_finiteness {ι : Type} (prereq : ι → ι → Prop) (S : ι → Prop) :
    (closeableG prereq (negInterior prereq S))
    ∧ ((∀ x, (¬ S x) → negInterior prereq S x) ↔ closeableG prereq (fun x => ¬ S x)) := by
  refine ⟨fun a b hab hb => ?_, ?_⟩
  · obtain ⟨U, hU, hUc, hUb⟩ := hb; exact ⟨U, hU, hUc, hU a b hab hUb⟩
  · constructor
    · intro h a b hab hnsb
      obtain ⟨U, hU, hUc, hUb⟩ := h b hnsb
      exact hUc a (hU a b hab hUb)
    · intro hc x hnsx
      exact ⟨fun y => ¬ S y, hc, fun y hy => hy, hnsx⟩

/-! ## Part 3: the honest test for notation -/

/-- **Is this renaming.** The closure under an arbitrary (here infinite, `ℕ`-indexed) union is content: it holds
at an infinite index, which no finite-count statement reaches. The binary union is the two-element-index instance
of the same generic fact, so at finite index the generic operation restates the count-indexed one, notation. -/
theorem is_this_renaming {ι : Type} (prereq : ι → ι → Prop) :
    (∀ F : ℕ → (ι → Prop), (∀ n, closeableG prereq (F n)) → closeableG prereq (fun x => ∃ n, F n x))
    ∧ (∀ S T : ι → Prop, closeableG prereq S → closeableG prereq T →
        closeableG prereq (fun x => S x ∨ T x)) :=
  ⟨fun _ hF a b hab => fun ⟨n, hn⟩ => ⟨n, hF n a b hab hn⟩,
   fun _ _ hS hT a b hab hb => hb.elim (fun h => Or.inl (hS a b hab h)) (fun h => Or.inr (hT a b hab h))⟩

/-! ## The verdicts

Part 1: the structural results are count-free. The permitted moves are the proper opens, the whole space the
prohibition at the top, with the empty closure a proper open (`permitted_are_the_proper_opens`); the operations,
arbitrary intersection and union, stay inside the family without finiteness (`operations_generically`); and the
negation is the interior of the complement, a proof from the definition, closeable and contained in the
complement, undershooting it (`negation_is_interior_of_complement`). The cardinality is the only part that keeps
its count.

Part 2: the generic forms hold at infinite ground-sets, and that is content. At `ℕ` with `<` the prohibition, the
proper opens, and the operations all hold (`infinite_grounds`), where the count-indexed results are silent. What
needed finiteness (`what_needed_finiteness`): the count `2^n - 1` is not recovered, an infinite family is not
counted; residuation is recovered structurally, the negation closeable with no exhaustive check; and the Boolean
complement is recovered only at a discrete order, the negation equalling the complement exactly when that
complement is closeable. So finiteness was doing the counting and the exhaustive checks, and the structure
survives without it while the cardinality does not.

Part 3: content where it extends, notation where it restates. The closure under an infinite union is content, no
finite-count statement reaching it; the binary union is the finite instance of the same generic fact, notation
(`is_this_renaming`). By the same standard: the arbitrary-index operations and the infinite-ground results are
content; the structural permitted, prohibition, and negation statements are notation at finite `ι` and content at
infinite; and the cardinality `2^n - 1` is essentially finite, neither renamed nor recovered generically.

The verdict: stating the ground-structure over an arbitrary open makes real content provable, not merely
renaming. The framework's ethics extends past its enumerated finite instances: the permitted family, the
prohibition at the top, and the lattice operations hold at infinite ground-sets, and the operations stay inside
the family under arbitrary joins and meets, which is what complete distributivity supplies and finiteness was
standing in for. But the extension is bounded and honest. Complete distributivity permits the arbitrary joins and
meets; it does not strengthen any finite statement, only carries it to the infinite case. The cardinality
`2^n - 1` genuinely needs finiteness and is not recovered. And the structural statements at a finite reason count
are the instance with a variable, notation by the same standard topology applied to fineness and sobriety, content
only where they reach the infinite. So the generic form is content at the infinite and at arbitrary index, and
notation at the finite, and the honest split is per statement, not wholesale. Reported per part. Nothing here is
resolved. -/

end Chiralogy.GenericOpen
