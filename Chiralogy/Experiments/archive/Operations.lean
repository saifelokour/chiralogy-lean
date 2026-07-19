import Chiralogy

/-! # Experiment: what do the lattice operations mean?

The permitted moves form a lattice with meet, join, negation, and a top that is the contradictory quotient. The
order and the top have readings; the operations do not. Ask what combining two closures means, given that the
elements are quotients of a theory and the top is inconsistency.

This is not a deontic algebra (a Boolean algebra of actions with permission laid over it): the elements are
quotients, the prohibition is an element, the top, not a predicate. One distinction is IMPORTED for comparison,
not adopted: deontic logic separates an obligation for the contradictory (self-defeating, `O⊥`) from jointly
inconsistent obligations (`OA ∧ O¬A`, unenforceable but coherent apart). Determine which the top is. Stays in
`Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Operations

/-! ## Part 1: the operations as operations on theories

A closure acts as a quotient by `closeE`, identifying each closed throw `inr e` with a verdict. State each
operation on that quotient action, not as set union, intersection, or complement relabelled. -/

/-- A closure imposes throw `e` iff its quotient collapses `inr e` to a verdict. -/
private theorem imposes_iff (S : Bool → Bool) (e : Bool) :
    closeE S (Sum.inr e) = Sum.inl true ↔ S e = true := by
  cases h : S e <;> simp [closeE, h]

/-- **Join is joint imposition.** As quotients, `cjoin a b` is the smallest theory imposing both: it imposes
everything `a` imposes and everything `b` imposes, and it imposes a throw only if `a` or `b` does. -/
theorem join_is_joint_imposition (a b : Bool → Bool) :
    (∀ e, closeE a (Sum.inr e) = Sum.inl true → closeE (cjoin a b) (Sum.inr e) = Sum.inl true)
    ∧ (∀ e, closeE b (Sum.inr e) = Sum.inl true → closeE (cjoin a b) (Sum.inr e) = Sum.inl true)
    ∧ (∀ e, closeE (cjoin a b) (Sum.inr e) = Sum.inl true →
        closeE a (Sum.inr e) = Sum.inl true ∨ closeE b (Sum.inr e) = Sum.inl true) := by
  refine ⟨fun e h => ?_, fun e h => ?_, fun e h => ?_⟩
  · rw [imposes_iff a e] at h; rw [imposes_iff (cjoin a b) e]; simp [cjoin, h]
  · rw [imposes_iff b e] at h; rw [imposes_iff (cjoin a b) e]; simp [cjoin, h]
  · rw [imposes_iff (cjoin a b) e] at h; rw [imposes_iff a e, imposes_iff b e]
    simpa [cjoin, Bool.or_eq_true] using h

/-- **Meet is common ground.** As quotients, `cmeet a b` is the largest theory both extend: it imposes a throw
iff both `a` and `b` impose it. -/
theorem meet_is_common_ground (a b : Bool → Bool) :
    (∀ e, closeE (cmeet a b) (Sum.inr e) = Sum.inl true →
        closeE a (Sum.inr e) = Sum.inl true ∧ closeE b (Sum.inr e) = Sum.inl true)
    ∧ (∀ e, closeE a (Sum.inr e) = Sum.inl true → closeE b (Sum.inr e) = Sum.inl true →
        closeE (cmeet a b) (Sum.inr e) = Sum.inl true) := by
  refine ⟨fun e h => ?_, fun e ha hb => ?_⟩
  · rw [imposes_iff (cmeet a b) e] at h; rw [imposes_iff a e, imposes_iff b e]
    simpa [cmeet, Bool.and_eq_true] using h
  · rw [imposes_iff a e] at ha; rw [imposes_iff b e] at hb; rw [imposes_iff (cmeet a b) e]
    simp [cmeet, ha, hb]

/-- **Negation closes the remainder.** The negation `fun r => !a r` collapses exactly the throws `a` leaves
open: its quotient identifies `inr e` iff `a`'s quotient leaves `inr e` untouched. -/
theorem negation_closes_the_remainder (a : Bool → Bool) (e : Bool) :
    closeE (fun r => !a r) (Sum.inr e) = Sum.inl true ↔ closeE a (Sum.inr e) = Sum.inr e := by
  cases h : a e <;> simp [closeE, h]

/-! ## Part 2: is the top `O⊥` or `OA ∧ O¬A`? -/

/-- **The top is self-defeating, not a clash.** The full closure is inconsistent in itself: one closure,
closing every reason while remaining faithful, collides (`full_totality_collides` needs a single map). And the
inconsistent element is the unique full closure (`exactly_one_prohibited`), a single element. So the top is
`O⊥`, an obligation for the contradictory, not `OA ∧ O¬A`, two coherent demands that clash. -/
theorem top_is_self_defeating_not_a_clash :
    (¬ ∃ c : Fin 4 → Fin 4 → Bool ⊕ Bool, (∀ x y, ∃ b, c x y = Sum.inl b) ∧ (∃ x y e, c x y = Sum.inr e))
    ∧ (∀ close : Bool → Bool, isFull close → close = fun _ => true) :=
  ⟨full_totality_collides, fun close h => (exactly_one_prohibited close).1 h⟩

/-- **Join with complement is bookkeeping, not substance.** `a ⊔ ¬a = ⊤` always. But it is generic: of the 16
ordered pairs of closures over two reasons, 9 join to the top while only 4 are complementary, so 5
non-complementary pairs also reach it. The identity is a lattice fact, not the special content of imposing a
stance together with exactly what it omits. -/
theorem join_with_complement_is_the_top :
    (∀ a : Bool → Bool, cjoin a (fun r => !a r) = fun _ => true)
    ∧ (Finset.univ.filter (fun p : (Bool → Bool) × (Bool → Bool) =>
          cjoin p.1 p.2 = fun _ => true)).card = 9
    ∧ (Finset.univ.filter (fun p : (Bool → Bool) × (Bool → Bool) =>
          p.2 = fun r => !p.1 r)).card = 4 := by
  refine ⟨fun a => ?_, by decide, by decide⟩
  funext r; simp only [cjoin]; cases a r <;> rfl

/-! ## Part 3: do the operations read in a domain?

Under forcing the readable moves are the up-sets (a domain with prerequisite structure among its grounds). Ask
whether the operations stay inside the readable set. -/

/-- **Operations under forcing.** Join and meet of two up-sets are up-sets, so they stay readable; the
complement of an up-set need not be an up-set, so negation can leave the readable set. -/
theorem operations_under_forcing :
    (∀ a b : Bool → Bool, isUpSet a → isUpSet b → isUpSet (cjoin a b))
    ∧ (∀ a b : Bool → Bool, isUpSet a → isUpSet b → isUpSet (cmeet a b))
    ∧ (∃ a : Bool → Bool, isUpSet a ∧ ¬ isUpSet (fun r => !a r)) :=
  ⟨by decide, by decide, ⟨fun r => r, by decide, by decide⟩⟩

/-- **Which operations read.** Combining two readable positions by meet or join is always readable; complementing
one is not. Of the three up-sets, only two have up-set complements: positions combine but do not complement, a
real asymmetry under forcing. -/
theorem which_operations_read :
    (∀ a b : Bool → Bool, isUpSet a → isUpSet b → isUpSet (cjoin a b) ∧ isUpSet (cmeet a b))
    ∧ (Finset.univ.filter (fun a : Bool → Bool => isUpSet a)).card = 3
    ∧ (Finset.univ.filter (fun a : Bool → Bool => isUpSet a ∧ isUpSet (fun r => !a r))).card = 2 :=
  ⟨by decide, by decide, by decide⟩

/-! ## The verdict

Part 1: the operations are statable on quotients, not relabelled set operations. Join is joint imposition, the
smallest theory imposing both closures (`join_is_joint_imposition`); meet is common ground, the largest theory
both extend (`meet_is_common_ground`); negation closes the remainder, the throws the closure leaves open
(`negation_closes_the_remainder`). Each is stated on the quotient action `closeE`, so the quotient reading is
available.

Part 2: the top is `O⊥`, self-defeating in itself. The full closure collides as a single map, closing every
reason while faithful, and is the unique inconsistent element (`top_is_self_defeating_not_a_clash`); it is the
contradictory quotient, not two coherent obligations that clash. But `a ⊔ ¬a = ⊤` is bookkeeping, not content:
9 of 16 ordered pairs join to the top and only 4 are complementary (`join_with_complement_is_the_top`), so
reaching the top is generic and the complement identity says nothing special.

Part 3: the operations split under forcing. Join and meet of readable positions stay readable, the up-sets being
closed under union and intersection; negation does not, the complement of an up-set need not be an up-set
(`operations_under_forcing`), and only two of the three up-sets have readable complements
(`which_operations_read`). Positions combine but do not complement.

The verdict: the order-operations mean something as operations on theories, join and meet reading as joint
imposition and common ground and preserving readability; the top is genuinely `O⊥`; but the one identity that
looked substantive, join with complement reaching the top, is generic, and negation is the weak operation,
generic at the top and not readability-preserving under forcing. All domain readings are READINGS with
defeasible mappings. Nothing here is resolved. -/

end Chiralogy.Operations
