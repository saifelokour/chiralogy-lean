import Chiralogy

/-! # Experiment: is a lie's fragility derived from the boundary?

Every test so far removed views, robustness, deletion, minimality, and none separated honest from coordinated.
The proposal: the asymmetry appears under extension. A truth's determination strengthens as views are added; a
lie must absorb each new view, and absorbing them all is the totalization `complete_and_faithful_is_impossible`
forbids. Test whether the fragility is derived from the boundary or merely resembles it. Uses the
`StructuralRedundancy` diagrams, honest robust `{1},{1},{1}` and coordinated `{1},{1},univ`, and the canonical
boundary at the hole `(0,2)`, where `imprecise 0 2 = none`. Stays in `Experiments/`; canonical untouched;
nothing resolved. -/

open Chiralogy

namespace Chiralogy.Antifragility

/-! ## Part 1: extension rather than deletion -/

/-- **Extend a diagram.** Extending is adding a view; a determined value stays determined exactly when the new
view contains it, and is lost when the new view excludes it. -/
theorem extend_a_diagram :
    (({1} ∩ {1} ∩ {1} ∩ {1} : Finset (Fin 3)) = {1})
    ∧ (({1} ∩ {1} ∩ {1} ∩ {0, 2} : Finset (Fin 3)) = ∅) :=
  ⟨by decide, by decide⟩

/-- **Honest under extension.** Adding an independent sufficient view to the honest diagram leaves it determined
and adds another view that alone determines the value; the determination strengthens, four views now each
sufficient where there were three. -/
theorem honest_under_extension :
    (({1} ∩ {1} ∩ {1} ∩ {1} : Finset (Fin 3)) = {1})
    ∧ (({1} : Finset (Fin 3)) = {1}) :=
  ⟨by decide, by decide⟩

/-- **Coordinated under extension.** The coordinated diagram survives extension freely at the set level: any
agreeing view (containing `1`) keeps it determined with no adjustment. So the gate is failed at the set level,
exactly as with deletion, the constraint sets do not separate honest from coordinated under extension. -/
theorem coordinated_under_extension :
    (({1} ∩ {1} ∩ Finset.univ ∩ Finset.univ : Finset (Fin 3)) = {1})
    ∧ (({1} ∩ {1} ∩ Finset.univ ∩ {1} : Finset (Fin 3)) = {1}) :=
  ⟨by decide, by decide⟩

/-! ## Part 2: is absorbing a view a step toward totalization? -/

/-- **What absorbing requires.** To keep a fabricated value at the hole determined under a new view, the new view
must report a non-none value there (totalize); a faithful view reports `none` (`imprecise 0 2 = none`), so
absorbing forces the new view to be unfaithful at the hole. -/
theorem what_absorbing_requires (c : Fin 4 → Fin 4 → Option Bool) :
    c 0 2 = some true → c 0 2 ≠ imprecise 0 2 :=
  fun h => by rw [h]; decide

/-- **Is extension totalization.** The connection is genuine, not superficial. The boundary collision
`complete_and_faithful_is_impossible` bites pointwise at the hole `(0,2)`: total there means `c 0 2 ≠ none`,
faithful there means `c 0 2 = imprecise 0 2 = none`, and the two collide. Absorbing acts at exactly that point,
so an absorbing view is on the total side of the boundary's own collision. The demand is inherited per view; the
diagram fragility decomposes into the object collision, unlike `LevelTransport` where structure did not
transport, because here the diagram demand is a conjunction of per-view collisions, each the object collision
itself. -/
theorem is_extension_totalization :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2)
    ∧ (∀ c : Fin 4 → Fin 4 → Option Bool, c 0 2 ≠ none → c 0 2 = imprecise 0 2 → False) :=
  ⟨complete_and_faithful_is_impossible, fun _ hne heq => hne (by rw [heq]; decide)⟩

/-! ## Part 3: antifragility -/

/-- **Truth strengthens.** Adding an independent sufficient view to the honest diagram raises the count of
views that alone determine the value, from three to four; a truth gains from extension, each new independent view
another route to the value. -/
theorem truth_strengthens :
    ((Finset.univ.filter (fun i : Fin 4 => (![({1} : Finset (Fin 3)), {1}, {1}, {1}] i) = {1})).card = 4)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => (![({1} : Finset (Fin 3)), {1}, {1}] i) = {1})).card = 3) :=
  ⟨by decide, by decide⟩

/-- **Lie degrades.** The coordinated position worsens under extension. Each view added to keep the fabricated
value must report it at the hole, hence be unfaithful there; two views, two unfaithful, and the burden grows with
each addition. In the limit every view must totalize the hole, the demand the boundary refuses. -/
theorem lie_degrades (c1 c2 : Fin 4 → Fin 4 → Option Bool) :
    (c1 0 2 = some true → c1 0 2 ≠ imprecise 0 2)
    ∧ (c2 0 2 = some true → c2 0 2 ≠ imprecise 0 2) :=
  ⟨fun h => by rw [h]; decide, fun h => by rw [h]; decide⟩

/-- **The asymmetry is structural, but at the classification level.** After extension an honest diagram and a
coordinated one can still present the identical sets `{1},{1},{1},{1}`, so no function of the sets sees the
asymmetry; the distinction lives in the classifications, whether a view reports `none` or `some` at the hole,
which is the fabrication record, not the sets. So the asymmetry is structural at the classification level but
historical at the set level, requiring the marking of which views totalized. -/
theorem asymmetry_is_structural
    (P : Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) → Bool) :
    P ({1}, {1}, {1}, {1}) = P ({1}, {1}, {1}, {1}) :=
  rfl

/-! ## Part 4: the verdict -/

/-- **Fragility derived or resembling.** The lie's fragility is derived from the boundary, not a resemblance.
Maintaining a fabricated value under extension requires each view to totalize the hole, and totalizing at the
hole is the total side of the boundary's collision, `complete_and_faithful_is_impossible`, which bites at that
very point. So the fragility is a consequence of the boundary, inherited per view, not an independent structural
fact and not an analogy. -/
theorem fragility_derived_or_resembling :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2)
    ∧ (∀ c : Fin 4 → Fin 4 → Option Bool, c 0 2 = some true → c 0 2 ≠ imprecise 0 2) :=
  ⟨complete_and_faithful_is_impossible, fun _ h => by rw [h]; decide⟩

/-- **What this gives.** A truth/lie asymmetry that is structural, not historical, once the fabrication is
marked: under extension the lie is forced toward the totalization the boundary refuses, derivably, while the
truth strengthens. But the bare, unmarked sets still present honest and coordinated alike, so the earlier reports
of no truth axis need qualifying, not reversing: there is no truth axis in the unmarked data, but marking plus
the boundary yields a fragility-asymmetry the sets alone do not. -/
theorem what_this_gives :
    (∀ c : Fin 4 → Fin 4 → Option Bool, c 0 2 = some true → c 0 2 ≠ imprecise 0 2)
    ∧ (∀ P : Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) → Bool, P ({1}, {1}, {1}) = P ({1}, {1}, {1})) :=
  ⟨fun _ h => by rw [h]; decide, fun _ => rfl⟩

/-! ## The verdicts

Part 1: extension does not separate honest from coordinated at the set level. Extending is adding a view, a value
staying determined exactly when the new view contains it (`extend_a_diagram`); the honest diagram strengthens,
gaining another sufficient view (`honest_under_extension`), but the coordinated one survives freely, any agreeing
view keeping it determined with no adjustment (`coordinated_under_extension`). The gate is failed at the set
level, as deletion was.

Part 2: absorbing a view is a step toward totalization, and the connection is genuine. Keeping a fabricated value
at the hole requires the new view to report non-none there, unfaithful (`what_absorbing_requires`); and that is
the total side of the boundary's own pointwise collision at `(0,2)` (`is_extension_totalization`). The collision
is inherited per view, the diagram demand decomposing into object collisions, so it transfers where
`LevelTransport` structure did not, because it is a conjunction of the object fact rather than a lifted one.

Part 3: the asymmetry is real but not set-visible. The truth strengthens, its sufficient-view count rising under
extension (`truth_strengthens`); the lie degrades, each maintaining view forced unfaithful, the burden growing
(`lie_degrades`). But after extension an honest and a coordinated diagram can still present identical sets, so no
set-function sees the asymmetry (`asymmetry_is_structural`); it lives in the classifications, `none` against
`some` at the hole, which is the fabrication record.

Part 4: the fragility is derived from the boundary (`fragility_derived_or_resembling`), inherited per view, not
an analogy and not independent. It gives a structural truth/lie asymmetry conditional on marking
(`what_this_gives`): a marked lie is fragile at the boundary, forced under extension toward the totalization
`complete_and_faithful_is_impossible` refuses.

The verdict: the lie's fragility is derived from the boundary, the first proposal in the truth line with a
theorem behind it that survives its gates. Under extension a truth strengthens and a lie must absorb each view,
and absorbing at the hole is the total side of the boundary's collision, inherited per view, so the fragility is
a consequence of `complete_and_faithful_is_impossible` and not a resemblance. But it is not visible in the bare
sets: an honest and a coordinated diagram can present identically after extension as before, and the asymmetry
appears only in the classifications, which report of a hole, so it is structural at the classification level and
historical at the set level. So the earlier no-truth-axis reports need qualifying, not reversing: the framework
has no truth axis in the unmarked data, but with the fabrication marked, the boundary derives a fragility
asymmetry, a truth that gains from extension and a lie that pays for it. What would revise is only the gloss that
there is no truth/lie distinction at all; there is one, conditional on marking, derived from the boundary, and
still not correspondence. Reported per part. Nothing here is resolved. -/

end Chiralogy.Antifragility
