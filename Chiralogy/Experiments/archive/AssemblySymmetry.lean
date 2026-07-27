import Chiralogy.Model.AssemblageRelations

/-! ARCHIVED (fully graduated). The fibre-preserving automorphism law, carrier-general.

GRADUATED to `Model/NaryAssemblage`, same names: `Pt`, `Fib`, `Fib_apply`, `Fib_differsInOne`, `Fib_cross`,
`fib_fixes_iff`, `factor_condition_is_local`, `full_product_when_unconstrained` (spec 9.14).

The correction this file made stands: the factors DO constrain their own coordinates, so "only the import can
break symmetry" was too strong; what is true is that the factor conditions are local and per-coordinate while
the import condition is global. Typechecks standalone. -/

/-! # Experiment (LIVE): lifting the assembly-symmetry law off its carrier

`AsymmetricCone` measured, decide-bound on a four-point carrier, that an assembly's automorphism group has
order eight for both equal and unequal factors, and read that as "the factors cannot break the symmetry, only
the import can". This lifts the question off the fixed carrier.

The lift CORRECTS the reading in two places. Both corrections are recorded where they occur rather than in a
footnote, because the reading was the middle clause of a chain.

Neutral, gravity-free. Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.AssemblySymmetry


/-! ### GRADUATED (Model/NaryAssemblage pass)

Into `Model/NaryAssemblage`, same names: `Pt`, `Fib`, `Fib_apply`, `Fib_differsInOne`, `Fib_cross`,
`fib_fixes_iff`, `factor_condition_is_local`, `full_product_when_unconstrained`. The local `relabel` is
superseded by the canonical one graduated in the Moves pass. -/

/-! ## Part 1: the action, the fibre-preserving maps, and what the regions force -/

section General

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

abbrev Pt (X : Fin n → Type) := ∀ k, X k

abbrev IsCross (a b : Pt X) : Prop := ¬ ∃ i, differsInOne a b i


/-- A FIBRE-PRESERVING map: one built coordinatewise, acting inside each coordinate and mixing none. -/
def Fib (π : ∀ k, X k → X k) (a : Pt X) : Pt X := fun k => π k (a k)

theorem Fib_apply (π : ∀ k, X k → X k) (a : Pt X) (k : Fin n) : Fib π a k = π k (a k) := rfl

/-- **A fibre-preserving injection preserves each region setwise**, in both directions. -/
theorem Fib_differsInOne (π : ∀ k, X k → X k) (hinj : ∀ k, Function.Injective (π k))
    (a b : Pt X) (k : Fin n) :
    differsInOne (Fib π a) (Fib π b) k ↔ differsInOne a b k := by
  constructor
  · rintro ⟨hne, hoth⟩
    refine ⟨fun hc => hne (by rw [Fib_apply, Fib_apply, hc]), fun j hj => ?_⟩
    exact hinj j (hoth j hj)
  · rintro ⟨hne, hoth⟩
    refine ⟨fun hc => hne (hinj k hc), fun j hj => ?_⟩
    rw [Fib_apply, Fib_apply, hoth j hj]

/-- And it preserves the cross region setwise. -/
theorem Fib_cross (π : ∀ k, X k → X k) (hinj : ∀ k, Function.Injective (π k)) (a b : Pt X) :
    IsCross (Fib π a) (Fib π b) ↔ IsCross a b := by
  constructor
  · rintro h ⟨k, hk⟩
    exact h ⟨k, (Fib_differsInOne π hinj a b k).mpr hk⟩
  · rintro h ⟨k, hk⟩
    exact h ⟨k, (Fib_differsInOne π hinj a b k).mp hk⟩

/-! ## Part 2: the automorphism law, carrier-general -/

/-- **THE LAW.** A fibre-preserving injection fixes an assembly exactly when it fixes each FACTOR off that
factor's own diagonal, and fixes the IMPORT on the cross region. The two clauses are of different shapes: the
factor clause is a conjunction of per-coordinate conditions, each mentioning one factor and one coordinate map;
the import clause is a single global condition on the whole tuple. -/
theorem fib_fixes_iff [∀ k, Inhabited (X k)] (π : ∀ k, X k → X k)
    (hinj : ∀ k, Function.Injective (π k)) (c : ∀ k, X k → X k → Option Bool)
    (imp : Pt X → Pt X → Option Bool) :
    relabel (Fib π) (nary c imp) = nary c imp
      ↔ ((∀ (k : Fin n) (x y : X k), x ≠ y → c k (π k x) (π k y) = c k x y)
          ∧ (∀ a b : Pt X, IsCross a b → imp (Fib π a) (Fib π b) = imp a b)) := by
  constructor
  · intro h
    constructor
    · intro k x y hxy
      set a : Pt X := Function.update (fun j => (default : X j)) k x with ha
      set b : Pt X := Function.update (fun j => (default : X j)) k y with hb
      have hd : differsInOne a b k := by
        refine ⟨?_, fun j hj => ?_⟩
        · rw [ha, hb]; simp only [Function.update_self]; exact hxy
        · rw [ha, hb]; simp only [Function.update_of_ne hj]
      have hd' : differsInOne (Fib π a) (Fib π b) k := (Fib_differsInOne π hinj a b k).mpr hd
      have hcell : nary c imp (Fib π a) (Fib π b) = nary c imp a b := congrFun (congrFun h a) b
      rw [nary_apply_differ c imp hd', nary_apply_differ c imp hd] at hcell
      have hax : a k = x := by rw [ha]; simp
      have hbk : b k = y := by rw [hb]; simp
      rw [Fib_apply, Fib_apply, hax, hbk] at hcell
      exact hcell
    · intro a b hcr
      have hcell : nary c imp (Fib π a) (Fib π b) = nary c imp a b := congrFun (congrFun h a) b
      rw [nary_apply_imp c imp ((Fib_cross π hinj a b).mpr hcr), nary_apply_imp c imp hcr] at hcell
      exact hcell
  · rintro ⟨hc, himp⟩
    funext a b
    show nary c imp (Fib π a) (Fib π b) = nary c imp a b
    by_cases hex : ∃ k, differsInOne a b k
    · obtain ⟨k, hk⟩ := hex
      have hk' : differsInOne (Fib π a) (Fib π b) k := (Fib_differsInOne π hinj a b k).mpr hk
      rw [nary_apply_differ c imp hk', nary_apply_differ c imp hk, Fib_apply, Fib_apply]
      exact hc k (a k) (b k) hk.1
    · rw [nary_apply_imp c imp ((Fib_cross π hinj a b).mpr hex), nary_apply_imp c imp hex]
      exact himp a b hex

/-- **The factor clause is coordinatewise: no factor constrains any other coordinate's map.** Replacing every
factor except the one at `k` leaves the condition at `k` untouched. -/
theorem factor_condition_is_local (c c' : ∀ k, X k → X k → Option Bool) (π : ∀ k, X k → X k)
    (k : Fin n) (h : c k = c' k) :
    (∀ x y : X k, x ≠ y → c k (π k x) (π k y) = c k x y)
      ↔ (∀ x y : X k, x ≠ y → c' k (π k x) (π k y) = c' k x y) := by rw [h]

/-- **When nothing constrains, every fibre-preserving injection is an automorphism.** If each factor is
off-diagonally invariant under every coordinate injection and the import is invariant under every
fibre-preserving injection, the fibre-preserving automorphism group is the FULL product of the coordinate
symmetry groups. On a finite carrier its order is the product of the factorials of the fibre sizes: the general
LAW behind the measured count, which is a product of per-coordinate symmetries and not a fixed number. -/
theorem full_product_when_unconstrained [∀ k, Inhabited (X k)]
    (c : ∀ k, X k → X k → Option Bool) (imp : Pt X → Pt X → Option Bool)
    (hc : ∀ (k : Fin n) (ρ : X k → X k), Function.Injective ρ →
      ∀ x y : X k, x ≠ y → c k (ρ x) (ρ y) = c k x y)
    (himp : ∀ ρ : ∀ k, X k → X k, (∀ k, Function.Injective (ρ k)) →
      ∀ a b : Pt X, IsCross a b → imp (Fib ρ a) (Fib ρ b) = imp a b)
    (π : ∀ k, X k → X k) (hinj : ∀ k, Function.Injective (π k)) :
    relabel (Fib π) (nary c imp) = nary c imp :=
  (fib_fixes_iff π hinj c imp).mpr
    ⟨fun k x y hxy => hc k (π k) (hinj k) x y hxy, himp π hinj⟩

/-- **CORRECTION ONE, carrier-general: a FACTOR can exclude a fibre-preserving map.** If the factor at `k`
fails to be fixed off its diagonal, the map is not an automorphism, whatever the import does. So the reading
"the factors cannot break the symmetry" is false as stated; what is true is the weaker and sharper statement
above, that a factor constrains only its OWN coordinate. -/
theorem factor_can_exclude [∀ k, Inhabited (X k)] (π : ∀ k, X k → X k)
    (hinj : ∀ k, Function.Injective (π k)) (c : ∀ k, X k → X k → Option Bool)
    (imp : Pt X → Pt X → Option Bool) (k : Fin n) (x y : X k) (hxy : x ≠ y)
    (h : c k (π k x) (π k y) ≠ c k x y) :
    relabel (Fib π) (nary c imp) ≠ nary c imp := by
  intro hfix
  exact h (((fib_fixes_iff π hinj c imp).mp hfix).1 k x y hxy)

/-! ## Part 3: the import is the only cross-coordinate constraint -/

/-- **The import can exclude a map**, carrier-general, by failing to be fixed on a single cross cell. -/
theorem import_can_exclude [∀ k, Inhabited (X k)] (π : ∀ k, X k → X k)
    (hinj : ∀ k, Function.Injective (π k)) (c : ∀ k, X k → X k → Option Bool)
    (imp : Pt X → Pt X → Option Bool) (a b : Pt X) (hcr : IsCross a b)
    (h : imp (Fib π a) (Fib π b) ≠ imp a b) :
    relabel (Fib π) (nary c imp) ≠ nary c imp := by
  intro hfix
  exact h (((fib_fixes_iff π hinj c imp).mp hfix).2 a b hcr)

/-- An import that marks a single point on the diagonal. -/
def impPoint [DecidableEq (Pt X)] (p : Pt X) : Pt X → Pt X → Option Bool :=
  fun a b => if a = b ∧ a = p then some true else none

/-- **THE OTHER HALF, carrier-general: the import alone can exclude a map every factor tolerates.** With all
factors all-absent, so that the factor clause is satisfied by every coordinate map, an import marking one point
excludes exactly the maps that move it. The cross-coordinate cut is the import's and only the import's. -/
theorem import_alone_can_pin [∀ k, Inhabited (X k)] [DecidableEq (Pt X)] (π : ∀ k, X k → X k)
    (hinj : ∀ k, Function.Injective (π k)) (p : Pt X) (hmove : Fib π p ≠ p) :
    (∀ (k : Fin n) (x y : X k), x ≠ y →
        botC (X k) (π k x) (π k y) = botC (X k) x y)
      ∧ relabel (Fib π) (nary (fun k => botC (X k)) (impPoint p))
          ≠ nary (fun k => botC (X k)) (impPoint p) := by
  refine ⟨fun _ _ _ _ => rfl, ?_⟩
  refine import_can_exclude π hinj _ (impPoint p) p p (by rintro ⟨k, hk, _⟩; exact hk rfl) ?_
  show (if Fib π p = Fib π p ∧ Fib π p = p then some true else none)
    ≠ (if p = p ∧ p = p then some true else none)
  rw [if_neg (fun hcon => hmove hcon.2), if_pos ⟨rfl, rfl⟩]
  exact fun hcon => absurd hcon.symm (Option.some_ne_none true)

end General

/-! ## Part 1 (continued): the proposed containment is REFUTED

The lift also corrects the claim that every automorphism of an assembly is fibre-preserving. It is not: an
assembly that cannot tell one region from the cross admits automorphisms that MIX coordinates. -/

abbrev Q2 := ∀ _ : Fin 2, Fin 2


theorem mk2_factor0 (c0 c1 : Fin 2 → Fin 2 → Option Bool) (imp : Q2 → Q2 → Option Bool) :
    IsFactorAt 0 (mk2 c0 c1 imp) c0 := by
  intro a b hd
  have h0 : a 0 ≠ b 0 := hd.1
  have h1 : a 1 = b 1 := hd.2 1 (by decide)
  simp [mk2, h0, h1]

theorem mk2_factor1 (c0 c1 : Fin 2 → Fin 2 → Option Bool) (imp : Q2 → Q2 → Option Bool) :
    IsFactorAt 1 (mk2 c0 c1 imp) c1 := by
  intro a b hd
  have h1 : a 1 ≠ b 1 := hd.1
  have h0 : a 0 = b 0 := hd.2 0 (by decide)
  simp [mk2, h1, h0]

def gC : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none
def qC : Fin 2 → Fin 2 → Option Bool := fun x y => some (decide (x = y))
def impD : Q2 → Q2 → Option Bool := fun a b => if a = b then some true else none

def Agq : Q2 → Q2 → Option Bool := mk2 gC qC impD

/-- A map that acts on the second coordinate DIFFERENTLY in each first-coordinate fibre: it mixes
coordinates, so it is not of the form `Fib`. -/
def wreath : Q2 → Q2 := fun a => fun i => if i = 0 then a 0 else (if a 0 = 0 then a 1 else a 1 + 1)

theorem wreath_not_fibre_preserving :
    (![0, 0] : Q2) 1 = (![1, 0] : Q2) 1 ∧ wreath ![0, 0] 1 ≠ wreath ![1, 0] 1 := by
  refine ⟨by decide, by decide⟩

/-- **REFUTATION.** The wreath map fixes this assembly, so it is an automorphism, and it carries a region-0
pair off region 0. So NOT every automorphism of an assembly is fibre-preserving: the containment proposed for
Part 1 fails. The reason is visible in the witness: this assembly is absent on every region-0 cell AND on every
differ-in-both cell, so it cannot tell the two apart, and a map exchanging them goes undetected. -/
theorem automorphism_need_not_be_fibre_preserving :
    (∀ a b : Q2, Agq (wreath a) (wreath b) = Agq a b)
      ∧ differsInOne (![0, 0] : Q2) ![1, 0] 0
      ∧ ¬ differsInOne (wreath ![0, 0]) (wreath ![1, 0]) 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## THE VERDICTS

PART 1: the action and the regions, with the proposed containment REFUTED.

`Fib` is the carrier-general fibre-preserving map, built coordinatewise. `Fib_differsInOne` and `Fib_cross`
show a fibre-preserving injection preserves every region and the cross setwise, in both directions, at every
carrier.

But the proposed containment, that every automorphism is fibre-preserving on the regions, is FALSE.
`automorphism_need_not_be_fibre_preserving` exhibits a coordinate-mixing map that fixes an assembly and carries
a region-0 pair off region 0. The reason is legible: that assembly abstains on every region-0 cell AND on every
differ-in-both cell, so it cannot distinguish them, and the mixing goes undetected. The measured count of eight
was counting such maps. So the count does NOT generalize, and it was not counting fibre-preserving maps.

PART 2: the law, carrier-general, and the correction it forces.

`fib_fixes_iff` is the theorem the thread needed. A fibre-preserving injection fixes an assembly exactly when
it fixes each FACTOR off that factor's own diagonal AND fixes the IMPORT on the cross region. Carrier-general,
uniform in `n`, no finiteness.

The two clauses have different shapes and that is the content. The factor clause is a conjunction of
PER-COORDINATE conditions, each mentioning one factor and one coordinate map, so `factor_condition_is_local`
holds: no factor constrains any other coordinate's map. The import clause is a SINGLE GLOBAL condition on the
whole tuple.

CORRECTION ONE. The reading "the factors cannot break the symmetry" is FALSE as stated.
`factor_can_exclude` shows, carrier-generally, that a factor failing to be fixed off its own diagonal excludes
the map whatever the import does. What survives is the sharper statement: a factor constrains ONLY ITS OWN
COORDINATE, and can say nothing about any other. The earlier measurement did not see this because both of its
factors happened to be invariant under every permutation of a two-element fibre.

THE ORDER LAW, replacing the count. `full_product_when_unconstrained`: when each factor is off-diagonally
invariant under every coordinate injection and the import is invariant under every fibre-preserving injection,
EVERY fibre-preserving injection is an automorphism, so the fibre-preserving automorphism group is the full
product of the coordinate symmetry groups. On a finite carrier its order is the product of the factorials of
the fibre sizes. The law is a PRODUCT OF PER-COORDINATE SYMMETRIES; the number eight was carrier-specific and
was moreover inflated by the coordinate-mixing maps Part 1 refutes.

PART 3: the import is the only cross-coordinate constraint, carrier-general.

`import_can_exclude` shows the import can exclude a map by failing at a single cross cell.
`import_alone_can_pin` gives the separation: with all factors all-absent, so that the factor clause is
satisfied by EVERY coordinate map, an import marking one point excludes exactly the maps that move it. So the
cross-coordinate cut is the import's and only the import's.

The clean statement the thread needs is `fib_fixes_iff` read structurally: GIVEN THE CARRIER, the
fibre-preserving automorphism group is cut by per-coordinate factor conditions and ONE global import condition.
Symmetry across coordinates is a property of the import; symmetry within a coordinate is a property of that
coordinate's factor. That is the middle clause of the chain, now a theorem, and it is finer than the version it
replaces: the factors are not symmetry-blind, they are symmetry-blind ACROSS COORDINATES.

PART 4: the merge surface, flagged for a later graduation pass. No graph run here.

REUSES, and would merge with:

  `nary_apply_differ`, `nary_apply_imp` (canonical, `Model/NaryAssemblage`) are the only canonical lemmas the
  main proof calls. The dependency surface is thin.

  `differsInOne` and its uniqueness (canonical). `Fib_differsInOne` is a new fact about it and belongs beside
  `nary_region_independent` if it graduates.

  `relabel` duplicates the local copies in `CombinedCategory`, `CombinedArrows`, `ScaleIndependence` and
  `ArcReadiness`. FIVE copies now exist across live files; exactly one must survive, and `CombinedCategory`'s
  is the grounded one.

  `mk2` duplicates the computable assembly former in `AssemblageCoordinates` and `AsymmetricCone`.

DOES NOT reuse, though a reader might expect it to: `factor_region_absent_count`, the `glue` bijections, and
the region-count machinery of `AssemblageCoordinates` play no part. This law is about VALUES at region cells,
not about counting them, so the coordinate-space machinery is not on its dependency surface.

WHAT REMAINS OPEN

1. `fib_fixes_iff` characterizes the FIBRE-PRESERVING automorphisms. The full automorphism group is larger, as
   Part 1 shows, and is not characterized here. The extra maps arise where the assembly cannot separate a
   region from the cross, which suggests a separation hypothesis would close the gap; not proved.
2. The order law is stated as a set equality. The cardinality form, a product of factorials, is immediate on a
   finite carrier but is not formalized.
3. `import_alone_can_pin` uses all-absent factors to isolate the import's contribution. Whether an import can
   pin the group to the identity over ARBITRARY factors, and on which carriers, is not settled: the three
   available cell values bound how many points a diagonal import can distinguish. -/

#print axioms Fib_apply
#print axioms Fib_differsInOne
#print axioms Fib_cross
#print axioms fib_fixes_iff
#print axioms factor_condition_is_local
#print axioms full_product_when_unconstrained
#print axioms factor_can_exclude
#print axioms import_can_exclude
#print axioms import_alone_can_pin
#print axioms mk2_factor0
#print axioms mk2_factor1
#print axioms wreath_not_fibre_preserving
#print axioms automorphism_need_not_be_fibre_preserving

end Chiralogy.AssemblySymmetry
