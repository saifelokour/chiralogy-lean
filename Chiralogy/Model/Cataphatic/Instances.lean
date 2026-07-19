import Chiralogy.Model.Cataphatic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice
import Mathlib.Algebra.Module.Basic
import Mathlib.Topology.MetricSpace.Basic

/-! # Model: the borrowed fillings of the cataphatic skeleton

The free skeleton (`Model/Cataphatic.lean`) is parameterized over any ambient with a surplus. Here are the
borrowed fillings: the four registers, each instantiating the skeleton at a specific ambient with its own
surplus, and the target-dependence demonstrations that show the specific ambient matters (their concreteness
is their content, so they are not parameterized). The measure register is ● BORROWED: the framework hosts
measures, it does not own magnitude. The conformance form reads only a build, so the algebraic/enriched split
is a classification of the seven witnesses, not something the form registers (`cataphatic_form_reads_only_a_build`);
the form distinguishes no two witnesses at all (`form_distinguishes_nothing`), so every classification is ours. -/

namespace Chiralogy

/-- **The surplus `ZMod 3` buys.** A point beyond {0, 1}, the evaluation point for algebraic spot-checking
the source lacks. This is the witness that instantiates the skeleton at `ZMod 3`. -/
theorem embedding_buys_in_rich_ambient : ∃ a : ZMod 3, a ≠ 0 ∧ a ≠ 1 :=
  ⟨2, by decide, by decide⟩

/-- **The trivial ambient buys nothing.** `ZMod 2` is Boolean, no point beyond {0, 1}: the gain is
target-dependent, which is why this concreteness cannot be parameterized away. -/
theorem embedding_buys_nothing_in_trivial : ¬ ∃ a : ZMod 2, a ≠ 0 ∧ a ≠ 1 := by decide

/-- **Arithmetization conforms.** Carrier `Bool`, ambient the field `ZMod 3`, build `embed`; it buys
algebraic-checking. -/
def arithmetic_register_conforms : CataphaticConformant := ⟨Bool, ZMod 3, embed (ZMod 3)⟩

/-- Arithmetization fills the skeleton: the free/forget chiasm holds at `ZMod 3`, from its surplus. -/
theorem arithmetic_cataphatic_chiasm :
    (∀ b : Bool, restrict (embed (ZMod 3) b) = b) ∧
      (∃ a : ZMod 3, embed (ZMod 3) (restrict a) ≠ a) ∧ ¬ Function.Surjective (embed (ZMod 3)) :=
  cataphatic_model_chiasm (F := ZMod 3) (by decide) embedding_buys_in_rich_ambient

/-- Error-correcting code: ambient the 3-repetition codeword space `Bool × Bool × Bool`, a product with a
Hamming metric, not a field. -/
def ecc_register : CataphaticConformant := ⟨Bool, Bool × Bool × Bool, fun b => (b, b, b)⟩

/-- The Hamming distance on the codeword ambient: the metric the message space lacks. -/
def hamming3 (a b : Bool × Bool × Bool) : Nat :=
  (if a.1 = b.1 then 0 else 1) + (if a.2.1 = b.2.1 then 0 else 1) + (if a.2.2 = b.2.2 then 0 else 1)

/-- **ECC buys distance, independent of arithmetization.** Distinct messages encode to codewords at
Hamming distance 3: a metric operation on a product ambient, not field-arithmetic. -/
theorem ecc_buys_distance : hamming3 (ecc_register.build false) (ecc_register.build true) = 3 := by decide

/-- A third free construction: build a bit into an ordered ambient. -/
def order_register : CataphaticConformant := ⟨Bool, ℕ, fun b => if b then 1 else 0⟩

/-- Comparison, forcing the ambient to reduce to `ℕ`. -/
def less (a b : ℕ) : Bool := decide (a < b)

/-- **Order buys comparison, a third independent operation.** The two built points are ordered:
distinct from field-arithmetic and from Hamming distance. -/
theorem order_buys_comparison :
    less (order_register.build false) (order_register.build true) = true := by decide

/-- The measure level, one more BORROWED nested construction: build into a magnitude-carrying ambient. -/
def measure_register : CataphaticConformant := ⟨Bool, ℤ, fun b => if b then 1 else -1⟩

/-- Magnitude (`natAbs`): both built values have magnitude one, so measurement collapses the order. -/
def magnitude (z : ℤ) : ℕ := z.natAbs

/-- **Measure is hosted, ● borrowed.** The bought-operation is magnitude, borrowed exactly as the field, the
metric, and the order are borrowed: the framework hosts measures, it does not own magnitude. -/
theorem measure_hosts_magnitude :
    magnitude (measure_register.build true) = 1 ∧ magnitude (measure_register.build false) = 1 := by decide

/-- Level one: a bit into a field. -/
def tower1 : Bool → ZMod 3 := embed (ZMod 3)

/-- Level two: the field into a field-with-order, a different richer structure. -/
def tower2 : ZMod 3 → ZMod 3 × ℕ := fun x => (x, 0)

/-- **The tower nests.** Each level is a genuine containment (injective build-outward), the levels
heterogeneous (a field, then a field with an order coordinate). -/
theorem tower_nests : Function.Injective tower1 ∧ Function.Injective tower2 :=
  ⟨Function.LeftInverse.injective (g := restrict) (restrict_embed_id (F := ZMod 3) (by decide)),
   fun _ _ h => congrArg Prod.fst h⟩

/-- The composite free move, two levels of build-outward. -/
def embedComp : Bool → ZMod 3 × ℕ := fun b => (embed (ZMod 3) b, 0)

/-- The composite forget move, two levels dropped. -/
def restrictComp : ZMod 3 × ℕ → Bool := fun p => restrict p.1

/-- **The nested chiasms telescope.** The composite is again a free/forget chiasm, composing by
containment (dual to the apophatic non-composition: sections compose, absences do not). -/
theorem telescopes :
    (∀ b, restrictComp (embedComp b) = b) ∧ (∃ p, embedComp (restrictComp p) ≠ p) :=
  ⟨fun b => restrict_embed_id (F := ZMod 3) (by decide) b, ⟨(2, 0), by decide⟩⟩

/-- The composite center contains the level-one center: the level-one surplus `2`, carried to `(2, 0)`, is
unreached by the composite embedding. -/
theorem level1_center_in_composite : ¬ ∃ b, embedComp b = ((2 : ZMod 3), (0 : ℕ)) := by decide

/-- The apophatic model primitive is a genuine monad on `Type`. -/
example : Monad Option := inferInstance

/-- **The loop does not close.** The apophatic monad `Option` and the cataphatic free construction `embed`
are different forgetful functors (pointed versus field), two adjunctions, not the two triangles of one:
resemblance, not identity. -/
theorem loop_does_not_close :
    Nonempty (Monad Option) ∧ ¬ Function.Surjective (embed (ZMod 3)) :=
  ⟨⟨inferInstance⟩, embedding_not_iso embedding_buys_in_rich_ambient⟩

/-! ## Witness census: further candidate forgetful steps

Independence is per bought-operation, not per structure: a candidate is a new witness only if its
bought-operation is genuinely new (not field-arithmetic, distance, comparison, or magnitude, and not a
refinement of one). Everything conforms (the loose gate); only new bought-operations count. -/

/-- Monoid: the ambient is the free monoid `List Bool`, the build is the generator inclusion. -/
def monoid_register : CataphaticConformant := ⟨Bool, List Bool, fun b => [b]⟩

/-- The composition the monoid ambient carries: an associative binary op the source lacked. -/
def compose (a b : List Bool) : List Bool := a ++ b

/-- **Monoid buys composition** (new): two generators compose into a word outside the generator image. -/
theorem monoid_buys_composition :
    compose (monoid_register.build true) (monoid_register.build false) = [true, false] := rfl

/-- Group: the ambient `ℤ`, nested above the monoid (a group is a monoid with inverses). -/
def group_register : CataphaticConformant := ⟨Bool, ℤ, fun b => if b then 1 else 0⟩

/-- The inverse the group ambient carries: `a` composed with its negation. -/
def groupInverse (a : ℤ) : ℤ := a + -a

/-- **Group buys inverses** (new, the step above composition): every element has an inverse, so a generator
composed with its negation is the unit. -/
theorem group_buys_inverses : groupInverse (group_register.build true) = 0 := by decide

/-- Vector: the ambient is the free module `ℤ × ℤ`, the build is the basis inclusion. -/
def vector_register : CataphaticConformant := ⟨Bool, ℤ × ℤ, fun b => if b then (1, 0) else (0, 1)⟩

/-- The scalar action the module ambient carries. -/
def scale (v : ℤ × ℤ) : ℤ × ℤ := (2 : ℤ) • v

/-- **Vector buys linearity** (new): scalar multiplication and linear combinations (superposition) exist,
none of field-arithmetic, distance, comparison, or magnitude. -/
theorem vector_buys_linearity : scale (vector_register.build true) = (2, 0) := by decide

/-- **Lattice collapses to the order-family.** A meet is inter-definable with comparison
(`a ≤ b ↔ a ⊓ b = a`): its bought-operation is order in another form, not independent. -/
theorem lattice_collapses_to_order {L : Type} [SemilatticeInf L] (a b : L) :
    a ≤ b ↔ a ⊓ b = a := inf_eq_left.symm

/-- **Continuity collapses to the metric-family.** In a metric space, sequence convergence is distance
convergence, `u → L` iff `dist (u n) L → 0`: the limit is carried by distance, already witnessed by the
metric register, so continuity via a metric buys nothing new. -/
theorem continuity_collapses_to_metric {X : Type} [MetricSpace X] (u : ℕ → X) (L : X) :
    Filter.Tendsto u Filter.atTop (nhds L) ↔
      Filter.Tendsto (fun n => dist (u n) L) Filter.atTop (nhds 0) :=
  tendsto_iff_dist_tendsto_zero

/-! ## Collapses and exclusions

Continuity has no independent witness. A genuine (unique) limit needs the clean metric case, where
convergence is distance convergence (`continuity_collapses_to_metric`): metric-family. The non-metric routes
fail too: a finite topology is its specialization order (order-family), and a non-metric infinite topology
(cofinite) gives non-unique convergence, not a genuine limit. So continuity is distance or comparison in
another form, recorded, not counted. Nothing provisional remains.

Cofree constructions (right adjoints, comonads) are apophatic-shaped: the fold and observation side, the dual
of the `Maybe`-monad, not cataphatic build-witnesses. They are not counted here.

## The tower

Nested (the algebraic tower `Set → Monoid → Group`): composition then inverses, each a forgetful step above
the last (as `tower_nests` and `telescopes` nest). Parallel (different forgetful functors, not one tower):
field, metric, order, magnitude, linearity. -/

/-- **All independent bought-operations**, side by side: field, metric, order, magnitude, composition,
inverses, linearity. Seven independent witnesses (was four): lattice collapses to order, continuity collapses
to metric, cofree is apophatic-shaped. -/
theorem all_independent_bought_operations :
    (∃ a : ZMod 3, a ≠ 0 ∧ a ≠ 1) ∧
      hamming3 (ecc_register.build false) (ecc_register.build true) = 3 ∧
      less (order_register.build false) (order_register.build true) = true ∧
      magnitude (measure_register.build true) = 1 ∧
      compose (monoid_register.build true) (monoid_register.build false) = [true, false] ∧
      groupInverse (group_register.build true) = 0 ∧
      scale (vector_register.build true) = (2, 0) :=
  ⟨embedding_buys_in_rich_ambient, ecc_buys_distance, order_buys_comparison,
   measure_hosts_magnitude.1, monoid_buys_composition, group_buys_inverses, vector_buys_linearity⟩

/-! ## The openness principle (● reading)

The witnesses are the forgetful functors, one bought-operation per forgetful step. Freyd's GAFT gives a free
construction per suitable forgetful functor, and algebraic theories are open-ended, so the list is open, not
a fixed enumeration: the seven verified are a finite sample of an open family. The apophatic register
instantiates a domain; the cataphatic witness fills an ambient slot (a forgetful functor). Marked ●, Freyd
plus open structures, not a formalized enumeration. -/

/-! ## The arity split: which witnesses are signature operations

Checked at the instances, not proven as a general signature theorem. -/

/-- **The witnesses split by algebraicity.** Four buy plain-signature operations into the carrier: monoid
composition (binary, `compose` associative on `List Bool`), group inverses (`groupInverse` into `ℤ`), vector
linearity (`scale` into `ℤ × ℤ`), and field ring operations. Three buy maps into external valued or relational
structures: metric distance (`hamming3` into `ℕ`), measure magnitude (`magnitude` into `ℕ`), order comparison
(`less` into `Bool`), which are operations `X^n → X` only under enrichment. -/
theorem witnesses_split_by_algebraicity :
    (compose (compose [true] [false]) [true] = compose [true] (compose [false] [true]))
    ∧ (groupInverse 1 = 0)
    ∧ (scale (1, 0) = (2, 0))
    ∧ (hamming3 (false, false, false) (true, true, true) = 3)
    ∧ (magnitude (-1 : ℤ) = 1)
    ∧ (less 0 1 = true) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- A register valued in a non-posetal hom-object: the `ℤ`-module endomorphisms, an object of `Ab`. -/
def homValuedRegister : CataphaticConformant :=
  ⟨Bool, ℤ →+ ℤ, fun b => if b then AddMonoidHom.id ℤ else 0⟩

/-- **The cataphatic form reads only a build.** The form asks for a carrier, an ambient, and a build; it
distinguishes neither signature operations from enriched homs nor posetal bases from others. A witness valued
in a non-posetal hom-object conforms (the base `ℤ →+ ℤ` is not thin, two distinct parallel maps `id`, `0`), so
the algebraic/enriched split of `witnesses_split_by_algebraicity` is a classification of the seven exhibited,
invisible to the gate. -/
theorem cataphatic_form_reads_only_a_build :
    homValuedRegister.X = Bool ∧ (AddMonoidHom.id ℤ ≠ (0 : ℤ →+ ℤ)) := by
  refine ⟨rfl, fun h => ?_⟩
  have := DFunLike.congr_fun h 1
  simp at this

/-- **The form distinguishes nothing.** The cataphatic form is loose: every type is the carrier of some
conformant, and two witnesses differing in carrier, ambient, and build are both conformant with no test
separating them. The witness family is undifferentiated from the framework's side, so every classification of
it, the algebraic/enriched split included, is imposed from outside. -/
theorem form_distinguishes_nothing :
    (∀ X : Type, ∃ cc : CataphaticConformant, cc.X = X)
    ∧ (⟨Bool, Bool, id⟩ : CataphaticConformant).X = Bool
    ∧ (⟨Fin 3, ℕ, fun _ => (0 : ℕ)⟩ : CataphaticConformant).X = Fin 3 :=
  ⟨fun X => cataphatic_is_loose X, rfl, rfl⟩

/-- Append on a list-with-failure: the zero absorbs, the monoid operates on the present part. -/
def mzAppend : Option (List Bool) → Option (List Bool) → Option (List Bool)
  | none, _ => none
  | _, none => none
  | some a, some b => some (a ++ b)

/-- **One signature at two arities.** For the algebraic witnesses the apophatic reason and the cataphatic
operation inhabit one signature. The list-with-failure level is a monoid-with-zero: the absorbing constant
`none` (arity 0, the reason) and the binary `mzAppend` (the bought operation) live on one value space, not two
theories compared. -/
theorem same_signature_different_arity :
    (∀ x : Option (List Bool), mzAppend none x = none)
    ∧ mzAppend (some [true]) (some [false]) = some [true, false] :=
  ⟨fun _ => rfl, rfl⟩

end Chiralogy
