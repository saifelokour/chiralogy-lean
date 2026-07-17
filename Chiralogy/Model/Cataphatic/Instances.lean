import Chiralogy.Model.Cataphatic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

/-! # Model: the borrowed fillings of the cataphatic skeleton

The free skeleton (`Model/Cataphatic.lean`) is parameterized over any ambient with a surplus. Here are the
borrowed fillings: the four registers, each instantiating the skeleton at a specific ambient with its own
surplus, and the target-dependence demonstrations that show the specific ambient matters (their concreteness
is their content, so they are not parameterized). The measure register is ● BORROWED: the framework hosts
measures, it does not own magnitude. -/

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

/-- The three bought-operations side by side: a field, a metric, an order. Three forgetful functors, three
independent cataphatic models. -/
theorem three_independent_bought_operations :
    arithmetic_register_conforms.T = ZMod 3 ∧
      hamming3 (ecc_register.build false) (ecc_register.build true) = 3 ∧
      less (order_register.build false) (order_register.build true) = true :=
  ⟨rfl, ecc_buys_distance, by decide⟩

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

end Chiralogy
