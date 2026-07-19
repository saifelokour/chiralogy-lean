import Chiralogy

/-! # Experiment: are the two arms one index split by arity?

The apophatic index is nullary generators (constants, arity 0); the cataphatic index is forgetful functors,
one free construction each. Hypothesis: these are one signature split by arity, the apophatic reading arity 0,
the cataphatic reading positive arity. A signature is symbols with arities; a nullary operation is a
distinguished point, which is `maybe_free_pointed`. The known seam: enriched universal algebra covers metric
spaces and posets, so a metric is algebraic only under enrichment, not in a plain signature.

Concrete instances, canonical witnesses. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.ArityIndex

/-! ## Part 1: do the cataphatic witnesses correspond to positive-arity operations? -/

/-- **The witnesses split by algebraicity.** Monoid (composition, binary), group (inverses, unary), and
vector (linearity) are plain-signature operations into the carrier: `compose` is associative on `List Bool`,
`groupInverse` lands in `ℤ`, `scale` in `ℤ × ℤ`. Metric (`hamming3`), measure (`magnitude`), and order
(`less`) land in external types (`ℕ`, `ℕ`, `Bool`), not the carrier: they are not operations `X^n → X` but
maps into a valued or relational structure, algebraic only under enrichment. -/
theorem witnesses_split_by_algebraicity :
    (compose (compose [true] [false]) [true] = compose [true] (compose [false] [true]))
    ∧ (groupInverse 1 = 0)
    ∧ (scale (1, 0) = (2, 0))
    ∧ (hamming3 (false, false, false) (true, true, true) = 3)
    ∧ (magnitude (-1 : ℤ) = 1)
    ∧ (less 0 1 = true) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Part 2: does the apophatic side sit at arity 0 of the same signature? -/

/-- **Reasons are the arity-0 symbols.** Restating `reasons_are_nullary_generators` in signature terms:
Maybe's reason is the single arity-0 symbol `fail`, Except's are the arity-0 symbols `throw e`. -/
theorem reasons_are_arity_zero :
    (∀ x : Bool ⊕ Bool, (∃ e, x = Sum.inr e) ↔ ∃ e, throwExcept e = x)
    ∧ (∀ v : Option Bool, v = none ↔ ∃ u : Unit, failMaybe u = v) :=
  reasons_are_nullary_generators

/-- Append on a list-with-failure: the zero (absence) absorbs, the monoid operates on the present part. -/
def mzAppend : Option (List Bool) → Option (List Bool) → Option (List Bool)
  | none, _ => none
  | _, none => none
  | some a, some b => some (a ++ b)

/-- **One signature at two arities.** The list-with-failure level's theory is monoids-with-zero: the constant
`none` (arity 0, the absorbing zero, the apophatic reason) and the binary `mzAppend` (arity 2, the cataphatic
monoid operation) inhabit one signature on one value space, at different arities. The gate holds: both are
operations of the same theory, not two theories compared. -/
theorem same_signature_different_arity :
    (∀ x : Option (List Bool), mzAppend none x = none)
    ∧ mzAppend (some [true]) (some [false]) = some [true, false] :=
  ⟨fun _ => rfl, rfl⟩

/-! ## Part 3: the verdict on the asymmetry -/

/-- **The apparent one-inversion asymmetry is a level confusion.** The cataphatic model has plural operations
(the witnesses), as the apophatic model has plural reasons (`throw false ≠ throw true`); both kernels are a
single move. The asymmetry named, cataphatic one inversion against apophatic plural reasons, compares the
cataphatic kernel to the apophatic model, different levels. Like for like there is no asymmetry, so neither
reading needs to account for one. -/
theorem cataphatic_kernel_one_inversion_explained :
    (compose [true] [false] = [true, false] ∧ groupInverse 1 = 0 ∧ scale (1, 0) = (2, 0))
    ∧ (∃ e e' : Bool, throwExcept e ≠ throwExcept e') := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨false, true, by decide⟩⟩

/-! ## The verdict

Part 1: the cataphatic witnesses split. Monoid, group, and vector are plain-signature operations into the
carrier (positive arity); metric, measure, and order land in external types, not the carrier, and are
algebraic only under enrichment or as relations, not in a plain signature (`witnesses_split_by_algebraicity`).
The predicted seam is real and named.

Part 2: the apophatic reasons are the arity-0 symbols (`reasons_are_arity_zero`), and for the algebraic
witnesses they share a signature with the positive-arity operations: the list-with-failure level carries the
constant `none` and the binary `mzAppend` in one theory, monoids-with-zero, at arities 0 and 2
(`same_signature_different_arity`). The gate holds: one signature, not two.

Part 3: the asymmetry is arity, for the algebraic part. The apophatic constants (arity 0) and the algebraic
cataphatic operations (positive arity) are one signature split by arity, so 5.c.1's asymmetry there is arity,
not kind, and the distinguished base is the theory with exactly one arity-0 symbol and nothing else, Maybe.
But the enriched witnesses (metric, measure, order) do not join that signature: they are a different kind,
outside plain algebra. So it is one index split by arity for the algebraic witnesses, and a genuinely
different index for the enriched ones. The one-inversion fact is not an asymmetry the reading must explain
(`cataphatic_kernel_one_inversion_explained`): both kernels are one, both models plural.

The verdict: partly one index split by arity, partly two. The apophatic constants and the algebraic cataphatic
operations are one signature at arities 0 and positive; the enriched cataphatic witnesses (metric, magnitude,
order) are not signature operations at all, and index a different, enriched structure. The asymmetry of 5.c.1
is arity where the cataphatic side is algebraic and kind where it is enriched. Nothing here is resolved. -/

end Chiralogy.ArityIndex
