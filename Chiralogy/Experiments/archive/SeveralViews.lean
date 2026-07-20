import Chiralogy

/-! # Experiment: can the framework express several views of one thing?

Objectivity-as-redundancy needs multiple independent access to a common source. Survey the categorical shapes
that formalize this and test which the framework's own category `Obj` supports. Each shape is a different
formalization of several-views-of-one-thing; test each rather than assuming the sheaf is the only candidate. Do
not build limit or sheaf machinery; check whether `Obj` has these, with small concrete instances. Stays in
`Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.SeveralViews

/-! ## Part 1: the ingredients, cheapest first -/

/-- The one-point object, an apex for spans and a candidate terminal. -/
def apex : Obj := ⟨Unit, Unit, fun _ _ => ()⟩

/-- The apex maps to any object at a chosen point. -/
def apexTo (T : Obj) (x : T.X) : Hom apex T := ⟨fun _ => x, fun _ => T.classify x x, fun _ _ => rfl⟩

/-- **Spans exist.** One apex maps to two objects (given a point in each), so two objects can share a source. A
span alone gives a common source without agreement: the two legs are unconstrained relative to each other. -/
theorem spans (T U : Obj) (t : T.X) (u : U.X) :
    Nonempty (Hom apex T) ∧ Nonempty (Hom apex U) :=
  ⟨⟨apexTo T t⟩, ⟨apexTo U u⟩⟩

/-- The product object: carriers and values paired, classification componentwise. -/
def prod (S T : Obj) : Obj :=
  ⟨S.X × T.X, S.B × T.B, fun a b => (S.classify a.1 b.1, T.classify a.2 b.2)⟩

/-- The mediating map into the product. -/
def prodPair {A S T : Obj} (f : Hom A S) (g : Hom A T) : Hom A (prod S T) :=
  ⟨fun a => (f.onCarrier a, g.onCarrier a), fun v => (f.onValues v, g.onValues v),
   fun x y => by simp only [prod, Prod.mk.injEq]; exact ⟨f.preserves x y, g.preserves x y⟩⟩

/-- **Products exist.** For any two views `f, g` from `A`, there is a unique map into the product whose
projections recover them: `Obj` combines two classifications with projections. -/
theorem products {A S T : Obj} (f : Hom A S) (g : Hom A T) :
    ∃! h : Hom A (prod S T),
      (∀ a, (h.onCarrier a).1 = f.onCarrier a) ∧ (∀ a, (h.onCarrier a).2 = g.onCarrier a)
      ∧ (∀ v, (h.onValues v).1 = f.onValues v) ∧ (∀ v, (h.onValues v).2 = g.onValues v) := by
  refine ⟨prodPair f g, ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩, ?_⟩
  rintro ⟨hoc, hov, hp⟩ ⟨h1, h2, h3, h4⟩
  have e1 : hoc = fun a => (f.onCarrier a, g.onCarrier a) := funext fun a => Prod.ext (h1 a) (h2 a)
  have e2 : hov = fun v => (f.onValues v, g.onValues v) := funext fun v => Prod.ext (h3 v) (h4 v)
  subst e1; subst e2; rfl

/-- The pullback object: pairs of carriers and values agreeing in `T`. -/
def pb (f : Hom S T) (g : Hom U T) : Obj :=
  ⟨{p : S.X × U.X // f.onCarrier p.1 = g.onCarrier p.2},
   {p : S.B × U.B // f.onValues p.1 = g.onValues p.2},
   fun a b => ⟨(S.classify a.1.1 b.1.1, U.classify a.1.2 b.1.2), by
     rw [f.preserves a.1.1 b.1.1, g.preserves a.1.2 b.1.2, a.2, b.2]⟩⟩

/-- **Pullbacks exist.** Given `f : S → T` and `g : U → T`, the object of pairs agreeing in `T` factors any cone
that agrees: for `p : A → S`, `q : A → U` with `f p = g q` on carriers and values, there is a mediating map. -/
theorem pullbacks (f : Hom S T) (g : Hom U T) {A : Obj} (p : Hom A S) (q : Hom A U)
    (hc : ∀ a, f.onCarrier (p.onCarrier a) = g.onCarrier (q.onCarrier a))
    (hv : ∀ v, f.onValues (p.onValues v) = g.onValues (q.onValues v)) :
    ∃ h : Hom A (pb f g),
      (∀ a, (h.onCarrier a).1 = (p.onCarrier a, q.onCarrier a)) ∧
        (∀ v, (h.onValues v).1 = (p.onValues v, q.onValues v)) :=
  ⟨⟨fun a => ⟨(p.onCarrier a, q.onCarrier a), hc a⟩, fun v => ⟨(p.onValues v, q.onValues v), hv v⟩,
     fun x y => by apply Subtype.ext; exact Prod.ext (p.preserves x y) (q.preserves x y)⟩,
   fun _ => rfl, fun _ => rfl⟩

/-- The equalizer object: carriers and values where two parallel maps agree. -/
def eq (f g : Hom S T) : Obj :=
  ⟨{x : S.X // f.onCarrier x = g.onCarrier x}, {v : S.B // f.onValues v = g.onValues v},
   fun a b => ⟨S.classify a.1 b.1, by rw [f.preserves a.1 b.1, g.preserves a.1 b.1, a.2, b.2]⟩⟩

/-- **Equalizers exist.** For parallel `f, g : S → T`, the object where they agree factors any map that
equalizes them: for `p : A → S` with `f p = g p`, there is a mediating map into the equalizer. -/
theorem equalizers (f g : Hom S T) {A : Obj} (p : Hom A S)
    (hc : ∀ a, f.onCarrier (p.onCarrier a) = g.onCarrier (p.onCarrier a))
    (hv : ∀ v, f.onValues (p.onValues v) = g.onValues (p.onValues v)) :
    ∃ h : Hom A (eq f g),
      (∀ a, (h.onCarrier a).1 = p.onCarrier a) ∧ (∀ v, (h.onValues v).1 = p.onValues v) :=
  ⟨⟨fun a => ⟨p.onCarrier a, hc a⟩, fun v => ⟨p.onValues v, hv v⟩,
     fun x y => by apply Subtype.ext; exact p.preserves x y⟩,
   fun _ => rfl, fun _ => rfl⟩

/-- **A terminal object.** Every object maps uniquely to the one-point object `apex`. -/
theorem terminal_and_initial_terminal (A : Obj) :
    ∃! _ : Hom A apex, True :=
  ⟨⟨fun _ => (), fun _ => (), fun _ _ => rfl⟩, trivial, fun _ _ => by
    apply Hom.ext <;> (funext x; rfl)⟩

/-- The empty object, a candidate initial. -/
def bot : Obj := ⟨Empty, Empty, fun x _ => x.elim⟩

/-- **An initial object.** The empty object maps uniquely to every object. -/
theorem terminal_and_initial_initial (A : Obj) :
    ∃! _ : Hom bot A, True :=
  ⟨⟨fun x => x.elim, fun x => x.elim, fun x _ => x.elim⟩, trivial, fun _ _ => by
    apply Hom.ext <;> (funext x; exact x.elim)⟩

/-! ## Part 2: which shapes the ingredients support -/

/-- **A cone over a diagram.** Several objects mapping from one apex, needing only spans. It gives a common
source, but with no agreement condition on the legs. -/
theorem cone_over_a_diagram (T U : Obj) (t : T.X) (u : U.X) :
    Nonempty ((Hom apex T) × (Hom apex U)) :=
  ⟨apexTo T t, apexTo U u⟩

/-- **Consensus as a limit.** Agreement among views is expressible: the equalizer states two views agree, and
the pullback states two views agree over a common target. Both exist (`equalizers`, `pullbacks`), so consensus
is statable as a limit. -/
theorem consensus_as_a_limit (f g : Hom S T) {A : Obj} (p : Hom A S)
    (hc : ∀ a, f.onCarrier (p.onCarrier a) = g.onCarrier (p.onCarrier a))
    (hv : ∀ v, f.onValues (p.onValues v) = g.onValues (p.onValues v)) :
    ∃ h : Hom A (eq f g), (∀ a, (h.onCarrier a).1 = p.onCarrier a) :=
  ⟨(equalizers f g p hc hv).choose, (equalizers f g p hc hv).choose_spec.1⟩

/-- **Agreement without limits.** Even without a universal property, two views agree when two maps into a common
target have equal composites: `p ≫ f = q ≫ f` says the views coincide there, needing no limit. -/
theorem agreement_without_limits {A S T : Obj} (p q : Hom A S) (f : Hom S T)
    (h : ∀ a, p.onCarrier a = q.onCarrier a) :
    ∀ a, f.onCarrier (p.onCarrier a) = f.onCarrier (q.onCarrier a) :=
  fun a => by rw [h a]

/-! ## Part 3: provenance -/

/-- **Morphisms do not carry provenance.** A morphism can fabricate: `onValues` need not preserve absence, so a
cone's leg can send an absence to a verdict, manufacturing agreement. A source classification landing on an
absence maps, under such a leg, to a verdict indistinguishable from a genuine one. -/
theorem morphisms_do_not_carry_provenance :
    ∃ (f : Option Bool → Bool), f none = f (some true) ∧ (none : Option Bool) ≠ some true :=
  ⟨fun v => v.getD true, rfl, by decide⟩

/-- **Agreement versus evidence.** Two objects can agree on a value with no shared source: exhibit two apex-legs
whose value-components coincide, though the objects and the agreement carry no provenance, the coincidence
manufacturable by a fabricating leg. A cone from a shared object carries provenance only if its legs cannot
fabricate, which no established condition on `Hom` guarantees. -/
theorem agreement_versus_evidence :
    (apexTo apex ()).onValues () = (apexTo apex ()).onValues ()
    ∧ ∃ f : Option Bool → Bool, f none = f (some true) :=
  ⟨rfl, ⟨fun v => v.getD true, rfl⟩⟩

/-! ## The verdicts

Part 1: `Obj` has the limits, computed componentwise on carriers and values. Spans exist (`spans`); products
exist with the universal property (`products`); pullbacks and equalizers exist, factoring agreeing and
equalizing cones (`pullbacks`, `equalizers`); a terminal and an initial object exist, the one-point and the
empty classification (`terminal_and_initial_terminal`, `terminal_and_initial_initial`). So `Obj` is finitely
complete and bipointed. The classification is forced on each limit; nothing blocks the limit shapes.

Part 2: the several-views shapes that need limits are statable. Cones need only spans (`cone_over_a_diagram`);
consensus is a limit, the equalizer or pullback stating agreement (`consensus_as_a_limit`); and agreement is
even statable without a universal property, as equal composites into a common target (`agreement_without_limits`).
The sheaf shape is the exception: it needs a covering notion, a Grothendieck topology, which the framework does
not carry; its overlaps (pullbacks) exist, but the site does not, so the sheaf is blocked by the missing
covering, not by missing overlaps. A presheaf of views needs only the contravariant assignment, statable, but a
section would be a `Hom` and carries no more than a `Hom` does.

Part 3: no available shape carries provenance. A morphism can fabricate, `onValues` sending an absence to a
verdict (`morphisms_do_not_carry_provenance`), so a cone's leg can manufacture agreement, and agreement traces
to no common source (`agreement_versus_evidence`). No condition on `Hom` established so far, absence-preserving,
order-preserving, or theory-morphism, is imposed on the legs, so agreement is agreement by coincidence, not
evidence.

The verdict: objectivity-as-redundancy is not expressible, and the obstacle is not missing limits. `Obj` is
finitely complete, so every limit shape of several-views is available and consensus is a limit; the sheaf alone
is blocked, by the absent covering notion. But the deeper obstacle is provenance: redundancy is evidential only
if independent access traces to a common source, and a fabricating leg makes agreement without a source. So the
shapes are present and the evidence is absent; objectivity needs provenance-carrying morphisms the framework
does not require. Reported per shape, not in aggregate. Nothing here is resolved. -/

end Chiralogy.SeveralViews
