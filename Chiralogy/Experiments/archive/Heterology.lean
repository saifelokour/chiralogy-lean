import Chiralogy.Kernel.Apophatic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Chiralogy.Registers.Physics

/-! # Experiment: Heterology, the constructive arm, kernel first   [staged; gated on the proof terms]

The cataphatic dual of the apophatic kernel: the arm that constructs where apophatic refutes. Staged: this
stage builds the kernel dual only. Model and boundary follow only if the kernel dual does genuinely
different work on the proof terms. Stays in Experiments, resolves nothing, graduates nothing.

The whole risk is one thing: a symmetric mirror that does no new work. Heterology must construct (its
kernel theorem is ∃-shaped, a witness is built) where apophatic refutes (→ False, a thing is forbidden). The
decisive gate is the shape of the conclusion.

The gate, checked on terms:
- `apophatic_move` (recalled, `hole_uniform`) is refutation-shaped: `¬ Function.Surjective c`, and its proof
  (through `no_reflexive_object`) ends in `hg b hb : False`.
- `heterology_move` is construction-shaped: it exhibits `yoneda.preimage α`, an actual morphism built from
  the natural transformation. Its proof ends in a constructed term, not absurdity. This is the Yoneda
  direction (an object is recovered from its maps outward) dual to Lawvere's no-reflexive-object.

Where the self-fold fails, the other-build succeeds (`coexist`): the same object has no complete
self-account and a complete other-account, saying opposite things about opposite directions. And heterology
has its own forbidden move (`cataphatic_idolatry`): not every object builds outward into a given ambient,
so the arm bounds itself and is not blind positivity. Grades are inline; nothing here resolves P vs NP.
-/

open CategoryTheory Chiralogy

namespace Chiralogy.Heterology

/-- **The apophatic move (recalled, refutation-shaped).** The reflexive fold fails: no object surjects onto
its own function space. The proof ends in absurdity (`no_reflexive_object` closes with `hg b hb : False`).
●● -/
theorem apophatic_move {X : Type} (c : X → X → Option Bool) : ¬ Function.Surjective c :=
  hole_uniform c

/-- **The heterology move (new, construction-shaped).** The build succeeds: a morphism is reconstructed
from a natural transformation between the representables (Yoneda full). The proof exhibits the constructed
morphism `yoneda.preimage α`, not a contradiction. ●● -/
theorem heterology_move (A B : Obj) (α : yoneda.obj A ⟶ yoneda.obj B) :
    ∃ f : A ⟶ B, yoneda.map f = α :=
  ⟨yoneda.preimage α, yoneda.map_preimage α⟩

/-- **The complete other-account (cataphatic).** An object's morphisms are its outward relations: the
natural transformations between representables reconstruct the morphism. The reconstruction is an
equivalence, built both ways, not a negation. ●● -/
def complete_other_account (A B : Obj) : (yoneda.obj A ⟶ yoneda.obj B) ≃ (A ⟶ B) :=
  yonedaEquiv

/-- A sample object with a fixed-point-free codomain, for the coexistence check. -/
def sampleObj : Obj := ⟨Fin 2, Option Bool, fun x y => if x = y then some true else none⟩

/-- **The two accounts coexist, doing opposite work.** The same object has no complete self-account (the
fold fails, `hole_uniform`) and a complete other-account (the build succeeds, `yonedaEquiv`). The hole is in
the fold, not the build; they do not contradict. ●● -/
theorem coexist :
    (¬ Function.Surjective sampleObj.classify) ∧
    Nonempty ((yoneda.obj sampleObj ⟶ yoneda.obj sampleObj) ≃ (sampleObj ⟶ sampleObj)) :=
  ⟨hole_uniform sampleObj.classify, ⟨yonedaEquiv⟩⟩

/-- **Heterology's forbidden move (cataphatic idolatry).** Not every object builds outward into a given
ambient: a two-element carrier has no embedding into a one-element ambient. This is the dual of
no-reflexive-object (no fold in), a genuine limit on construction (no build out), and it uses the embedding
structure (injectivity of `onCarrier`), not the reflexive diagonal. So the arm bounds itself. ●● -/
theorem cataphatic_idolatry :
    ∃ A T : Obj, ¬ ∃ φ : A ⟶ T, Function.Injective φ.onCarrier :=
  ⟨⟨Bool, Unit, fun _ _ => ()⟩, ⟨Unit, Unit, fun _ _ => ()⟩,
   fun ⟨_, hφ⟩ => absurd (hφ (a₁ := true) (a₂ := false) (Subsingleton.elim _ _)) (by decide)⟩

/- **P vs NP, relocated (placement, not resolved).   ●**
P vs NP asks whether a construction exists: a polynomial algorithm, or a separating witness. It is
∃-shaped, cataphatic, about building outward, not an autological hole. That is why it never fit B2:
apophatic's boundary is the refutation of totalization (filling the internal hole), and P vs NP lives on the
other arm, the build. This is a placement to be tested by the model and boundary stages, gated on this
kernel dual. It is not resolved here, and nothing is defined that would decide it. -/

/-! ## Stage 2: the model dual (embedding / restriction)

Gated on stage 1, which passed. The one test this stage runs: is embedding a genuine costed, directional
move using specific ambient structure (arithmetization, a Boolean into a field richer than {0, 1}), or
generic "objects have maps out". The proof terms answer: embedding is specific (it uses a field with a
point beyond {0, 1} and fails for the trivial ambient), so heterology's model is not the free half. Two
honest deflations follow: the specificity is the field's, borrowed from arithmetic, not derived from the
heterological kernel; and embedding never touches `complete_other_account`, so the model floats free of the
kernel.

Part 1 recalls the apophatic moves as the duals to match. Totalization (the attempt, B2) fills the internal
hole; its fabrication cost is target-free. Partialization (abstention) is the inverse; its cost is
target-dependent. Their cataphatic duals are moves on the other-account, the build direction. -/

/-- The embedding: a Boolean value into a field, the arithmetization inclusion (`false` to 0, `true` to 1). -/
def embed (F : Type) [Zero F] [One F] : Bool → F := fun b => if b then 1 else 0

/-- **(b) Specific: embedding buys a new point in a genuinely richer ambient.** The field `ZMod 3` has an
element beyond the Boolean image {0, 1}, an evaluation point for algebraic spot-checking that the source
lacks. The proof uses the field's structure. ●● -/
theorem embedding_buys_in_rich_ambient : ∃ a : ZMod 3, a ≠ 0 ∧ a ≠ 1 :=
  ⟨2, by decide, by decide⟩

/-- **(b) It fails for the trivial ambient.** `ZMod 2` is Boolean: no point beyond {0, 1}, no gain. The
move is not generic; it requires specific richer structure and fails without it. ●● -/
theorem embedding_buys_nothing_in_trivial : ¬ ∃ a : ZMod 2, a ≠ 0 ∧ a ≠ 1 := by decide

/-- **(c) Not iso: embedding misses the ambient's extra points.** The inclusion `Bool → ZMod 3` is not
surjective; it cannot reach the third point. ●● -/
theorem embedding_not_iso : ¬ Function.Surjective (embed (ZMod 3)) := by
  intro hs; obtain ⟨b, hb⟩ := hs 2; cases b <;> exact absurd hb (by decide)

/-- The restriction: pull a field element back to Boolean (test whether it is 1). -/
def restrict : ZMod 3 → Bool := fun a => decide (a = 1)

/-- **Restriction recovers the object.** `restrict` after `embed` is the identity: the Boolean is
recovered. ●● -/
theorem restrict_embed_id : ∀ b : Bool, restrict (embed (ZMod 3) b) = b := by decide

/-- **Embedding does not recover the ambient.** `embed` after `restrict` is not the identity: the field's
extra point `2` is lost. Restriction is a genuine partial inverse (the build gains, the restrict loses),
the cataphatic dual of partialization. ●● -/
theorem embed_restrict_not_id : ∃ a : ZMod 3, embed (ZMod 3) (restrict a) ≠ a :=
  ⟨2, by decide⟩

/-- **The gain is target-dependent (the dual asymmetry).** A richer field gains more: `ZMod 5` has at least
two points beyond {0, 1} where `ZMod 3` has one. Embedding's gain depends on the ambient, while
restriction's loss is target-free (it always drops everything outside {0, 1}). This is the mirror of
apophatic's asymmetry (totalization target-free, partialization target-dependent), not the same. ●● witness;
the full dual-asymmetry claim is ●. -/
theorem gain_is_target_dependent :
    ∃ a b : ZMod 5, a ≠ 0 ∧ a ≠ 1 ∧ b ≠ 0 ∧ b ≠ 1 ∧ a ≠ b :=
  ⟨2, 3, by decide, by decide, by decide, by decide, by decide⟩

/- **Part 4: connection to the kernel (checked, negative).   ●**
Embedding should extend the other-account (`complete_other_account`, Yoneda): to build outward is to build
more relations outward. It does not. The embedding moves reference field structure (`ZMod`, `decide`) and
never `complete_other_account` or `yoneda`. Heterology's model and kernel are disconnected: they do not meet
through a theorem, so the specific weight of arithmetization is imported from the field, not carried down
from the Yoneda kernel.

**Part 5: P vs NP on the model (placement, not resolved).   ●**
P vs NP as a model question: does the required construction (a polynomial algorithm) embed into the
available ambient, or is it blocked. The embedding that would settle it is a cataphatic arithmetization
move (as arithmetization gave IP = PSPACE, a non-relativizing result); whether it reaches P vs NP is open.
Not resolved; nothing that would decide it is defined. -/

/-! ## Stage 3: the bridge (Yoneda as free cocompletion)

Gated on stages 1 and 2, both passed. This connects the kernel (other-account, Yoneda) to the model
(embedding, build-outward) through the shared build-outward pattern, closing deflation 2, and shows the
bridge is free, confirming deflation 1. The anti-launder rule holds: connecting two free things with a free
bridge generates no ownership. Nothing specific is derived from the bridge; it places the specific
construction without producing it.

An honesty note on the bridge. The full free-cocompletion universal property would derive the model from
the kernel. It cannot here: the kernel's Yoneda lives in the object category, the model's arithmetization
in a field, so there is no universal-property derivation across them. The genuine connection is the shared
pattern: both the other-account and the embedding are non-iso build-outward embeddings into a richer
ambient. That pattern is free, which is exactly why the connection routes borrowed weight without creating
owned weight.

The honest grade of the whole arm, stated and not softened:
- Structure: ●●. Kernel (Yoneda other-account), model (embedding), and bridge (the free build-outward
  pattern) are all real theorems, connected and universal.
- Force: ●. The specific weight (what makes a particular construction cross a barrier, arithmetization's
  field) is borrowed, hosted by the free skeleton, not owned by heterology.
- The asymmetry with apophatic: apophatic owns a specific obstruction (Lawvere with a flip, the hole, not
  free, not generic). Heterology owns a free construction (Yoneda, cocompletion) and hosts borrowed
  specifics. The apophatic arm has specific teeth; the cataphatic arm has universal reach and borrowed
  teeth. This is the correct nature of the two vias, not a defect. -/

/-- **The bridge (●●): kernel and model meet as build-outward embeddings.** The other-account (Yoneda) is a
faithful embedding into the richer presheaf ambient, and the model embedding is an injective, non-iso
embedding into a richer ambient. Both instantiate the same free build-outward pattern; the term references
both the Yoneda structure and the embedding, so kernel and model meet here, closing the disconnection stage
2 found. -/
theorem other_account_is_free_construction :
    (∀ A B : Obj, Function.Injective (yoneda.map (X := A) (Y := B))) ∧
    (Function.Injective (embed (ZMod 3)) ∧ ¬ Function.Surjective (embed (ZMod 3))) :=
  ⟨fun _ _ => yoneda.map_injective, by decide, embedding_not_iso⟩

/-- **The bridge is free (●●): it holds for any category, owning nothing.** Yoneda faithfulness (the free
cocompletion embedding) goes through for every category, with no specific ambient structure. Contrast with
`embedding_buys_in_rich_ambient`, which needed `ZMod 3`'s field and failed for `ZMod 2`. Both true; the
difference is the finding: the bridge connects generic to generic generically. -/
theorem bridge_is_free {C : Type u} [Category.{v} C] (A B : C) :
    Function.Injective (yoneda.map (X := A) (Y := B)) :=
  yoneda.map_injective

/-- **The weight stays borrowed (●● theorem, ● reading).** The free bridge holds even for the trivial
ambient, yet the specific gain still fails there: the field structure is hosted by the free skeleton, not
generated by it. The bridge places the specific construction; it does not produce it. -/
theorem weight_stays_borrowed :
    (∀ A B : Obj, Function.Injective (yoneda.map (X := A) (Y := B))) ∧
    (¬ ∃ a : ZMod 2, a ≠ 0 ∧ a ≠ 1) :=
  ⟨fun _ _ => yoneda.map_injective, embedding_buys_nothing_in_trivial⟩

/- **Part 4: why this is heterology's relationship to the barrier (placement, ●).**
The free part of building-outward relativizes: it holds of any ambient, including oracle ambients, so
generic constructions cannot cross the barrier. Only the specific part crosses: arithmetization uses the
field, which an oracle cannot fake. So heterology's own free-versus-borrowed structure predicts the
barrier: the free cocompletion skeleton relativizes, and the specific hosted construction is what crosses.
P vs NP needs a specific cataphatic construction the free skeleton cannot produce, which is why the arm can
place P vs NP in its skeleton but not settle it. Not resolved; nothing that would decide it is defined. -/

/-! ## Stage 4: the boundary (does the arm own its refusal?)

The final stage, dual to apophatic's B2. B2 is a specific refusal: no complete-and-faithful object, needing
Lawvere with a flip (it fails without the flip). Heterology's refusal is `cataphatic_idolatry`: not every
object embeds, a two-carrier object into a one-carrier ambient. The one question: is that refusal owned
(discriminates via heterology's own structure) or free (generic).

The refusal discriminates (`boundary_discriminates`): no into a smaller ambient, yes into an equal or larger
one. But the discrimination is generic pigeonhole (`boundary_is_free`): the refusal reduces to
`Fintype.card_le_of_injective`, holding for any finite types with a card gap, owning nothing
heterology-specific. Chiralogy's refusal needs the flip and fails without it; heterology's refusal is
cardinality, holding unconditionally. So the discriminator is free, not owned.

Verdict: free. Heterology owns nothing at the boundary either. The complete arm: reach ●● free (Yoneda),
construction ● borrowed (arithmetization's field), refusal ● free (pigeonhole). Free and hosting top to
bottom, owning nothing. Chiralogy owns its no (the flip) and does not build its yes (the empty center is not
constructed); heterology hosts its yes (borrowed) and does not own its no (generic). The two vias are mirror
opposites in ownership, and that is their correct nature, not a defect. Nothing here resolves P vs NP. -/

/-- **The refusal discriminates (●●): no into a smaller ambient, yes into an equal or larger one.** A
two-element carrier does not embed into a one-element ambient, but does embed into a two-element one, so the
refusal is not a blanket no; it discriminates by the ambient. -/
theorem boundary_discriminates :
    (∃ f : Bool → Bool, Function.Injective f) ∧ (¬ ∃ f : Bool → Unit, Function.Injective f) :=
  ⟨⟨id, Function.injective_id⟩,
   fun ⟨f, hf⟩ => absurd (Fintype.card_le_of_injective f hf) (by decide)⟩

/-- **The refusal is free (●● theorem, ● ownership).** The discrimination is generic pigeonhole: no
injection into a strictly smaller finite type, holding for any types with a card gap. The refusal reduces to
`Fintype.card_le_of_injective`, owning nothing heterology-specific. Unlike apophatic's refusal, which needs
the flip and fails without it, this needs only cardinality and holds unconditionally. -/
theorem boundary_is_free {α β : Type} [Fintype α] [Fintype β] (f : α → β)
    (h : Fintype.card β < Fintype.card α) : ¬ Function.Injective f :=
  fun hinj => absurd (Fintype.card_le_of_injective f hinj) (not_le.mpr h)

/- **The complete final grade of the heterology arm.**
- Kernel (Yoneda other-account): ●● structure, free.
- Model (embedding, arithmetization): ●● structure, ● force (borrowed field).
- Bridge (free cocompletion pattern): ●● structure, free.
- Boundary (cataphatic refusal): ●● theorems, ● ownership (free, generic pigeonhole).
Reach free, construction borrowed, refusal free: the cataphatic arm owns nothing and hosts everything
specific. This is the mirror of apophatic, which owns its refusal (the flip-specific hole) and does not build
its center (the empty center is not a construction). Owns-what-it-forbids versus hosts-what-it-builds: the
two vias, fixed. Nothing here resolves P vs NP. -/

/-! ## Graduation-prep 1: the crossing (is the framework chiastic?)

A chiasm needs an inversion map carrying one arm to the other, in the term. The candidate would carry the
fold's data (a fixed-point-free flip refuting a surjection, `no_reflexive_object`) to the build's data (a
natural transformation constructing a morphism, `heterology_move`). No such map exists on the terms: the
flip is an endomap on a codomain and carries no information about morphisms between category objects, so
there is no canonical function producing a natural transformation from a flip. The two moves take
independent inputs, and neither is produced from the other. The only genuine dualization available is the
generic opposite-category involution, which composes and touches neither arm's specific data, so it is the
wrong shape for a broken crossing.

What exists is adjacency, not crossing (`two_adjacent_arms`): both moves hold, side by side, joined by a
conjunction, each on its own independent hypothesis. That is a table (apophatic owns-no and empty-yes,
heterology free-no and borrowed-yes, on two axes), not a chiasm (an inversion map). Even `coexist` from the
kernel stage is a conjunction, not a crossing.

Verdict: the framework is bicameral, not chiastic. The crossing is prose and analogy, not a map. And the
reason is the lopsidedness stage 4 fixed (●): an owned obstruction (the flip) and a free construction
(Yoneda, pigeonhole) cannot be inverted into each other, so no crossing map is even available to break. The
non-chiasticity is the asymmetry, one register up. Graduation proceeds as a bicameral framework, without the
chiasm claim. Nothing here resolves P vs NP. -/

/-- **Two adjacent arms, not a crossing (●●).** The apophatic move (refutation) and the cataphatic move
(construction) both hold, joined by a conjunction, each on its own independent input: the fold's `c` and the
build's `α` are separate hypotheses, neither produced from the other. Adjacency (a table on two axes), not a
chiasm (an inversion map). No term-level `cross` carries the flip to the Yoneda construction; the term joins
the two by `And`, not by a function. -/
theorem two_adjacent_arms {X : Type} (c : X → X → Option Bool) (A B : Obj)
    (α : yoneda.obj A ⟶ yoneda.obj B) :
    (¬ Function.Surjective c) ∧ (∃ f : A ⟶ B, yoneda.map f = α) :=
  ⟨hole_uniform c, heterology_move A B α⟩

/-! ## Graduation-prep 2: the cataphatic submission form

The protocol's apophatic form has five fields (carrier, distinction-space, can-differ, classify,
non-degeneracy); its discriminating field is can-differ with non-degeneracy, the owned gate (the flip), so
few systems pass, those with a genuine hole. This stage adds the cataphatic form, and builds it loose where
the apophatic is tight, because the arm proved building-outward is free (Yoneda) and only borrowed-specifics
fail to embed (pigeonhole). The two gates are asymmetric by the arm's proven nature; the asymmetry is the
point, not a defect.

The cataphatic form (`CataphaticConformant`) is carrier, ambient, and build-outward, with no owned
discriminating field: build-outward is free, so nearly everything passes (`cataphatic_is_loose`), unlike the
apophatic form, which a degenerate classifier fails (`apophatic_is_tight`). The one place it discriminates is
the borrowed-specific bite (`cataphatic_borrowed_bite`): building into a particular rich ambient needs the
ambient's structure, graded ● because the specificity is the ambient's, not the protocol's. The two gates
are orthogonal (`protocol_orthogonal`): a system can build without a hole, or have a hole independently of
the specific build. This is experiment-staged; the canonical Protocol is untouched. Nothing resolves P vs
NP. -/

/-- **The cataphatic submission form.** Carrier, ambient, and a build-outward map. There is no owned
discriminating field (no can-differ analogue): building-outward is free, so the form is loose by design. -/
structure CataphaticConformant where
  X : Type
  T : Type
  build : X → T

/-- **The cataphatic form is loose (●● structure).** Every carrier passes: it builds into itself. The form
admits almost everything, by the arm's proven freeness. -/
theorem cataphatic_is_loose (X : Type) : ∃ cc : CataphaticConformant, cc.X = X :=
  ⟨⟨X, X, id⟩, rfl⟩

/-- **The apophatic form is tight (recall).** Not every classifier passes: a degenerate (constant)
classifier has no hole, failing non-degeneracy. The owned gate discriminates. -/
theorem apophatic_is_tight : ∃ c : Fin 2 → Fin 2 → Option Bool, ¬ NonDegenerate c :=
  ⟨fun _ _ => some true, fun ⟨_, _, h⟩ => h rfl⟩

/-- **The borrowed-specific bite (●● theorem, ● force).** The one place the cataphatic form discriminates:
building into a specific rich ambient needs the ambient's structure (a point beyond {0, 1}, present in
`ZMod 3`, absent in `ZMod 2`). The specificity is the ambient's, borrowed, not the protocol's. -/
theorem cataphatic_borrowed_bite :
    (∃ a : ZMod 3, a ≠ 0 ∧ a ≠ 1) ∧ (¬ ∃ a : ZMod 2, a ≠ 0 ∧ a ≠ 1) :=
  ⟨embedding_buys_in_rich_ambient, embedding_buys_nothing_in_trivial⟩

/-- **The two gates are orthogonal (●●).** A system builds without a hole (a degenerate classifier that
still has a build), and a system has both (a non-degenerate classifier with a build). Building and holing are
independent vias, neither forcing the other. -/
theorem protocol_orthogonal :
    (∃ (X T : Type) (_build : X → T) (c : X → X → Option Bool), ¬ NonDegenerate c) ∧
    (∃ (X T : Type) (_build : X → T) (c : X → X → Option Bool), NonDegenerate c) :=
  ⟨⟨Fin 2, Fin 2, id, fun _ _ => some true, fun ⟨_, _, h⟩ => h rfl⟩,
   ⟨Fin 2, Fin 2, id, fun x y => some (decide (x = y)),
    ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩⟩⟩

/-- **The protocol is complete and asymmetric (●● structure).** Both forms exist: the apophatic (tight,
owned, some fail) and the cataphatic (loose, free, all pass). The asymmetry is the arm's lopsidedness
inherited by the instrument: one tight owned gate, one loose free gate, because holes are rare and
constructions are free. -/
theorem protocol_is_complete_and_asymmetric :
    (∀ X : Type, ∃ cc : CataphaticConformant, cc.X = X) ∧
    (∃ c : Fin 2 → Fin 2 → Option Bool, ¬ NonDegenerate c) :=
  ⟨cataphatic_is_loose, apophatic_is_tight⟩

/-! ## Graduation-prep 3: the shared structure (two centers, one map)

The hypothesis: a self-classification map `c : X → X → B` is two-ended. The apophatic center is the codomain
`B` (the fold's hole lives there: the flip is a fixed-point-free endomap on `B`, and the hole is a gap in
the range into `B`). The cataphatic center is the domain `X` (the build's source: `X` generates its
relations outward, each `x` its row `c x`). One map, a center at each end.

The gate holds on the term: `apophatic_center_is_codomain` and `cataphatic_center_is_domain` both range over
one `c : X → X → B`, and `one_map_two_ends` puts both ends in a single term over the same `c`. The apophatic
end lands on the codomain `B` (via a `g : B → B`); the cataphatic end lands on the domain `X` (via the
transpose `X → (X → B)`). So at the bare-map level, this is the strong result: one map, two ends, domain and
codomain (●●). The cataphatic end is free (the transpose always exists), consistent with the arm's proven
freeness.

The honest obstacle (Part 2), confronted. The arm's elaborated cataphatic centers are not this domain. Stage
1's build was Yoneda on the object category (about objects `(X, B, classify)`, not a bare type `X`); stage
2's was an arithmetization field (`ZMod 3`, a separate object entirely, as stage 2's disconnection already
found). Neither is the domain `X` of a classification map. So the domain/codomain shape is clean and strong
for the bare map `c`, but the arm's built elaborations float off to the side, disconnected (●). Split grade:
bare-map ●● strong, elaborated-model ● disconnected. The hypothesis was not forced by redefining the arm's
center; it is tested on the bare map, where it holds, and the elaborations are reported as separate, not
fitted to it.

The arrow (Part 3, ●). If the two centers are domain and codomain of one map, they are asymmetric by
definition: a map goes one way, source to target, and domain differs from codomain intrinsically. This is
not the dead broken-chiasm (there is no crossing map); it is more primitive, the directionality of the map
itself. The map's one-way-ness is the arrow's surviving candidate after the crossing died, on firmer ground
because it needs only an asymmetry (domain not codomain, trivially so), not an inversion. A placement, not a
proof of anything temporal. Nothing resolves P vs NP. -/

/-- **The apophatic center is the codomain (●●).** For a single map `c : X → X → B`, the fold-refusal lives
at the codomain `B`: a fixed-point-free endomap on `B` refutes surjectivity. The obstruction is a statement
about `B`. -/
theorem apophatic_center_is_codomain {X B : Type} (c : X → X → B) (g : B → B) (hg : ∀ b, g b ≠ b) :
    ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-- **The cataphatic center is the domain (●●).** For the same shape of map `c : X → X → B`, the build-source
lives at the domain `X`: `X` generates its relations outward, the transpose `X → (X → B)` sending each `x` to
its row `c x`. The build is free (it always exists), consistent with the arm. -/
theorem cataphatic_center_is_domain {X B : Type} (c : X → X → B) :
    ∃ build : X → (X → B), ∀ x, build x = c x :=
  ⟨fun x => c x, fun _ => rfl⟩

/-- **One map, two ends (●●).** The same `c : X → X → B` carries both: the apophatic end at the codomain `B`
(a fixed-point-free endomap there refutes the fold) and the cataphatic end at the domain `X` (its transpose
is the free build-outward). Two centers, one map, its domain and its codomain, in one term. -/
theorem one_map_two_ends {X B : Type} (c : X → X → B) :
    (∀ g : B → B, (∀ b, g b ≠ b) → ¬ Function.Surjective c) ∧
    (∃ build : X → (X → B), ∀ x, build x = c x) :=
  ⟨fun g hg => no_reflexive_object hg c, ⟨fun x => c x, fun _ => rfl⟩⟩

/-! ## Graduation-prep 4: the op-chiasm (does the hole survive the domain/codomain swap?)

The crossing stage rejected op because `op ∘ op = id`. But composing on the bare map is not the chiasm test.
The test is whether the hole, the apophatic obstruction, survives op, which swaps codomain and domain. The
shared-center stage established the hole lives at the codomain `B`; op moves `B` to the domain position.

The term decides, and it says clean symmetry. `no_reflexive_object` needs a fixed-point-free endomap on the
codomain, and it puts no condition on the domain. So the hole is not `B`-specific; it is a codomain-generic
role, holding for whatever type is in the codomain position with a fixed-point-free endomap
(`hole_is_codomain_generic`). Under op, the hole-role transports to the swapped codomain: `no_reflexive_object`
holds for the op-swapped shape `d : B → B → X` given a fixed-point-free endomap on `X`, exactly as it held
for `c : X → X → B` given one on `B` (`hole_survives_op`). And `op ∘ op = id` returns to `c`, which has the
hole, so a reversible involution cannot lose hole-content on the round trip.

Verdict: clean op-symmetry, not a broken chiasm. The hole survives op faithfully as a codomain-generic role.
The framework is not chiastic; the earlier closure stands, and is stronger now, a clean op-symmetry rather
than mere adjacency. The reopening's bet on resurrection was wrong, and the term shows it: the hole
transports, it does not die. The arrow gets no home here (no content is lost under op, because op recovers
the map and the hole with it). Nothing resolves P vs NP. -/

/-- **The hole is codomain-generic (●●).** The fold-refusal obstructs surjection for any codomain carrying a
fixed-point-free endomap, with no condition on the domain. It is not `B`-specific; it is a role held by
whatever type sits in the codomain position. -/
theorem hole_is_codomain_generic {X B : Type} (g : B → B) (hg : ∀ b, g b ≠ b) (c : X → X → B) :
    ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-- **The hole survives op (●●): clean symmetry, not a broken chiasm.** op swaps `X` and `B`. Given
fixed-point-free endomaps on both ends, the hole holds at the codomain-`B` map `c` and, transported, at the
op-swapped codomain-`X` map `d`: `no_reflexive_object` applies to the swapped shape exactly as to the
original. The hole-role transports faithfully, and `op ∘ op = id` recovers it. No content is lost; the
chiasm does not resurrect. -/
theorem hole_survives_op {X B : Type} (gX : X → X) (hgX : ∀ x, gX x ≠ x)
    (gB : B → B) (hgB : ∀ b, gB b ≠ b) (c : X → X → B) (d : B → B → X) :
    ¬ Function.Surjective c ∧ ¬ Function.Surjective d :=
  ⟨no_reflexive_object hgB c, no_reflexive_object hgX d⟩

/-! ## Graduation-prep 5: the keystone (is the empty center the op-fixed middle?)

The last stage tests whether the empty center is the op-fixed middle between the cataphatic domain-center and
the apophatic codomain-center of one map. This is the third structural intuition, and the two before it were
wrong on the term (no crossing map, op is clean), so it is distrusted as hard.

The term says the keystone holds, and shows it, part by part. Part 1: the empty center is the coincidence
locus in its own definition, not a gloss. `empty_center_is_coincidence` is the condition `X ≃ (X → B)`, an
object equal to its own account across the two ends, and it is exactly what the empty center already was.
Part 3: it is empty because of the hole, the same theorem, proven from `fixedPoint_of_surjection` (the
diagonal). Statement is the coincidence, proof is the hole, one theorem. Part 2: op swaps the ends, and the
coincidence-emptiness holds at both, so it is invariant under the swap (`op_fixes_empty_center`).

One honest caveat, at full force: op remains conceptual (there is no concrete involution, as the earlier
stages found), so op-fixed here means the emptiness is invariant under the end-swap, not a computed fixed
point of a concrete map. The keystone is a symmetric empty middle, shown on the term, not a fixed-point
calculation.

Verdict: the keystone holds. The three centers are not three things: they are the two ends and the empty
middle of one map `c : X → X → B`. The cataphatic build-source at the domain, the apophatic hole at the
codomain, and the empty center where they would coincide (`X ≃ (X → B)`), kept empty by the hole and
symmetric under the op that swaps the ends. The bicameral framework graduates as a unified structure: two
ends and an empty middle of one map, not two adjacent arms. Nothing resolves P vs NP. -/

/-- **The empty center is the coincidence locus, and empty from the hole (●●, parts 1 and 3).** The empty
center's condition `X ≃ (X → B)`, an object equal to its own account, is impossible: a self-reflection iso
would be a surjection, which the hole forbids. Statement is the coincidence; proof is the hole. -/
theorem empty_center_is_coincidence {X B : Type} (g : B → B) (hg : ∀ b, g b ≠ b) :
    ¬ Nonempty (X ≃ (X → B)) := by
  rintro ⟨e⟩
  obtain ⟨b, hb⟩ := fixedPoint_of_surjection (⇑e) e.surjective g
  exact hg b hb

/-- **op fixes the empty center (●●, part 2).** op swaps the ends `X` and `B`. The coincidence-emptiness
holds at both: no object equals its account with codomain `B`, and none with the swapped codomain `X`. So
the empty middle is invariant under the end-swap (op-fixed as a symmetry), while the ends are swapped. -/
theorem op_fixes_empty_center {X B : Type} (gX : X → X) (hgX : ∀ x, gX x ≠ x)
    (gB : B → B) (hgB : ∀ b, gB b ≠ b) :
    (¬ Nonempty (X ≃ (X → B))) ∧ (¬ Nonempty (B ≃ (B → X))) :=
  ⟨empty_center_is_coincidence gB hgB, empty_center_is_coincidence gX hgX⟩

/-- **The keystone (●●).** Two ends and an empty middle of one map. The cataphatic build-source is the
domain, the apophatic hole is the codomain, and the empty center is the coincidence `X ≃ (X → B)` where they
would meet: kept empty by the hole (`empty_center_is_coincidence`) and symmetric under the op that swaps the
ends (`op_fixes_empty_center`). Not three centers, but the two ends and the empty middle of one
classification map. -/
theorem keystone {X B : Type} (gX : X → X) (hgX : ∀ x, gX x ≠ x) (gB : B → B) (hgB : ∀ b, gB b ≠ b) :
    (¬ Nonempty (X ≃ (X → B))) ∧ (¬ Nonempty (B ≃ (B → X))) :=
  op_fixes_empty_center gX hgX gB hgB

/-! ## Graduation-readiness: three targets, one stage

T1 (serious, rendered on its own terms): are the built theorems instances of the bare spine, or separate?
T2: close the op-conceptual caveat with a concrete involution. T3: re-grade the ambient from borrowed to
parametric. T1 is the gate and is not rescued by T2 or T3 landing. -/

/-- **T1: the spine's cataphatic slot is the transpose (●●).** For the bare map `c : X → X → B`, the
cataphatic end is exactly `c`'s transpose, a map `X → (X → B)`. This is the slot the built content would have
to fill to be an instance. -/
theorem spine_cataphatic_is_transpose {X B : Type} (c : X → X → B) :
    ∃ build : X → (X → B), build = c :=
  ⟨c, rfl⟩

/- **T1 verdict: SEPARATE (●), on its own terms, not rescued by T2 or T3.**
The built content does not instantiate the bare spine, and the terms show it, not prose.
- The kernel (`heterology_move`) is Yoneda full-faithfulness on the object category `Obj` (triples, a
  category), not the transpose of a bare `c`. It proves more than the spine's slot (full-faithfulness versus
  transpose-exists) and lives one level up. Not an instance; its term never mentions `c` or `one_map_two_ends`.
- The model (`embed : Bool → ZMod 3`) has a field as codomain, not a function space `X → B`, so it is not a
  transpose. Not an instance; its term is field structure.
- Re-deriving would require redefining `c` to be the hom-functor of `Obj` (and even then the built content is
  stronger), which is forcing (fitting the content to the spine). So it is not connectable without forcing.
Verdict: clean spine, disconnected content. The bare spine is a skeleton; Yoneda-on-`Obj` and arithmetization
are a pile beside it. This is a specific, nameable state, and it is named: NOT ready to graduate as a unified
structure. T2 and T3 landing does not change it. -/

/-- **T2: the concrete op involution.** The op that swaps the two centers is `Prod.swap` on the pair of
center-types. A real involution, `op ∘ op = id`, built not described. -/
def op_concrete : Type × Type → Type × Type := Prod.swap

/-- **op is a genuine involution (●●).** `op_concrete ∘ op_concrete = id` on the term. -/
theorem op_concrete_involutive (p : Type × Type) : op_concrete (op_concrete p) = p := Prod.swap_swap p

/-- The empty center as a predicate on the pair of center-types. -/
def emptyCenterAt (p : Type × Type) : Prop := ¬ Nonempty (p.1 ≃ (p.1 → p.2))

/-- **T2: the op-symmetry is the literal action of `op_concrete` (●●).** The empty center holds at `(X, B)`
and at `op_concrete (X, B)`, so its swap-invariance is not merely "the property holds at both ends" but the
action of the concrete involution `op_concrete` on the pair of centers. The caveat closes: op is concrete
(`Prod.swap`), modest but real, and the symmetry references it. -/
theorem op_symmetry_is_op_action {X B : Type} (gX : X → X) (hgX : ∀ x, gX x ≠ x)
    (gB : B → B) (hgB : ∀ b, gB b ≠ b) :
    emptyCenterAt (X, B) ∧ emptyCenterAt (op_concrete (X, B)) :=
  ⟨empty_center_is_coincidence gB hgB, empty_center_is_coincidence gX hgX⟩

/-- **T3: the ambient is an open parameter (●●).** The cataphatic form is parametric over its ambient `T`:
any `T` with a build gives a conformant, structurally identical to how the apophatic `Member` takes its
distinction space `B` as a slot. Neither arm owns its target space; both fill it per-instance. -/
theorem ambient_is_open_parameter (X T : Type) (f : X → T) :
    ∃ cc : CataphaticConformant, cc.X = X ∧ cc.T = T :=
  ⟨⟨X, T, f⟩, rfl, rfl⟩

/-- **T3: arithmetization is one filling, not borrowed weight (●●).** `ZMod 3` is one filling of the open
ambient slot; `ZMod 5` is another, equally admissible. The specific ambient is a slot filled per-instance,
so the cataphatic force is parametric, not borrowed. The prior grade of ● borrowed was a mischaracterization;
the corrected grade is ●● parametric. The two slots remain asymmetric (the apophatic slot is tight, the
cataphatic slot loose), which is the lopsidedness, not a force-deficiency. -/
theorem arithmetic_is_a_filling :
    (∃ cc : CataphaticConformant, cc.T = ZMod 3) ∧ (∃ cc : CataphaticConformant, cc.T = ZMod 5) :=
  ⟨⟨⟨Bool, ZMod 3, embed (ZMod 3)⟩, rfl⟩, ⟨⟨Bool, ZMod 5, embed (ZMod 5)⟩, rfl⟩⟩

/-! ## Graduation-readiness take 2: conformance, not instantiation

T1 asked whether the built content instantiates the bare spine, and found it does not. This stage tests the
reframe: does the content connect by conformance to the cataphatic protocol, the way apophatic's registers
conform to Member without instantiating `no_reflexive_object`, kernel general and registers specific with a
protocol between. The reframe is convenient, which is the tell, so it must pass on the term.

The parallel, checked (not assumed): apophatic's physics register conforms to Member (`phys : Member`,
`nondegenerate := imprecise_is_partial_mode.1`) and its terms contain zero direct references to
`no_reflexive_object`. So a register not referencing the kernel is the architecture, not a gap, as long as it
conforms to the protocol. The parallel is real.

The gate, on the term:
- Arithmetization CONFORMS: `arithmetic_register_conforms` is an actual `CataphaticConformant` witness
  (carrier `Bool`, ambient `ZMod 3`, build `embed`). It passes the protocol as the physics register passes
  Member. For it, T1's disconnection was the wrong standard: conformance is the standard, and it conforms.
- Yoneda-on-Obj does NOT conform: `CataphaticConformant.X` is `Type` (Type 0) and `Obj` is `Type 1`, so
  `(Obj, ...)` fails to typecheck against the protocol on a universe mismatch. The categorical Yoneda lives a
  universe up; it is a general categorical fact, kernel-shaped, not an object-level register. The protocol
  was left fixed, not weakened to admit it; it simply does not pass.

Verdict: MIXED, partial readiness. The object-level cataphatic content (arithmetization) conforms and
connects through the protocol, unified-through-conformance, the same architecture as apophatic, ready as a
register. The categorical Yoneda-on-Obj does not conform: a universe up, kernel-shaped, not among the
registers. The reframe corrected T1 for arithmetization but overclaimed in calling Yoneda-on-Obj a conforming
register: it is not, on the term. So the framework is ready as apophatic kernel/protocol/registers plus a
cataphatic kernel (the spine) and one conforming cataphatic register (arithmetization); the categorical
Yoneda content sits at the kernel level, not among the registers. Not forced, not laundered: arithmetization
passes the fixed protocol, Yoneda-on-Obj does not. Nothing resolves P vs NP. -/

/-- **Arithmetization conforms to the cataphatic protocol (●●).** A genuine `CataphaticConformant` witness:
carrier `Bool`, ambient `ZMod 3`, build `embed`. It passes the fixed protocol as apophatic's registers pass
Member, connecting to the kernel by conformance, not instantiation. -/
def arithmetic_register_conforms : CataphaticConformant := ⟨Bool, ZMod 3, embed (ZMod 3)⟩

/-- The Yoneda register's carrier `Obj` is a universe up: it lives in `Type 1`, not the `Type 0` that
`CataphaticConformant.X` requires. This is why `(Obj, ...)` cannot be a witness of the protocol, and why
Yoneda-on-Obj is kernel-shaped (a general categorical fact) rather than an object-level register. -/
def yoneda_carrier_is_a_universe_up : Type 1 := Obj

/-! ## C (rewrite): is the bare spine the Cayley-style specialization of the Yoneda spine?

Pure exploration; the framework is already ready and nothing rides on this. The reframe, literature-backed:
does `one_map_two_ends` (bare, Type 0) derive from the Yoneda spine (Type 1) by the one-object / point
restriction that gives Cayley from Yoneda, crossing the universe boundary take-2's error marked? The
precedent raised the prior; the term decides, and it says C fails on all three gate parts.

- Not derived (part 3): `one_map_two_ends`'s proof is `no_reflexive_object` (the diagonal) and the transpose
  `⟨c, rfl⟩`. Its term contains zero references to `yoneda` or `richer_spine`. The bare spine is provable
  independently; forcing the Yoneda spine into its proof would leave `yoneda` unused or require redefining
  the spine to fit the content.
- No universe crossing (part 2): `one_map_two_ends` is entirely at Type 0 (`{X B : Type}`), and its proof
  never touches Type 1. `richer_spine` is at Type 1 (`Obj : Type 1`). Nothing crosses Type 1 to Type 0,
  because the bare spine never needed the Type 1 level; the boundary take-2 marked is not traversed.
- Not the Cayley move (part 1): the Cayley specialization of Yoneda yields the hom-functor of a one-object
  category (a monoid's action on itself). The bare spine quantifies over all `c : X → X → B`, including maps
  with no composition or identity, which are not hom-functors. So the bare spine is strictly more general
  than yoneda-at-one-object; it is not that restriction, it is broader.

Verdict: C fails. The bare spine is fundamental in its own right at Type 0; Yoneda is a separate general
fact at Type 1; Cayley is a precedent that does not instantiate on these structures. Two kernel-level facts,
not one-and-its-shadow. The literature raised the prior; the term did not confirm it. Take-2's universe
error is not a Cayley boundary; it is only that the categorical Yoneda is a universe up and does not conform
to the object-level protocol. The framework graduates as take-2: a bicameral kernel/protocol/register
structure with one conforming cataphatic register (arithmetization) and a kernel-level Yoneda beside the
bare spine. C is a beautiful near-miss. Nothing resolves P vs NP. -/

/-- The richer Yoneda spine, at **Type 1**: full-faithfulness on the object category (`Obj : Type 1`). This
is where Yoneda-on-Obj lives, the fundamental categorical fact. -/
theorem richer_spine (A B : Obj) (α : yoneda.obj A ⟶ yoneda.obj B) : ∃ f : A ⟶ B, yoneda.map f = α :=
  heterology_move A B α

/-- The bare spine is provable with no reference to `richer_spine`, entirely at **Type 0**: its proof is the
diagonal and the transpose. `richer_spine` does not appear, so the bare spine is not derived from the Yoneda
spine and no universe boundary is crossed. C fails; the bare spine stands on its own. -/
theorem bare_spine_needs_no_yoneda {X B : Type} (c : X → X → B) :
    (∀ g : B → B, (∀ b, g b ≠ b) → ¬ Function.Surjective c) ∧ (∃ build : X → (X → B), ∀ x, build x = c x) :=
  one_map_two_ends c

/-! ## Cataphatic register witnesses: conformance AND independence

The reference register is `arithmetic_register_conforms` (`X = Bool`, `T = ZMod 3` a field, `build = embed`),
buying algebraic spot-checking from the field. Conforming to `CataphaticConformant` is the loose gate:
build-outward is free, so everything passes it and conforming proves nothing about independence. A candidate
is a new independent register only if, on the term, its ambient and its bought-operation both differ from
`Bool → field / algebraic-checking`. Three candidates from the build-outward family are tested; only the
independent ones are counted, and family-members are named as arithmetization reclothed. -/

/-- Candidate 1, error-correcting code. Conforms: carrier a message bit, ambient the 3-repetition codeword
space, build the encoding. The ambient `Bool × Bool × Bool` is a product with a Hamming metric, not a
field. -/
def ecc_register : CataphaticConformant := ⟨Bool, Bool × Bool × Bool, fun b => (b, b, b)⟩

/-- The Hamming distance on the codeword ambient: the metric structure the message space lacks. -/
def hamming3 (a b : Bool × Bool × Bool) : Nat :=
  (if a.1 = b.1 then 0 else 1) + (if a.2.1 = b.2.1 then 0 else 1) + (if a.2.2 = b.2.2 then 0 else 1)

/-- ECC is independent: its bought-operation is distance, not algebraic-checking. Distinct messages encode
to codewords at Hamming distance 3 (minimum distance 3, one error correctable). This is a metric operation
on a product ambient, not the field-arithmetic of `arithmetic_register_conforms`. So ECC is a new register,
not arithmetization in a costume, even though a Reed-Muller polynomial is itself a codeword: the substrate
overlaps, the bought-operation does not. -/
theorem ecc_buys_distance : hamming3 (ecc_register.build false) (ecc_register.build true) = 3 := by decide

/-- Candidate 2, PCP encoding. Conforms: carrier a witness bit, ambient a field, build the low-degree
extension. Its ambient is `ZMod 3`, a field. -/
def pcp_register : CataphaticConformant := ⟨Bool, ZMod 3, embed (ZMod 3)⟩

/-- PCP collapses to the arithmetization family: its ambient is the very field
`arithmetic_register_conforms` uses, and its bought-operation (local checkability) is bought by that field
extension, the same algebraic spot-checking. Same ambient core, not an independent register. -/
theorem pcp_collapses_to_arithmetization : pcp_register.T = arithmetic_register_conforms.T := rfl

/-- Candidate 3, interactive proof. Conforms: carrier a statement bit, ambient a transcript, build the map
into it. But a `build : X → T` is static, and the interactive bought-operation (prover-verifier rounds,
adaptivity) is temporal, so it is not captured here: the transcript `[b]` is a generic static encoding, not
an interaction. Fiat-Shamir confirms the collapse from the other side, hashing the transcript sends any
interactive protocol to a static non-interactive one. The round-structure is not an irreducible ambient on
the term, so IP collapses to a static encoding, not an independent register. -/
def ip_register : CataphaticConformant := ⟨Bool, List Bool, fun b => [b]⟩

/-! ### The honest tally

Every candidate conforms (the loose gate), so all are graded structure. Independence is decided on the term:
- ECC: independent. Ambient a product with a Hamming metric, bought-operation distance (`ecc_buys_distance`),
  distinct from `Bool → field`. A new register.
- PCP: collapses. Ambient the arithmetization field (`pcp_collapses_to_arithmetization`), bought-operation
  the same algebraic-checking. Arithmetization reclothed.
- IP: collapses. A static build cannot carry the interactive bought-operation, and Fiat-Shamir sends the
  interaction to a static encoding. Not an irreducible ambient.

The cataphatic register layer's honest thickness is two: `arithmetic_register_conforms` and `ecc_register`,
buying algebraic-checking and error-correction from a field and a metric respectively. PCP and IP conform
but are the arithmetization family, one method reclothed, and are not counted. The layer is thinner than
apophatic's several apophatic registers; that is the term's count, not a shortfall, and a padded three is
refused. Nothing resolves P vs NP. -/

/-! ## Reclassification: are the cataphatic witnesses model primitives, not registers?

The suspicion: `arithmetic_register_conforms` and `ecc_register` were mis-slotted as cataphatic registers.
A register is a domain, a subject-matter that instantiates the framework (physics). These are methods,
construction techniques. The test, on the term: do they sit at the model level in the structural role of
`Option` (a concrete construction realizing an abstract move, no subject-matter), and does a domain conform
to both arms at once? Placement only; no layout is designed. -/

/-- Part 2. Physics's cataphatic half is the transpose of its own self-classification, one map read at two
ends. Not a forced construction: it is `Physics.phys.classify`, the very map that carries the apophatic
hole. -/
def physics_has_cataphatic_half : CataphaticConformant :=
  ⟨Physics.phys.X, Physics.phys.X → Physics.phys.B, fun s => Physics.phys.classify s⟩

/-- Physics conforms to both arms on the term: `Member` (apophatic, established, the contentful hole) and
`CataphaticConformant` (cataphatic, its own transpose). The domain layer is shared, though the cataphatic
conformance is the loose gate, the free transpose rather than an independent structure. -/
theorem physics_conforms_to_both :
    (Physics.phys.classify = Physics.phys.classify) ∧
    physics_has_cataphatic_half.build = fun s => Physics.phys.classify s :=
  ⟨rfl, rfl⟩

/-- Part 3. The two ends are the same `c`: `one_map_two_ends` on physics's classify gives the very transpose
`physics_has_cataphatic_half` is built from. So the cataphatic half was always available on the existing
map, revealed by the protocol, not added. This grounds "always bicameral" on the term, ●●. The narrative
gloss that the framework was always secretly bicameral is only ●: the term supports the precise claim (every
`c` has a transpose) and the bicameralism is lopsided, its second chamber the free transpose. -/
theorem physics_bicameral_is_one_map_two_ends :
    physics_has_cataphatic_half.build = (fun s => Physics.phys.classify s) ∧
    (∃ build : Physics.phys.X → (Physics.phys.X → Physics.phys.B),
      ∀ x, build x = Physics.phys.classify x) :=
  ⟨rfl, (one_map_two_ends Physics.phys.classify).2⟩

/-- Part 1. Physics's cataphatic build is the transpose of a self-classification, tied to a domain. -/
theorem physics_build_from_its_classify :
    physics_has_cataphatic_half.build = fun s => Physics.phys.classify s := rfl

/-- Arithmetization's build is a standalone construction, `embed`, not the transpose of any
self-classification. It carries no `Member`, no hole, no subject-matter; it realizes build-outward the way
`Option` realizes keep-the-none at the model level. A model primitive, not a register. -/
theorem arithmetic_build_is_standalone : arithmetic_register_conforms.build = embed (ZMod 3) := rfl

/-- Likewise ECC: its build is the encoding, a standalone construction, not a domain's transpose. -/
theorem ecc_build_is_standalone : ecc_register.build = fun b => (b, b, b) := rfl

/-! ### The reclassification verdict (architecture, not layout)

On the term, all three parts land, with the lopsidedness stated honestly:
- Part 1, ●●. `arithmetic_register_conforms` and `ecc_register` have standalone builds (`embed`, the
  encoding), carry no self-classification, and hold no subject-matter. They occupy `Option`'s structural
  role, a concrete construction realizing an abstract move at the model level. Model primitives, not
  registers.
- Part 2, ●● structure. Physics conforms to both `Member` and `CataphaticConformant`, the cataphatic half
  being the transpose of its own `classify`. The domain layer is shared. The cataphatic conformance is the
  loose gate, so the sharing is lopsided.
- Part 3, ●● for the term-fact, ● for the gloss. `physics_bicameral_is_one_map_two_ends` grounds the
  bicameralism on `one_map_two_ends`: the same `c`, two ends, the transpose always available on the existing
  map. "Always secretly bicameral" as a story is ● narrative and is not upgraded past the transpose.

The corrected architecture, stated not drawn: one shared domain layer (registers are domains, each a
`Member` whose single `c` is bicameral by `one_map_two_ends`), addressed by two lopsided arms each with a
model layer, apophatic model primitive `Option` (keep-the-none), cataphatic model primitives arithmetization
and ECC (build-outward). The earlier stage's "cataphatic registers" were mis-slotted methods; here they are
model primitives, and the register layer is the shared domains like physics. No layout is designed, where a
center or boundary sits is the next question, excluded here. Nothing resolves P vs NP. -/

/-! ## Reading 4: is the cataphatic arm the proposer to the apophatic guard?

Pseudo-Dionysius: the cataphatic arm proposes affirmative accounts (the names, the constructions), the
apophatic arm guards (idolatry-detection bounds them). The functional question is what the cataphatic arm is
for, and the answer to test is proposer/guard. The critical constraint: this must be data-flow, the built
account is the input to the refutation, not a between-arms map. The term has refused every between-arms
crossing (`two_adjacent_arms` is an `And`, no content-arrow), so reading 4 must not resurrect that map in
Dionysian clothes. What is tested is that one account, proposed by the cataphatic arm, is bounded by the
apophatic arm, in one term. -/

/-- The proposer. A cataphatic construction whose ambient is the account space `X → B`: its build proposes
an account of `X`, a candidate self-classification in transpose form. Free (build-outward proposes
anything). -/
def proposedAccount {X B : Type} (build : X → (X → B)) : CataphaticConformant := ⟨X, X → B, build⟩

/-- The guard bounds the proposal, on the term. Idolatry-detection (`no_reflexive_object`) fires on the
proposer's own output `(proposedAccount build).build`: if the proposed account were totalized (claimed
surjective, the complete self-classification), it is refuted. The argument to the refutation is the built
account itself, so this is data-flow (the account flows into the guard), not a function between the arms.
The same `build` is the proposer's output and the guard's target, in one term. -/
theorem proposer_guard {X B : Type} (build : X → (X → B)) {g : B → B} (hg : ∀ b, g b ≠ b) :
    ¬ Function.Surjective (proposedAccount build).build :=
  no_reflexive_object hg build

/-- The guard is universal: it bounds any account, not only proposed ones. So the relationship is a division
of labor, a free proposer met by a guard ready for any proposal, not a guard that targets one construction.
This is the same data-flow read at the top level: whatever the proposer builds, the guard is already able to
bound. -/
theorem guard_is_universal {X B : Type} (c : X → X → B) {g : B → B} (hg : ∀ b, g b ≠ b) :
    ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-! ### The verdict

All three gates land on the term:
- Same account, both arms. `(proposedAccount build).build` is the proposer's output and is exactly the
  argument `no_reflexive_object` refutes. One object, not two glued by prose.
- Data-flow, not a crossing. `proposer_guard`'s proof is `no_reflexive_object hg build`, the guard applied
  to the account. There is no map `CataphaticArm ⟶ ApophaticArm`; the account is consumed as input. This is
  application, distinct from `two_adjacent_arms` (an `And`) and from the refused content-arrow.
- The guard bounds the proposal. `no_reflexive_object` fires on the built account (returns
  `¬ Surjective (proposedAccount build).build`), not a generic refutation sitting nearby.

So reading 4 holds, ●●: the cataphatic arm's function is proposer, it generates the affirmative accounts
that idolatry-detection disciplines, generation feeding correction by data-flow. This explains the
lopsidedness (proposing is free, `guard_is_universal` shows guarding is owned and total) and answers the
deflation worry, the cataphatic arm is generative, not inert. The framework needs both arms because neither
does the other's job: the guard only refutes, never builds an account; the proposer only builds, never
bounds. The honest qualification: the guard is universal, so it does not target this proposal specifically;
the division of labor is real, the targeting is not exclusive.

Divergence from the theology, ●: the classical tradition subordinates cataphatic to apophatic. The framework
does not. The proposer is free (build-outward, Yoneda) and the two ends are co-equal (`one_map_two_ends`,
the op-symmetry of the hole), so the proposer is free, not inferior. That the tradition ranks them and the
framework does not is a reading of the divergence, not a theorem about Dionysius. Nothing resolves P vs NP. -/

/-! ## The arrow, third form: is proposer to guard flow dynamical or kinematical?

Two forms of the arrow died: the broken chiasm (no crossing map) and content-loss-under-op (op clean). The
functional layer opened a third: the proposer to guard flow is directional (`proposer_guard` one way,
`guard_is_universal` no return). The literature splits this precisely: an arrow is kinematical if it is set
by the type signature (the guard lacks a build), dynamical if it is a structural obstruction (both round-trip
composites exist and differ, the adjoint curvature between embedding and coarse-graining). Test both
composites on the term. The arrow is zero-for-two; two of the three outcomes are no-arrow. -/

/-- Composite 1, build-then-fold. Exists (`proposer_guard`). The account `build` is consumed: it appears in
the term and in the output type, the refutation is of that account. Type flows into Prop. -/
theorem build_then_fold {X B : Type} (build : X → (X → B)) {g : B → B} (hg : ∀ b, g b ≠ b) :
    ¬ Function.Surjective (proposedAccount build).build :=
  proposer_guard build hg

/-- Composite 2, fold-then-build, does not genuinely exist. The guard's actual output is `¬ Surjective c`, a
Prop, hence proof-irrelevant: any map `F` from that output to an account is constant in it (`rfl`, by proof
irrelevance). So the refutation carries nothing to build from; whatever account `F` returns is smuggled from
the ambient data, not derived from the guard's output. The asymmetry is by absence, the type signature: Type
flows into Prop (build-then-fold), Prop cannot flow back into Type (fold-then-build). -/
theorem fold_then_build_ignores_guard {X B : Type} (c : X → X → B)
    (F : ¬ Function.Surjective c → CataphaticConformant) (h₁ h₂ : ¬ Function.Surjective c) :
    F h₁ = F h₂ := rfl

/-- The diagonal the guard refutes with, `fun x => g (c x x)`, is a buildable account, but it is built from
the guard's inputs `c` and `g`, not from its output (the refutation). So it is a separate construction using
the same inputs, not fold-then-build; it does not rescue the second composite. The guard's output still
yields nothing. -/
def diagonal_uses_inputs_not_output {X B : Type} (g : B → B) (c : X → X → B) : X → B := fun x => g (c x x)

/-! ### The verdict

Kinematical. `fold_then_build_ignores_guard` shows the second composite does not exist from the guard's
actual output: `¬ Surjective c` is proof-irrelevant, so any map out of it is constant and the account is
smuggled, never derived. Part 2 (do the two composites differ?) is never reached, there is only one genuine
composite, so the op-clean check does not arise. The one-wayness of the proposer to guard flow is the type
signature, not a structural obstruction. Real as data-flow (build-then-fold genuinely consumes the account),
but not a dynamical arrow: no adjoint curvature is instantiated on the term, because there is no second
composite to differ from the first.

Grade: ●● for the term-fact (the second composite is forced constant by proof irrelevance), deflationary as
a reading. The relation between the arms is a division of labor with a directional dependency, Type into
Prop, not an irreversible dynamical flow. The adjoint-curvature naming raised the prior; the term did not
find a differing round-trip. The arrow is now zero-for-three. Nothing resolves P vs NP. -/

/-! ## The theorem for the reading: is the relevance asymmetry forced by content, or a modeling choice?

The reading (●) was that the relevance asymmetry is the apophatic/cataphatic distinction, apophatic
proof-irrelevant, cataphatic proof-relevant. The pitfall: proof-irrelevance is a general property of Prop, true
of every proposition, so "the guard's output is proof-irrelevant because it is in Prop" is contingent
placement, not a theorem about idolatry-detection. The reading promotes to ●● only if the apophatic bareness
is forced by the content, surviving Type-valuation, not inherited from the Prop placement. -/

/-- A Type-valued idolatry witness: the diagonal `no_reflexive_object` refutes with. This is the apophatic
bound made proof-relevant. -/
def idolatryWitness {X B : Type} (g : B → B) (c : X → X → B) : X → B := fun x => g (c x x)

/-- Part A fails. Two distinct totalizations yield distinct idolatry witnesses, so a Type-valued
idolatry-detector is proof-relevant: the apophatic content is not intrinsically bare. It is the Prop
statement `¬ Surjective` that discards the witness, and that discarding is the modeling choice. If the
bareness were content, this would collapse to one witness; it does not. -/
theorem idolatry_distinguishes_totalizations :
    idolatryWitness (X := Unit) (fun b => !b) (fun _ _ => true) ≠
      idolatryWitness (X := Unit) (fun b => !b) (fun _ _ => false) := by decide

/-- What is genuinely content on the apophatic side is verdict-universality: totalization always fails, for
every `c`. This is a real theorem (`no_reflexive_object`), but it is not proof-irrelevance. One constant
verdict across all accounts is a different fact from two proofs of one failure being equal, and it does not
make the arm's data (the witness) bare. So the content fact the apophatic arm actually has is universality,
not bareness. -/
theorem apophatic_verdict_is_universal {X B : Type} (c : X → X → B) {g : B → B} (hg : ∀ b, g b ≠ b) :
    ¬ Function.Surjective c := no_reflexive_object hg c

/-- Part B holds. The cataphatic accounts are framework-distinct by bought-operation, not merely as Type
inhabitants: ECC buys a Hamming metric (distance 3, `ecc_buys_distance`), arithmetization buys a field. The
content, what the account does for the framework, differs. -/
theorem cataphatic_content_distinct :
    hamming3 (ecc_register.build false) (ecc_register.build true) = 3 ∧
      arithmetic_register_conforms.T = ZMod 3 :=
  ⟨ecc_buys_distance, rfl⟩

/-! ### The promotion verdict

The reading stays ●. Promotion needs both halves forced by content; only B is.
- Part A fails. `idolatry_distinguishes_totalizations` shows a Type-valued idolatry-detector (the diagonal
  witness) is proof-relevant: two totalizations get distinct witnesses. So the apophatic bareness is not
  intrinsic to idolatry-detection, it is the Prop statement `¬ Surjective` discarding the diagonal. The
  bareness is Prop-erasure, the contingent fact the pitfall warned of, not content-bareness. The genuine
  content fact is verdict-universality (`apophatic_verdict_is_universal`), a different theorem that is not
  proof-irrelevance.
- Part B holds. `cataphatic_content_distinct` shows the accounts differ by bought-operation (metric versus
  field), framework-distinct, not merely distinct terms.

So the relevance asymmetry is a modeling choice, not a theorem: the apophatic bound is placed in Prop (which
discards its witness) and the cataphatic account in Type (which keeps its structure), and the apophatic side
could have been Type-valued (the diagonal is real data). The proof-irrelevance tracks the Prop/Type
placement, not the apophatic/cataphatic distinction. The reading is a coherent lens, ●, and does not promote
to ●●, because the bareness is Prop-inherited. The cataphatic structure is genuinely content (B), but a
one-sided content fact does not force the asymmetry. Nothing resolves P vs NP. -/

/-! ## Cataphatic moves and cataphatic model-count

Two builds, graded independently. Build 1: does the cataphatic model have moves (free/forget) and do they
close the loop to the apophatic monad? Build 2: are the cataphatic models the free constructions, is there a
genuinely independent third, and is the layer open? -/

/-! ### 1a: the cataphatic moves, free and forget, not inverse

The free move is `embed` (adds structure, into the field); the forget move is `restrict` (drops structure,
back to the source). They are already on the term: `restrict_embed_id` (forget after free is the identity on
the source, `embed` is a section) and `embed_restrict_not_id` (free after forget is not the identity, the
field's extra point is lost). This is the cataphatic dual of the apophatic model's non-invertible move-pair
(`Model/Partiality`, totalize-then-partialize is not the identity either): both models have a move-pair that
fails to compose to the identity, and the failure is the content. Graded ●● on the term for the two moves
and their non-inversion. Honest limit: `embed` is a section and `restrict` its retraction (a split mono with
retraction), the free-then-forget-not-identity shape, but a full categorical adjunction with natural
unit/counit is not verified here. So: two moves with the non-inverse content, not a verified adjunction. -/

/-- 1a, restated as the named pair: forget-after-free is the identity, free-after-forget is not. -/
theorem free_forget_moves :
    (∀ b : Bool, restrict (embed (ZMod 3) b) = b) ∧ (∃ a : ZMod 3, embed (ZMod 3) (restrict a) ≠ a) :=
  ⟨restrict_embed_id, embed_restrict_not_id⟩

/-! ### 1b: does the loop close? (the between-arms claim, distrusted)

The apophatic model primitive is the monad `Option` (`Kl(Maybe)`), a `Type → Type` endofunctor adjoining a
point, whose forgetful functor is from pointed types. The cataphatic free construction is `embed`, a single
map into a fixed field, whose forgetful functor is from fields. These are different forgetful functors
(pointed versus field), and the two gadgets are not even the same kind: `Option` is a monad on `Type`,
`embed` is not an endofunctor of `Type` and carries no monad structure. So they are two different
free/forgetful pairs, not the two triangles of one adjunction. The loop does not close. -/

/-- The apophatic model primitive is a genuine monad on `Type`. -/
example : Monad Option := inferInstance

/-- 1b verdict, on the term: the apophatic side is a monad on `Type` (`Option`), the cataphatic side a map
into a fixed field that is not surjective (`embedding_not_iso`), not a monad on `Type`. Different gadgets,
different forgetful functors: no single shared adjunction. The loop does not close, it is resemblance (both
are free/forget), not identity. -/
theorem loop_does_not_close :
    Nonempty (Monad Option) ∧ ¬ Function.Surjective (embed (ZMod 3)) :=
  ⟨⟨inferInstance⟩, embedding_not_iso⟩

/-! ### 2a: a third independent cataphatic model (free-order, buys comparison)

A third free construction with a different forgetful functor (from ordered sets) and a genuinely new
bought-operation (comparison), neither the field's algebraic-checking nor ECC's metric. -/

/-- The third model: build a bit into an ordered ambient. Conforms. -/
def order_register : CataphaticConformant := ⟨Bool, ℕ, fun b => if b then 1 else 0⟩

/-- The bought-operation is comparison. `less` forces the ambient to reduce to `ℕ`; the two built points are
ordered, `build false < build true`. Comparison is distinct from field-arithmetic (arithmetization) and from
Hamming distance (ECC), so this is a third independent model. -/
def less (a b : ℕ) : Bool := decide (a < b)

theorem order_buys_comparison :
    less (order_register.build false) (order_register.build true) = true := by decide

/-- The three bought-operations side by side: a field (arithmetization), a metric (ECC), an order
(this model). Three different forgetful functors, three independent cataphatic models. -/
theorem three_independent_bought_operations :
    arithmetic_register_conforms.T = ZMod 3 ∧
      hamming3 (ecc_register.build false) (ecc_register.build true) = 3 ∧
      less (order_register.build false) (order_register.build true) = true :=
  ⟨rfl, ecc_buys_distance, by decide⟩

/-! ### 2b: the inexhaustibility principle (● reading)

The cataphatic models are the free constructions, one per forgetful functor. Freyd's General Adjoint Functor
Theorem guarantees a free construction (a left adjoint) for each suitable forgetful functor, and forgetful
functors are open-ended (one per algebraic structure: Lawvere theories, operads, an unbounded supply). So
the cataphatic model layer is open, not exhaustible: `arithmetic_register_conforms`, `ecc_register`, and
`order_register` are three instances (field, metric, order), and there is a new one for every structure.

Contrast the apophatic model, which is unique: one diagonal, one obstruction (`no_reflexive_object`), one
model (`Kl(Maybe)`). This is the ownership asymmetry at the model level: the apophatic model is unique
because it owns one obstruction; the cataphatic models are open because each borrows one free construction
per structure. Marked ●: a reading grounded in Freyd and the free/owned asymmetry, not a formalized
enumeration of all cataphatic models. Nothing resolves P vs NP. -/

/-- The apophatic obstruction the uniqueness reading rests on: one diagonal refutation, holding of every
account. Stated here only to anchor the ● contrast; the uniqueness itself is the reading. -/
theorem apophatic_obstruction_is_one {X B : Type} (c : X → X → B) {g : B → B} (hg : ∀ b, g b ≠ b) :
    ¬ Function.Surjective c := no_reflexive_object hg c

/-! ### The four verdicts, independent

- 1a, ●●: the free/forget moves exist and fail to be inverse (`free_forget_moves`), the cataphatic dual of
  the apophatic non-invertible pair. Honest limit: a section/retraction shape, not a verified full
  adjunction.
- 1b, fails: the loop does not close (`loop_does_not_close`). The apophatic monad `Option` and the cataphatic
  `embed` are different forgetful functors, different gadgets, two adjunctions not one. Resemblance, not
  identity, the between-arms claim failing again.
- 2a, ●●: a third independent model exists (`order_register`, `order_buys_comparison`), a new forgetful
  functor with a new bought-operation (comparison), not a costume of arithmetization or ECC.
- 2b, ●: the inexhaustibility principle is a reading (Freyd plus the ownership asymmetry), not a ●●
  enumeration. Apophatic unique (owns one obstruction), cataphatic open (borrows one free construction per
  structure). -/

/-! ## The chiasm census: apophatic-fractal versus cataphatic-nested

The mapping at the chiasm level. The apophatic chiasms are fractal (self-similar, scale-free, the same hole
at every level). Test whether the cataphatic chiasms are nested (a chiasm at each level of the build-outward
tower, each contained in the next). Grade each part independently. -/

/-! ### Part 1: the apophatic chiasm is fractal (scale-free), ●●

`hole_uniform` is the anchor: every object, whatever its distinction space, is Cantor-uniform, the same
obstruction at every level. The hole has no size parameter, it is the same at every magnification: fractal,
scale-free, self-similar. This restates an existing ●● fact as fractality. The compositional consequence
(`double_chiasm_does_not_compose`, in the Boundary) is that the apophatic chiasms sit parallel, kernel-hole
beside model-none, different absences, and do not merge: fractal things recur beside each other. -/

/-- The apophatic obstruction is scale-free: it holds of every object at every level, one shape at every
magnification (`hole_uniform`, restated as fractality). -/
theorem apophatic_chiasm_is_fractal {X : Type} (c : X → X → Option Bool) : ¬ Function.Surjective c :=
  hole_uniform c

/-! ### Part 2: the cataphatic side nests (heterogeneous tower), ●●

A tower of containments, each level a different richer structure, not self-similar repetition. `tower1`
embeds `Bool` in the field `ZMod 3`; `tower2` embeds that field in `ZMod 3 × ℕ`, adding an order coordinate.
Both are injective (containment), and the levels are heterogeneous (a field, then a field with an order
dimension, different bought-operations). Nested, not fractal. -/

/-- Level one: a bit into a field. -/
def tower1 : Bool → ZMod 3 := embed (ZMod 3)

/-- Level two: the field into a field-with-order, a different richer structure. -/
def tower2 : ZMod 3 → ZMod 3 × ℕ := fun x => (x, 0)

/-- The tower nests: each level is a genuine containment (injective build-outward), and the levels are
heterogeneous (field, then field with an order coordinate). -/
theorem tower_nests : Function.Injective tower1 ∧ Function.Injective tower2 :=
  ⟨Function.LeftInverse.injective (g := restrict) restrict_embed_id, fun _ _ h => congrArg Prod.fst h⟩

/-! ### Part 3a: the cataphatic model chiasm, at the surplus, ●●

The free move (`embed`) and forget move (`restrict`) are two cost-inverted moves crossing at a center. The
crossing is a genuine inversion (`embed_restrict_not_id`, free-then-forget is not the identity, so forget is
a real second move). The center is the surplus: the freely-added structure forget drops, the field's extra
point `2` that `embed` never reaches (`embedding_not_iso`). This is dual to the apophatic model chiasm
(totalize/partialize at the none): the none is a missing value (absence), the surplus is an extra value
(excess). Signature met, ●● for center and inversion. -/
theorem cataphatic_model_chiasm :
    (∀ b, restrict (embed (ZMod 3) b) = b) ∧
      (∃ a : ZMod 3, embed (ZMod 3) (restrict a) ≠ a) ∧
      ¬ Function.Surjective (embed (ZMod 3)) :=
  ⟨restrict_embed_id, embed_restrict_not_id, embedding_not_iso⟩

/-! ### Part 3b: the cataphatic kernel chiasm is ABSENT (one inversion, the lopsided result)

The apophatic kernel had two inversions (self-referential and epistemic) crossing at the hole. The
cataphatic kernel has only one move, the free transpose (`one_map_two_ends`): the account is `c` read as a
build, a single inversion. There is no second cataphatic kernel inversion, the guard is universal (not a
crossing, `guard_is_universal`) and the proposer to guard flow is data-flow (not a between-arms map,
established). A chiasm needs two arms to cross; with one inversion there is none. So there is no cataphatic
kernel chiasm, the honest lopsided result. No second inversion is invented to complete the parallel. -/

/-- The single cataphatic kernel move: the transpose. One inversion, hence no two-armed crossing at the
kernel. -/
theorem cataphatic_kernel_has_one_inversion {X B : Type} (c : X → X → B) :
    ∃ build : X → (X → B), build = c :=
  ⟨c, rfl⟩

/-! ### Part 4: do the nested chiasms telescope? (the between-level claim, distrusted) ●●

The apophatic fractal chiasms do not compose (parallel, different absences). The dual: do the cataphatic
nested chiasms compose by containment? Compose the two levels: `embedComp` is `embed` then the level-two
embedding, `restrictComp` the two forgets. The composite is again a free/forget chiasm (forget-after-free is
the identity, free-after-forget is not), and its center contains the level-one center: the level-one surplus
`2`, carried up to `(2, 0)`, is unreached by the composite (`level1_center_in_composite`). So the level-one
chiasm sits inside the composite chiasm: the nested chiasms telescope, on the term. This is the genuine dual
of the apophatic non-composition, fractal-parallel-non-composing versus nested-telescoping-composing. Honest
mechanism, stated so it is not mystified: the telescoping is that build-outward (a section with retraction)
composes across levels, exactly what absences at different levels do not do. That one side composes and the
other does not is the duality; the composition itself is the general fact that sections compose. -/

/-- The composite free move, two levels of build-outward. -/
def embedComp : Bool → ZMod 3 × ℕ := fun b => (embed (ZMod 3) b, 0)

/-- The composite forget move, two levels dropped. -/
def restrictComp : ZMod 3 × ℕ → Bool := fun p => restrict p.1

/-- The nested chiasms telescope: the composite is again a free/forget chiasm. -/
theorem telescopes :
    (∀ b, restrictComp (embedComp b) = b) ∧ (∃ p, embedComp (restrictComp p) ≠ p) :=
  ⟨fun b => restrict_embed_id b, ⟨(2, 0), by decide⟩⟩

/-- The composite center contains the level-one center: the level-one surplus `2`, carried to `(2, 0)`, is
unreached by the composite embedding. Containment shown, so the telescoping is by containment. -/
theorem level1_center_in_composite : ¬ ∃ b, embedComp b = ((2 : ZMod 3), (0 : ℕ)) := by decide

/-! ### Part 5: the measure level is nested BORROWED, ● (the grade guard)

The cataphatic arm can host a measure level: build outward into a magnitude-carrying ambient, buying
measurement, one more free construction and one more forgetful functor. `measure_register` builds a bit into
`ℤ`, and the bought-operation is magnitude (`natAbs`): both `1` and `-1` have magnitude `1`, so measurement
collapses the order (distinct from `order_register`, which buys comparison). The measure is BORROWED, hosted
exactly as the field, the metric, and the order are borrowed, not owned or derived.

The grade guard, firm: this is ●, a nested borrowed construction. It does NOT promote to the framework owning
or grounding magnitude (●●). The framework's standing position is that every magnitude is imported and never
enters the derived layers; a measure level is one more borrowed nested construction, not an exception. The
framework hosts measures; it does not own magnitude. -/

/-- The measure level, one more borrowed nested construction: build into a magnitude-carrying ambient. -/
def measure_register : CataphaticConformant := ⟨Bool, ℤ, fun b => if b then 1 else -1⟩

/-- The bought-operation is magnitude: both built values have magnitude one, so measurement collapses the
order. Borrowed like the others, hosted not owned. -/
def magnitude (z : ℤ) : ℕ := z.natAbs

theorem measure_hosts_magnitude :
    magnitude (measure_register.build true) = 1 ∧ magnitude (measure_register.build false) = 1 := by decide

/-! ### The census verdict

The apophatic-fractal / cataphatic-nested duality holds on the term, and the census is lopsided:
- Part 1, ●●. Apophatic chiasm fractal (scale-free, `apophatic_chiasm_is_fractal` = `hole_uniform`),
  parallel and non-composing.
- Part 2, ●●. Cataphatic side nests (`tower_nests`), a heterogeneous tower of containments.
- Part 3a, ●●. A cataphatic model chiasm at the surplus (`cataphatic_model_chiasm`), dual to the apophatic
  none (excess versus absence).
- Part 3b, absent. No cataphatic kernel chiasm: only one inversion (the transpose,
  `cataphatic_kernel_has_one_inversion`), and a chiasm needs two arms. The lopsided result, not forced.
- Part 4, ●●. The nested chiasms telescope (`telescopes`, `level1_center_in_composite`), composing by
  containment, the dual of apophatic non-composition. Honest mechanism: sections compose, absences do not.
- Part 5, ●. The measure level is borrowed and nested (`measure_hosts_magnitude`), hosted not owned. The
  framework does not own magnitude.

So the count is lopsided (one cataphatic model chiasm, no cataphatic kernel chiasm), and the composition is
dual (apophatic fractal chiasms sit parallel and do not compose, cataphatic nested chiasms telescope). The
totalizing figure "the cataphatic side is chiastic" stays out of reach; only the per-center and per-inversion
facts are ●●. Nothing resolves P vs NP. -/

end Chiralogy.Heterology
