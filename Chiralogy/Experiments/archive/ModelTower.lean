import Chiralogy

/-! # Experiment: is Kl(Maybe) the base of a cataphatic tower on the model side?

The model layer is asymmetric: apophatic unique (`Kl(Maybe)`, `Option Bool`), cataphatic open. Test whether
the apophatic model is the base of a cataphatic build-outward: whether a memoryful model (a Writer-flavoured
`Option Bool × List E`) is a `TowerLevel` above it, with memory as the surplus. The kernel is untouched
throughout: every object still has a hole and the verdict stays uniform.

The tower machinery is re-derived locally (the experiments are not compiled). Stays in `Experiments/`;
canonical untouched; nothing about P vs NP resolved. -/

open Chiralogy

namespace Chiralogy.ModelTower

/-! ## Shared: the tower machinery -/

@[ext] structure TowerLevel (A B : Type) where
  emb : A → B
  ret : B → A
  sec : Function.LeftInverse ret emb

def levelCompose {A B C : Type} (f : TowerLevel A B) (g : TowerLevel B C) : TowerLevel A C where
  emb := g.emb ∘ f.emb
  ret := f.ret ∘ g.ret
  sec := fun a => by simp only [Function.comp_apply]; rw [g.sec (f.emb a), f.sec a]

def grade {A B : Type} [Fintype A] [Fintype B] (_f : TowerLevel A B) : ℤ :=
  (Fintype.card B : ℤ) - Fintype.card A

theorem grade_adds {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (f : TowerLevel A B) (g : TowerLevel B C) :
    grade (levelCompose f g) = grade f + grade g := by
  simp only [grade]; ring

/-! ## Part 1: the memoryful model -/

/-- The memoryful distinction space: a verdict paired with an event log. -/
abbrev Mem (E : Type) : Type := Option Bool × List E

/-- **The memoryful level.** The apophatic distinction space embeds with an empty log; the retraction forgets
the log. A section with retraction on the term. -/
def memLevel (E : Type) : TowerLevel (Option Bool) (Mem E) :=
  ⟨fun b => (b, []), fun p => p.1, fun _ => rfl⟩

/-- Lift a classification into the memoryful model with an empty log. -/
def embedMem {X E : Type} (c : X → X → Option Bool) : X → X → Mem E :=
  fun x y => (memLevel E).emb (c x y)

/-- Forget the log, recovering the classification. -/
def restrictMem {X E : Type} (mc : X → X → Mem E) : X → X → Option Bool :=
  fun x y => (memLevel E).ret (mc x y)

/-- **The retraction holds.** Embedding then forgetting is the identity on classifications. -/
theorem restrict_embed_id {X E : Type} (c : X → X → Option Bool) :
    restrictMem (embedMem (E := E) c) = c := rfl

/-! ## Part 2: memory is the surplus -/

/-- **Memory is the surplus.** A nonempty log is a memoryful state outside the image of the embedding: the
excess the free move leaves (5.b.2), a value the apophatic model cannot express. -/
theorem memory_is_the_surplus : ∃ m : Mem Unit, ∀ b, (memLevel Unit).emb b ≠ m :=
  ⟨(some true, [()]), fun _ h => by
    have h2 : ([] : List Unit) = [()] := congrArg Prod.snd h
    exact absurd h2 (by decide)⟩

/-- **The kernel survives memory.** The hole holds of memoryful classifications: `no_reflexive_object` fires
at the memoryful codomain, using the fixed-point-free endomap that cycles the verdict and keeps the log. The
verdict stays uniform; memory does not make the guard discriminate. -/
theorem kernel_survives_memory {X E : Type} (c : X → X → Mem E) : ¬ Function.Surjective c :=
  no_reflexive_object (g := fun p => (optCycle p.1, p.2))
    (fun p h => optCycle_fixedpointfree p.1 (congrArg Prod.fst h)) c

/-! ## Part 3: does the tower's grade apply? -/

/-- **Unbounded memory is infinite.** The log type `List Unit` contains an infinite family, so the
finite cardinality gap, and hence the grade, does not apply to the unbounded memoryful codomain. -/
theorem unbounded_memory_is_infinite : Function.Injective (fun n : ℕ => List.replicate n ()) :=
  fun _ _ h => by simpa using congrArg List.length h

/-- A finite memoryful level: a bounded log (at most one event). -/
def memLevelBounded : TowerLevel (Option Bool) (Option Bool × Option Unit) :=
  ⟨fun b => (b, none), fun p => p.1, fun _ => rfl⟩

/-- **The bounded grade is defined.** With a finite log the grade is the cardinality gap, three. -/
theorem grade_of_bounded_memory : grade memLevelBounded = 3 := by
  simp only [grade, Fintype.card_prod, Fintype.card_option, Fintype.card_bool, Fintype.card_unit]
  norm_num

/-- A second finite memoryful level, above the first. -/
def memLevel2 : TowerLevel (Option Bool × Option Unit) ((Option Bool × Option Unit) × Option Unit) :=
  ⟨fun b => (b, none), fun p => p.1, fun _ => rfl⟩

/-- **Memory over memory adds.** Composing two finite memoryful levels adds their grades, the same additive
law as every other cataphatic composition. Memory is a surplus, but an additive one. -/
theorem memory_over_memory_adds :
    grade (levelCompose memLevelBounded memLevel2) = grade memLevelBounded + grade memLevel2 :=
  grade_adds memLevelBounded memLevel2

/-! ## Part 4: the canonicity question -/

/-- **Freeness is untouched.** The base embeds out faithfully: `embedMem` is injective, a genuine embedding
out of the apophatic model, consistent with `maybe_free_pointed` (free means initial, and maps out of an
initial object are what freeness provides). The theorem stands. -/
theorem embed_out_of_base {X E : Type} : Function.Injective (embedMem (X := X) (E := E)) := by
  intro c c' h
  funext x y
  exact congrArg Prod.fst (congrFun (congrFun h x) y)

/-- **Canonicity under pressure.** A genuine level with nonempty surplus sits above `Kl(Maybe)`, and the
kernel survives it (the hole holds at the memoryful codomain). So the apophatic model is a base of a tower,
not a terminus. This qualifies only the canonicity-as-uniqueness reading of the model layer; freeness
(`embed_out_of_base`, `maybe_free_pointed`) stands, and the kernel and boundary are untouched. -/
theorem canonicity_under_pressure :
    (∃ m : Mem Unit, ∀ b, (memLevel Unit).emb b ≠ m)
    ∧ (∀ (X : Type) (c : X → X → Mem Unit), ¬ Function.Surjective c) :=
  ⟨memory_is_the_surplus, fun _ c => kernel_survives_memory c⟩

/-! ## The verdict

Part 1: the apophatic model is a genuine base. `memLevel` is a section with retraction
(`restrict_embed_id`), and the surplus is nonempty (`memory_is_the_surplus`): a real Writer extension, not a
trivial relabelling. Memory is the first surplus.

Part 2: memory is the surplus, the nonempty logs the base cannot express, and the kernel survives it
(`kernel_survives_memory`): the hole is uniform, the verdict does not discriminate on memory.

Part 3: the grade does not apply to unbounded memory (`unbounded_memory_is_infinite`); with a bounded log it
is defined (`grade_of_bounded_memory`, three) and adds under composition (`memory_over_memory_adds`). Memory
is a surplus, but additive, like every other cataphatic level, so it buys no magnitude.

Part 4: freeness stands (`embed_out_of_base`); only the canonicity-as-uniqueness reading is qualified. The
apophatic model is the base of a cataphatic tower, not the only model (`canonicity_under_pressure`), and this
concerns the model layer alone: the kernel still holes uniformly, the boundary is untouched.

The verdict: yes, `Kl(Maybe)` is the base of a cataphatic tower, and memory is its first surplus, genuine but
additive. This qualifies the model layer's canonicity reading without touching freeness, the kernel, or the
boundary. Nothing here is about P vs NP; no complexity class, no separation. -/

end Chiralogy.ModelTower
