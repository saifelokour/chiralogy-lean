# Autology

A small, machine-checked framework for **self-classification**: an object is a carrier `X`, a distinction
space `B`, and a map `c : X → X → B` by which the carrier classifies its own kind. The framework is
*autological*: it is an object of itself, subject to its own hole, and forbidden by its own boundary from
claiming completeness.

The theorems are structural facts about the form `c : X → X → B`, universal in reach and verified in the
register of category theory, type theory, Lean, and English: a coordinate system, not a fence, and
re-verifiable in any adequate register. The only incompleteness is Autology's account of itself, which by
its own central theorem has a hole in every register alike (see `INVARIANCE.md`).

## The object

An object is `(X, B, c)`; a morphism `(f, g)` preserves `c`. These form the category `Autology`
(`Kernel/Autology.lean`). Everything else is structure of this category.

## Two absences

The kernel is two structural absences (`Kernel/Obstructions.lean`):

- **No reflexive object**: no `c : X → X → B` is surjective onto its own classifier space (the diagonal
  argument). This is the payload: no object has a complete self-account.
- **No universe classifier**, hence **no right adjoint** to the level shift (the size argument, via the
  paradox term). A right adjoint would produce a small copy of the universe.

They are distinct: the first is about a self-map's surjectivity, the second about a functor. The hole is
arity-1, transports across any distinction space carrying a fixed-point-free endomap, and is uniform -
present on every object and every mode (`Kernel/Hole.lean`).

## Derived versus imported

The kernel and its structure are **derived**. The **model** is the canonical extension: partiality, the
Kleisli category of `Maybe`, characterized by its universal property as the free adjunction of one absence
(`Model/`). The codomain axis closes there: stochastic and substructural distinction spaces collapse
through the diagonal in a cartesian base (`Model/Closure.lean`).

The only **imported** data are the **target** (no standard certifies itself, so every target is defeasible)
and every **measure** or magnitude (degree, rate, count). Order is derived; rate and target are imported.

## The boundary

The framework hands back the ethics: no target, no valuation. It issues exactly one judgment without a
target (`Boundary/Boundary.lean`): the attempt to totalize a self-classification into completeness is
**self-defeating**: it aims at a destination the boundary proves empty, and reaches for it by trading a
true absence for a false verdict, a contradiction by its own goal. The prohibition follows from an
impossibility, not a value; it attaches only to the claim of completeness; and everything reachable (every
target, and whether any cost matters) is handed back.

## The autology

Autology is an object of itself. It is subject to its own hole; it cannot claim completeness; it falls under
its own boundary. That is the point: the framework is not exempt from the structure it describes.

## Structure

```
Kernel/     the category; the two absences; the hole; the three modes; the involution; the dynamics; the scope
Protocol/   membership (the object condition); the payload as a global absence
Model/      partiality (Kl(Maybe)); the codomain closure; arrangement; coherence; the moves
Boundary/   the one prohibition
Registers/  the fork surface (a register is an object in a domain's language; physics is the first)
Experiments/ new graded work (physics is the first probe)
```

`Registers/` is the fork surface and `Experiments/` new graded work; physics is the first of each, and the
rest is the formal silence past the boundary until it arrives. See `GRADING.md` for the grades and the
discipline.

Build: `lake exe cache get` then `lake build`. No `sorry`; every theorem's `#print axioms` is within
`{propext, Classical.choice, Quot.sound}`.

## License

Released under CC BY-SA 4.0: fork it, rewrite it, re-register it in any language or proof assistant; the
one thing you may not do is close it. There is no master copy; see `CONTRIBUTING.md`.
