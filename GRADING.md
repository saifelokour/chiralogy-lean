# Grading and discipline

Every claim carries one of four grades.

- **●● theorem**: a machine-checked Lean theorem, axioms within `{propext, Classical.choice, Quot.sound}`.
  This is the only grade that asserts a fact of the framework.
- **● reading**: a faithful interpretation of a ●● theorem in a domain's language. A correspondence, not a
  proof; it may be contested without touching the theorem.
- **○ imported**: data the framework does not supply: the target, and every measure or magnitude. Handed
  back to whoever uses the framework.
- **✗ absent**: a structure the framework does not have. Stated as such, never smuggled.

## Discipline

- **No `sorry`, no new axioms.** Every theorem's `#print axioms` must be within the baseline. Verify the
  repository as a unit.
- **A member must earn its place.** A model member is admitted only if it buys structural content the
  kernel does not force *and* is used. Partiality is the one codomain member; it opens the partial mode, the
  arrangement, and a coherence structure.
- **Refusals are graded, not catalogued.** A result that turned out to be a refusal survives only as the
  positive theorem it justifies. There are no catalogues of dead ends.
- **Elegance is the alarm.** The most seductive claim is the one to distrust hardest. A universal property
  is a checked factorization or a cited standard result, never a suggestive restatement. A prohibition is an
  impossibility, never a smuggled value.
- **Precise and concise.** The math speaks; prose is minimal. Doc-comments are one or two lines. No
  companion prose files past this one and the README.

## The five-step template

1. Re-level: find the object inside a domain that classifies its own kind.
2. Check membership: five data, two tests; is it a genuine two-place self-classification or an external
   judge?
3. Locate it in the trichotomy: no-self-model, total, or partial.
4. Derive its structure; separate what is derived from what is imported.
5. Grade every claim, and refuse the flattering reading.
