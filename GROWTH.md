# How the Library Grows

This is the operational procedure by which the canonical library is extended. It is the concrete form of the framework's growth method; for why this is the only way the map grows, see the account of the framework as an abstract map in the `chiralogy-spec` repository (`MAP.md`).

The library grows by one loop, run without end: descend into a concrete field, find structure, ascend to what is general, land it in canonical. In this repo that loop is concrete.

## Descent, a survey

Reify: open an `Chiralogy/Experiments/` file, instantiate the kernel in a concrete carrier with a supplied import, and explore. Build witnesses. A survey is a descent into one territory; it makes visible, as concrete Lean fact, structure the abstract library does not yet carry. A survey verdict of DEAD or reduces-to-canonical is a complete result, reported plainly. Most descents find no new general structure, and that is the process working, not failing.

## Ascent, the gates

A survey result is a candidate for canonical only if it passes, in order, each gate reported separately. A later step doing a gate's work implicitly does not count as the gate having run.

1. **Equivalence-check.** Is this already canonical, possibly under another name, possibly strictly more general? The dependency graph hides re-derivations; a result equivalent to an existing theorem looks new until this check. Run it first. Most candidates that feel new fail here.
2. **Statement-comparison.** Is it genuinely new content, or a restatement or packaging of existing theorems?
3. **Generality.** Carrier-general: quantified over the carrier and arity, no fixed carrier, no `decide` or `native_decide` in the proof.
4. **Placement.** Where it lands, what it depends on, whether the edge is clean or redundant.
5. **Axiom audit.** `#print axioms`; within the baseline `{propext, Classical.choice, Quot.sound}`; `sorryAx` and `native_decide` scanned to zero.
6. **Register-neutrality.** The name and statement carry no domain vocabulary; the register reading is spec prose only.

A dry-run wrapper runs all gates and reverts, to decide before committing. A candidate that clears every gate is graduated: it lands in canonical. That is a stroke on the map.

## The compounding payoff

A graduated theorem is carrier-general, so every register that instantiates the kernel inherits it at once, by instantiation. Structure found by descending into one territory sharpens every territory. Ascent is from one field; the descent of the result is to all of them.

## Why it does not finish

The library is never a closed catalog. It cannot be completed, and the reason is not that the work is large but that a completed self-description is the exact object the kernel forbids (`no_total_internal_self_description`, in `Chiralogy/Kernel/Apophatic.lean`): a library that fully described its own structure would be the surjection the hole rules out. The same hole that sits in the kernel is the reason this procedure has no last step. The library's incompleteness and its capacity to grow are one fact.
