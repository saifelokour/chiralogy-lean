# Experiments

New graded work: probes that test the framework against a domain or extend it. This is where new results go;
graduated probes are archived under `archive/` (physics at `archive/PhysicsRegister.lean`, and the heterology
arc that graduated the cataphatic arm). Further probes are the formal silence past the boundary until they
arrive.

Discipline (from `GRADING.md`): no `sorry`, no new axioms, every theorem's `#print axioms` within
`{propext, Classical.choice, Quot.sound}`. A model member is admitted only if it buys structural content and
is used. Refusals survive only as the positive theorem they justify. Elegance is the alarm: the most
seductive claim is distrusted hardest. Follow the five-step template.

## Graduation

A positive result does not stay in Experiments. It graduates to the layer
whose test it passes:

    Kernel     holds of every object from the bare form c : X → X → B
    Model      needs the canonical extension (trivial on total objects)
    Protocol   refines the object condition (the data, the tests, the payload)
    Registers  an actual system instantiates the structure (●, defeasible)

Sort by structural scope, not by where the result was found. A kernel theorem
noticed while probing a register is still a kernel theorem.

A refusal graduates nothing. It survives only as the positive theorem it
justifies (often a closure result in the layer it probed) and otherwise
stays here as record.

Boundary is presumed singular. A result graduates there only if it is a
target-free ought-not resting on a proven internal impossibility: a move
self-defeating by its own goal, not by any value. Any candidate is presumed
to be the prohibition swelling (the attempt, on the ethics) until it exhibits
a genuine new impossibility. If it rests on a value, it is imported and handed
back. If it is structural, it is Model.

## Form

Experiments, registers, and anything that graduates are precise and concise,
not prosy. State the theorem, its grade, and its scope. Doc-comments are one
or two lines. No narrative, no retelling, no verbose motivation: the math
carries it. A result that cannot be stated concisely is not yet understood.

An experiment states, in order and briefly:
  1. hypothesis: the structure or member proposed
  2. the failure mode: what it is most exposed to
  3. counter-bias: the wanted outcome, named to be distrusted
  4. verdict: per claim, graded (●● / ● / ○ / ✗)
  5. graduation: which layer it passes to, or the residue a refusal leaves
