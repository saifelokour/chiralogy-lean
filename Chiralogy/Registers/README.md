# Registers

A **register** is an object of `Chiralogy` presented in a domain's language: a carrier of things, a
distinction space, and a map by which the things classify their own kind. To add one, supply the object
condition: the five data (carrier, distinction space, a proof the space can differ, the classification,
non-degeneracy) and pass the two tests (the payload fires; non-degeneracy holds). The **target** is imported
(○).

A **translation** between registers is a morphism `(f, g)`. A **seam** is where a translation fails to be
faithful: a morphism whose value map `g` is not injective, losing classification structure.

This directory is the fork surface. The first register is physics (GR / QM), a READING at
`Chiralogy/Registers/Physics.lean`. Add objects, not prose.

Registers, and anything that graduates, are precise and concise, not prosy. State the theorem, its grade,
and its scope. Doc-comments are one or two lines. No narrative, no verbose motivation: the math carries it.
Grade every claim (`GRADING.md`).
