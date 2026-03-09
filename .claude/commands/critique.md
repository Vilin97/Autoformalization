You are a hostile reviewer trying to REJECT this formalization. Your job is to find every weakness, gap, and dishonesty. Do not be polite. Do not give credit. Do not soften your language. If you catch yourself writing "mitigating factor" or "well-addressed", stop and ask whether a reviewer would actually accept that mitigation.

Write the full adversarial critique to `Aristotle/Landau/critique.md`.

## Mandatory sections

For EACH of the following, either find a real problem or explicitly state "I found no issue" (do not skip silently):

1. **Sorry's** — List every `sorry` with file:line. For each: is the statement actually true? Could the hypotheses be wrong? Could Aristotle prove the negation? What's the worst-case scenario if this sorry hides a bug?

2. **Hidden axioms** — Every `admit`, `axiom`, `native_decide`, `Decidable.decide` (used unsafely), `sorry` in imported files. Run `lean_verify` on the main theorems. List every axiom beyond `propext`, `Classical.choice`, `Quot.sound`.

3. **Circularity** — Trace the full dependency chain. Is any hypothesis equivalent to the conclusion? Do any "instances" use the conclusion as input? Is VelocityDecayConditions satisfiable by a non-equilibrium distribution for the Coulomb kernel specifically?

4. **Hypothesis audit** — List every hypothesis of the main theorem (explicit + typeclass + VelocityDecayConditions). For each: is it necessary? Is it physically reasonable? Could it be weakened? Is it secretly assuming the conclusion?

5. **Mathematical correctness** — Are there ANY steps where the formalization diverges from the standard mathematical proof?

6. **Code quality** — `maxHeartbeats` above 800000, files over 600 lines, `set_option linter.all false`, Aristotle-generated proofs that are unmaintainable. These are real problems, not cosmetic.

7. **Documentation lies** — Check every numerical claim in docstrings, MEMORY.md, progress.md against reality. Flag every discrepancy.

## Tone

Write as if you are a referee who has been asked "should this paper be accepted?" and your default answer is NO. The formalization must earn your approval through evidence, not through charity.

Do NOT write a "summary" section that softens the critique. End with a verdict: ACCEPT, REVISE, or REJECT, with specific conditions.
