# Babysit

Run one full cycle of the autonomous autoformalization lifecycle:

1. `/check-aristotle` — Fetch and integrate completed Aristotle proofs
2. `/plan` — Assess current state and produce prioritized work plan
3. `/prove` — Close sorry's directly (decompose into sub-lemmas as needed)
4. `/submit-aristotle` — Submit hard lemmas to Aristotle (if any ready)
5. `/simplify` — Fix code smells, decompose long proofs, reduce heartbeats
6. `/log` — Record what changed
7. `/cleanup` — Delete stale files and dead code
8. `/critique` — Adversarial analysis of current state
9. `/commit` — Commit and push all changes
