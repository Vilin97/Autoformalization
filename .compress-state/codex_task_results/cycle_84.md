## Gate Repair

Repaired the cycle by golfing
`sheafH_filtered_colimit_h1_cokernelFunctor` in
`Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`.
The `map_id` and `map_comp` proofs now rewrite with one sheaf-level functor-law
fact each, avoiding the duplicated evaluated top-sections transport facts.

Verification passed:

- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `python3.9 scripts/normalized_loc.py`: `4104`

Normalized LOC decreased from the cycle-start baseline `4115` to `4104`
(`-11`). `lake build` was not run because no Lean file was added, deleted, or
renamed.
