# Structural Compression Ideas

Beyond the mechanically-derived Phase 1-4 backlog, these are higher-leverage
structural opportunities found by reading the codebase. The planner should
consult this file when picking the next task — particularly when the mechanical
backlog has only small-yield items left.

Each idea lists: the leverage estimate, an entry-point cycle that's small
enough to fit a single compress-loop iteration, and dependencies on other
ideas (since wrong order = redoing work).

---

## Idea 1: Sheafify the entire `PresheafFilteredColimit*` cluster

**Leverage:** 400-700 raw LOC. Highest-yield single initiative remaining.

**Why:** The three files `PresheafFilteredColimit{,Core,General}.lean` total
**2,273 lines (33% of the codebase)** and host 90 of the 132 `IsSheaf` /
`Presheaf` occurrences in the project. The naming reveals a bottom-up design:
build everything on presheaves, then pay a long `*Core` file to bridge
presheaf-colimits to sheaf-colimits via `sheafToPresheaf` round-trips.
Mathlib already provides this bridge for free (`Sheaf.colimit`, `presheafToSheaf`
preserves colimits). A top-down rewrite that takes `J' ⥤ Sheaf …` directly and
produces `H^n(colim Fⱼ) ≃ colim H^n(Fⱼ)` at the sheaf level should delete the
entire `_presheaf` ladder.

**Entry-point cycle (small enough for one iteration):** Replace the four
remaining `_presheaf` decls in `PresheafFilteredColimitCore.lean`
(`sheafH_filtered_colimit_succ_inj_subsingleton_presheaf`,
`sheafH_filtered_colimit_surj_presheaf`,
`sheafH_filtered_colimit_comparison_presheaf`,
`sheafH_filtered_colimit_comparison_succ_compatibility_presheaf`)
with sheaf-level analogues. Update callers in `PresheafFilteredColimit.lean`.
Expect -150 to -250 raw LOC for this entry cycle alone.

**Dependencies:** None. Should run before Idea 6 (golf) since most golf targets
live in these files and will be rewritten.

**Beware:** Many cross-file callers — keep the public name stable or refactor
all callers in the same cycle. Reviewer-flagged lemmas like
`isFlasque_filtered_colimit` should already be sheaf-typed (cycle 5 did that).

---

## Idea 2: Collapse `class IsFlasqueSheaf` to a `def`

**Leverage:** 30-50 raw LOC + cleanup of wrapper-conversion noise scattered
across `FlasqueVanishing.lean`.

**Why:** `class IsFlasqueSheaf F : Prop` (FlasqueVanishing.lean:34) is a
one-field wrapper around `IsFlasque F.val` — `epi_map` is the only field.
The auto-generated `IsFlasqueSheaf.casesOn`, `.rec`, `.recOn` are confirmed
unused (Phase-2 list). The class adds nothing over `def IsFlasqueSheaf F :=
IsFlasque F.val` or even direct use of `IsFlasque F.val` everywhere.

**Entry-point cycle:** Convert `class IsFlasqueSheaf` to `def`, remove the
three auto-generated decls, and update the ~20 use sites in `FlasqueVanishing`
+ `IrreducibleStep` + `ConstantSheafFlasque`. Watch for instance resolution —
some sites may rely on `[IsFlasqueSheaf F]` as a typeclass argument; those
become explicit hypotheses.

**Dependencies:** None. Independent of Idea 1.

---

## Idea 3: Inline `ULiftInt.lean` (28 lines)

**Leverage:** 20-28 raw LOC.

**Why:** `ULiftInt.lean` defines one `noncomputable def
uliftZMultiplesAddEquiv` and one `@[simp]` lemma. Used in 5 sites total
(CohomologyAPI:541, ZeroOutside:180/201/202/220). Mathlib likely already has
this equivalence (`AddEquiv.ulift`, `ULift.addEquiv`, or a `homAddEquiv` on
constant `ULift ℤ`).

**Entry-point cycle:** Run `lean_leansearch` for "additive equivalence
ULift Int", "homAddEquiv ULift", "ULift addEquiv". If a Mathlib lemma exists,
replace all 5 call sites and delete the file. If not, inline the def as a
local `let` or fold into `ZeroOutside.lean` (4 of 5 sites are there).

**Dependencies:** None.

---

## Idea 4: Merge `ZeroOutsideFinset.lean` into `ZeroOutside.lean`

**Leverage:** 10-20 raw LOC + one fewer file.

**Why:** `ZeroOutsideFinset.lean` (77 lines, 3 decls) is used only by
`FinitelyGeneratedVanishing.lean`. Same namespace as `ZeroOutside.lean`
(`TopCat.Presheaf`). Splitting them costs an `import` line, reopens the
namespace block, and adds module-doc boilerplate that yields no organisational
benefit.

**Entry-point cycle:** Move `finsetCoproductInclGen`, `finsetImageInclGen`,
`finsetImageInclGen_comp_ι`, `finsetImageInclGen_mono` into the bottom of
`ZeroOutside.lean`. Update the import in `FinitelyGeneratedVanishing.lean` and
`GrothendieckVanishingOverview.lean`. Delete `ZeroOutsideFinset.lean`.

**Dependencies:** None.

---

## Idea 5: Upstream parts of `TopologicalKrullDim.lean` to Mathlib

**Leverage:** 150-200 raw LOC (long-tail; depends on PR review timing).

**Why:** Theorems like `topologicalKrullDim_eq_iSup_height`,
`topologicalKrullDim_add_one_eq_iSup_height_add_one`,
`height_add_one_le_topologicalKrullDim_of_isClosed_of_ne_univ` are pure
topology with no sheaf content. They belong in
`Mathlib.Topology.KrullDimension`. The unused `height_eq_order_height`,
`height_mono`, `topologicalKrullDim_eq_bot_iff_isEmpty` go away naturally
during the upstream PR's review (Mathlib reviewers will flag them).

**Entry-point cycle:** This is NOT a single compress-loop task — it's an
out-of-band Mathlib PR. The compress loop should not pursue this directly,
but should NOT golf or restructure these theorems either (avoid wasted work).
Mark `TopologicalKrullDim.lean` declarations as out-of-scope until the
upstream PR is merged.

**Dependencies:** Coordination with user; not a loop task.

---

## Idea 6: Run Aristotle (auto-prover) on the highest-ratio Phase-4 golf candidates

**Leverage:** Variable per-target, potentially 200-500 raw LOC across the top
20 candidates.

**Why:** The 70 untouched Phase-4 golf items will yield ~3-15 raw LOC each
when done by hand. The Aristotle MCP `submit_directory(prompt=...)` accepts
free-form prompts including "Golf this proof to the minimum tactic count" —
the auto-prover often finds dramatically shorter proofs (`omega`, `aesop`,
single `simp` with the right lemma set) that humans don't try.

**Entry-point cycle:** Pick a Phase-4 ratio outlier in a self-contained file
(NOT one that Idea 1 will rewrite). Strong candidates by body/sig ratio AND
file independence: `finsetGenCocone_isColimit` (body/sig 25.5, in
`FinitelyGeneratedVanishing.lean`), `zeroOutside` (17.0, in `ZeroOutside.lean`),
`isFlasque_of_injective` (9.0, in `FlasqueVanishing.lean`). Submit the file
to Aristotle with the prompt:
"Golf the proof of `<name>` in this file. Minimize tactic count. Do not
change the statement, signature, or any other declaration. Reply with just
the rewritten proof body."

**Dependencies:** Defer most candidates until AFTER Idea 1 — the
`PresheafFilteredColimit*` items will be rewritten or deleted entirely.

---

## Recommended sequence

1. **Idea 1** (filtered-colimit sheafification) — biggest yield, blocks others
2. **Idea 5** (Mathlib PR) — runs in parallel, out-of-band
3. **Idea 2** (IsFlasqueSheaf collapse) — independent
4. **Idea 3 / Idea 4** (small file consolidations) — independent, bite-sized
5. **Idea 6** (Aristotle golf) — only after Idea 1 reduces the target set
