# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-03T15:30Z

## Status Summary
- **CI**: Green (3/3 recent runs pass)
- **Sorry count**: 4 syntactic (3 logical gaps) in `FiniteGeneratorReduction.lean`
- **Files**: 16 files, ~5425 lines
- **Oversized files**: 4 over 600-line limit (FiniteGeneratorReduction 741, ZeroOutside 733, SheafStalkAlgebra 688, FlasqueVanishing 616)
- **Docs**: Blueprint 404 (P1, unfixed for 2 cycles)
- **CLAUDE.md**: Sorry count FIXED this cycle (was claiming 1, now correct at 4)

## Active Multi-Cycle Strategies

1. **Ext/colimit commutation gap**: All 4 sorry's relate to Hartshorne III Lemma 2.9 (Ext commutes with filtered colimits of mono diagrams). Mathlib v4.28.0 lacks universal δ-functors, Čech cohomology, and Godement resolutions. Three approaches under consideration:
   - (a) Build effaceable δ-functor theorem from scratch (~300 lines)
   - (b) Prove section-level colimit factoring directly via Mathlib's existing colimit preservation API
   - (c) Restructure to eliminate dead branches and reduce sorry count without closing the core gap

2. **File size reduction**: IrreducibleStep was 1263→594 (split into SheafStalkAlgebra). But SheafStalkAlgebra (688), ZeroOutside (733), FiniteGeneratorReduction (741) are now over limit. Need further splits.

## This Cycle's Work Items

1. **[/prove] Verify `#print axioms` for main theorem** (P1, critique issue #4)
   Run `#print axioms GrothendieckVanishing` to confirm `sorryAx` is present (expected) and no other unexpected axioms exist. The `lean_verify` tool's clean report is suspicious.

2. **[/prove] Attempt sorry #4 (line 597): section-level colimit factoring** (P1)
   This sorry needs: sheafToPresheaf ⋙ evaluation preserves filtered colimits for sheaves on topological spaces. Search Mathlib for `PreservesFilteredColimits` instances on `sheafToPresheaf` and `evaluation`. If Mathlib has these, the sorry is closable. If not, check if objectwise colimit of sheaves = sheaf colimit at each stalk.

3. **[/prove] Attempt sorry #3 (line 254): eliminate dead branch** (P1)
   This is claimed "dead at call site" since `ext_comm_filtered_colimit_mono` is only called with `n ≥ dim(X)+1 ≥ 2`. If we can restructure the proof to pass `n' + 1` instead of `n` to `ext_comm_filtered_colimit_mono`, the dead branch may be eliminable. Alternatively, add `(hn : n ≥ 1)` hypothesis and prove the n=0 case separately at the call site.

4. **[/simplify] Split FiniteGeneratorReduction.lean** (P2)
   At 741 lines, the largest file. Natural split point at line 260 (end of Ext helpers) / line 600 (start of FinsetGenerated section). Extract `FinsetGenerated` section (lines 600-741) into a new file `FinsetGeneratedSheaf.lean`.

5. **[/prove] Attempt sorry #1 (line 207) and #2 (line 215)** (P1)
   These are the hardest sorry's (Ext colimit commutation core). If sorry #4 is closed, sorry #1 may become tractable via the connecting map argument. Sorry #2 (hQprov) requires the full recursive IH — attempt decomposition into sub-lemmas.

## Backlog
- P1: Fix docs/blueprint 404 (requires merge to protected branch → main)
- P2: Split ZeroOutside.lean (733 lines)
- P2: Split SheafStalkAlgebra.lean (688 lines)
- P3: Split FlasqueVanishing.lean (616 lines, borderline)
- P3: Universe polymorphism audit
- P4: Mathlib upstream PRs (FlasqueVanishing, constantSheaf_flasque_of_irreducible)
