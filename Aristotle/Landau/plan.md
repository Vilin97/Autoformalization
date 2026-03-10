# Plan — Cycle 62

## Status summary

- **Sorry count**: 0
- **Files**: 21 files, 7,895 lines
- **Heartbeat overrides**: 1 (`synthInstance.maxHeartbeats 160000`)
- **Linter warnings**: 6 unused simp args (Section3Helpers), 2 unused vars (Section3Helpers + Defs), 1 refine' (VelocityDecayInstance), 3 multiGoal (Section3Helpers), ~20 long lines
- **Critique verdict**: CONDITIONAL ACCEPT (conditions: fix MEMORY.md, harden /commit)
- **Build regression fixed**: `linarith` → `nlinarith [Real.pi_pos]` in Defs.lean

## Active multi-cycle strategies

### Harden build verification (NEW)
Cycle 61 committed broken code masked by cache. The `/commit` command must force-recompile modified files. This cycle: update commit command + fix MEMORY.md.

### Clean up linter warnings (ongoing)
Section3Helpers has 6 unused simp args + style issues. Chip away each cycle.

## This cycle's work items

### 1. Fix all unused simp args in Section3Helpers.lean (`/simplify`)
- **Why**: Critique #16. Six specific warnings with exact line numbers.
- **Approach**: Remove each unused argument, rebuild to verify.
- **Files**: `Aristotle/Landau/main/Section3Helpers.lean`
- Lines 544-546: remove `Pi.single_apply`
- Line 552: remove `Finset.sum_add_distrib`
- Line 606: remove `mul_assoc`
- Line 607: remove `Fin.sum_univ_three`

### 2. Fix unused variables and refine' (`/simplify`)
- **Why**: Critique #18. Quick wins.
- Line 618 in Section3Helpers: unused `hn_pos`, `hρ`
- Line 192 in Defs.lean: unused `hg_int`
- Line 21 in VelocityDecayInstance.lean: `refine'` → `refine`

### 3. Fix MEMORY.md (`/simplify`)
- **Why**: Critique #19. Blocking ACCEPT condition. Claims 22 files/8,300 lines vs actual 21/7,895.

### 4. Harden `/commit` command (`/simplify`)
- **Why**: Critique #20. Prevent build regressions.
- **Approach**: Add `lake env lean` verification step for modified `.lean` files.

### 5. Explore C^∞ → C^k weakening (`/strengthen`)
- **Why**: Critique #9. The proof uses at most C² spatial and finite-order velocity.
- **Approach**: Audit `ContDiff ℝ ⊤` usage in proof chain to determine minimum regularity.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| #6: 5 files over 600 lines | Code quality | TorusInstance (1162) most pressing |
| #8: No non-equilibrium VDC instance | Epistemic | Hard |
| #9: C^∞ → C^k | Epistemic | Start exploration this cycle |
