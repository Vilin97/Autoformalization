# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Formalization of Grothendieck's Vanishing Theorem (Hartshorne III, Theorem 2.7) in Lean 4 with Mathlib. The main theorem states: for a Noetherian topological space X of dimension n and any sheaf F of abelian groups on X, H^i(X, F) = 0 for all i > n.

- **Lean**: 4.28.0 (`lean-toolchain`)
- **Mathlib**: v4.28.0 (via `lakefile.toml`)
- **Package name**: `aristotle`

## Build Commands

```bash
# Full build (uses cached .olean files)
lake build

# Verify a single modified file (IMPORTANT: lake build may use stale .olean cache)
lake env lean Aristotle/GrothendieckVanishing/main/SetupCore.lean

# Rebuild from scratch (rarely needed; slow)
lake clean && lake build
```

**Critical**: `lake build` uses cached `.olean` files and may not recompile modified files. Always verify modified files with `lake env lean <file>` before committing.

## CI & Branch Protection

GitHub Actions runs `leanprover/lean-action@v1` on every push/PR (`.github/workflows/lean_action_ci.yml`). Documentation is deployed via `doc-gen4` to GitHub Pages.

**The `grothendieck-vanishing` branch is protected.** Direct pushes are blocked. Agents work on the persistent `wip/grothendieck-vanishing` branch and push there freely. A single PR (`wip/grothendieck-vanishing` → `grothendieck-vanishing`) stays open with auto-merge enabled and merges automatically once the `build` CI check passes. See `/commit` for the full workflow.

## Code Structure

Entry point: `Aristotle.lean` → imports `Aristotle.Basic` + `Aristotle.GrothendieckVanishing.main.main`

All theorem files live in `Aristotle/GrothendieckVanishing/main/`. The proof proceeds by well-founded induction on Krull dimension:

```
GrothendieckVanishing.lean    ← Main theorem (assembles all cases)
├── DimZeroVanishing.lean     ← Irreducible dim=0: constant sheaf is flasque
│   └── ConstantSheafFlasque.lean
├── IrreducibleStep.lean      ← Irreducible dim≥1 (uses IrreduciblePosVanishing)
│   └── FiniteGeneratorReduction.lean
├── ClosedOpenDecomposition.lean ← Reduction to irreducible spaces
│   └── ReducibleVanishing.lean  ← Reducible case via Finset.induction
└── (shared infrastructure)
    ├── SetupCore.lean         ← Core: category instances, FlasqueVanishing, ClosedImmersionSES
    ├── Setup.lean             ← Wrapper theorems (contains IrreduciblePosVanishing sorry)
    ├── ClosedImmersion.lean   ← Closed immersion counit/stalk
    ├── ZeroOutside.lean       ← Extension-by-zero sheaf machinery
    ├── CohomologyIso.lean     ← H'(⊤, F) ≅ H(F) isomorphisms
    └── Auxiliary.lean         ← Topology/dimension helpers
```

## Lean Options (from lakefile.toml)

- `relaxedAutoImplicit = false` — all implicit arguments must be declared
- `pp.unicode.fun = true` — pretty-prints `fun a ↦ b`
- Several Mathlib linters disabled (simpArgs, unusedTactic, unreachableTactic)

## Heartbeat Discipline

Never increase `maxHeartbeats` above 200000 (the default). If a proof exceeds this, refactor it into smaller lemmas instead. Existing violations in SetupCore.lean are technical debt, not precedent.

## Automated Proving Infrastructure

- **Aristotle MCP server** (`tools/aristotle-mcp-server.py`): submits lemmas to an external automated prover
- **Aristotle I/O**: `aristotle-in/` (submissions), `aristotle-out/` (results), `aristotle-jobs.json` (tracking)
- **Slash commands**: `/prove` (hands-on proving), `/plan` (work planning), `/critique` (adversarial review), `/check-aristotle` (poll job status), `/submit-aristotle` (submit to prover)

## Remaining Work

1 sorry remains in `IrreducibleStep.lean` (Mathlib API gap):
1. `cohomology_vanishing_of_finitelyGenerated_vanishing` (Step 3A) — Hartshorne 2.9, cohomology commutes with filtered colimits
