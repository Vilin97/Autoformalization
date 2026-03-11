# Plan — Cycle 99

## Status summary

- **Sorry count**: 0
- **Files**: 31 files, 9,539 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Eliminate `synthInstance.maxHeartbeats 160000` in CoulombForceTransport.lean (`/simplify`)
- **What**: Issue 6a. The only heartbeat override in the codebase. Try to eliminate it by adding explicit type annotations or restructuring the proof to avoid slow typeclass synthesis.
- **Why**: Eliminates the last heartbeat override, achieving zero `maxHeartbeats` overrides across all 31 files.

### 2. Check unused imports (`/simplify`)
- **What**: Check if any lean files have redundant imports after the recent extraction work (cycles 94-98).
- **Why**: Extractions moved code between files; some imports may now be unnecessary.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 1 file over 600 lines | Defs.lean, can't split per user pref |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | 5 candidates ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
