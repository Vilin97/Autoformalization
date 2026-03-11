# Plan — Cycle 79

## Status summary

- **Sorry count**: 0
- **Files**: 22 files, ~8,841 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Continue semicolon cleanup — short-line semicolons (`/simplify`)
- **What**: Remove mid-line semicolons on lines ≤100 chars by splitting them onto separate lines. Target the worst offenders: Section3Helpers (140), TorusInstance (110), CoulombPSD (70).
- **Why**: 574 plain semicolons remain. Previous cycles removed trailing semicolons and broke long lines with semicolons. Now attack the remaining short-line semicolons in the 3 worst files.
- **Approach**: For lines with `;` that are NOT `<;>` combinators, break at `;` boundaries. This will increase line count but improve readability. Verify build after each file.
- **Note**: Some single-line chains like `simp; ring` or `norm_num; linarith` are idiomatic and short — leave those alone. Focus on lines with 3+ semicolons or lines where the tactics are complex.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 7 files over 600 lines | Code quality — ongoing |
| 6c | 186 lines > 100 chars | Code style — future cycles |
| 6c | ~300 remaining semicolons (after this cycle) | Code style — future cycles |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard |
| 8c | Generalize beyond T^3 | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community |
| 8e | Split Defs.lean | Code quality |
| 8f | Split Section3Helpers.lean (976 lines) | Code quality |
