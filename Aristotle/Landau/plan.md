# Plan — Cycle 75

## Status summary

- **Sorry count**: 0
- **Files**: 22 files, ~8,400 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Break mega-lines in Section3Helpers.lean (`/simplify`)
- **What**: Break the 20 lines > 200 chars into properly formatted multi-line tactics
- **Why**: Section3Helpers has the worst offender (697 chars). These Aristotle-generated proofs cram many tactics onto one line.
- **Approach**: Read each mega-line, break `;`-separated tactics onto separate lines with proper indentation. Verify build after each file.

### 2. Break mega-lines in NewtonianPotential.lean (`/simplify`)
- **What**: Break 9 lines > 200 chars
- **Why**: Second-worst file for mega-lines

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 7 files over 600 lines | Code quality — ongoing |
| 6c | 1146 semicolons | Code style — partially addressed by line-breaking |
| 6c | 22 more mega-lines (other 4 files) | Code style |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard |
| 8c | Generalize beyond T^3 | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community |
| 8e | Split Defs.lean | Code quality |
