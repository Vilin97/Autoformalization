# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-04T21:55Z

## Status Summary

- **Sorry count**: 2 in `FiniteGeneratorReduction.lean`
  - Line 43: `gabriel_injective_of_filtered_colimit` (dead code, never referenced)
  - Line 223: `hmono_transitions` (load-bearing false — asserted for all diagrams but FALSE for the recursive quotient diagram Q)
- **Files**: 16 `.lean` in `main/`, ~5760 total lines
- **CI**: Green (all 3 recent runs pass)
- **Docs**: Blueprint returns 404 (no deployment workflow exists)
- **Documentation lies**: CLAUDE.md, main.lean, and FiniteGeneratorReduction.lean all claim "1 sorry" — actually 2
- **Aristotle**: 1 job queued (`sheafH_colim_v2.lean`, job `6ecc7b79`), 1 expired

## Fundamental Obstacle (unchanged from prior cycle)

The dimension-shifting proof for "H^n commutes with filtered colimits" creates a quotient diagram Q with non-mono coprojections (`ker(Q.map φ) ≅ coker(Y'.map φ) ≠ 0` by the snake lemma). The recursive IH call requires `hmono_transitions` for Q, which is provably FALSE. The sorry at line 223 is "load-bearing false" — it makes a false assertion that is accepted by `sorry`.

Valid alternative approaches (none yet in Mathlib):
1. Čech cohomology (Čech = derived on Noetherian spaces)
2. Universal δ-functor (T^0 = Hom preserves colimits → T^n = Ext^n)
3. Gabriel's theorem (filtered colimits of injectives are injective in locally Noetherian categories)

## This Cycle's Work Items

### 1. Delete dead code `gabriel_injective_of_filtered_colimit` (`/cleanup`)
- File: `FiniteGeneratorReduction.lean:25-43`
- This theorem is never referenced. It's dead code that inflates the sorry count.
- Deleting it reduces sorry count from 2 → 1 and fixes the documentation lie.
- **Immediate, < 1 min.**

### 2. Fix documentation lies (`/cleanup`)
- `CLAUDE.md:76`: Update sorry description to match reality after item 1
- `main.lean:7-11`: Update sorry list
- `FiniteGeneratorReduction.lean` docstrings: Remove "SOLE sorry" claims
- **Immediate, < 5 min.**

### 3. Delete stale `aristotle-in/sheafH_colim.lean` (`/cleanup`)
- Doesn't compile (broken `constantSheaf` calling convention). Job expired.
- `sheafH_colim_v2.lean` is the replacement (compiles, queued).
- **Immediate, < 1 min.**

### 4. Attempt to prove `hmono_transitions` via restructured proof (`/prove`)
- The sorry at line 223 cannot be closed with the current dimension-shifting approach.
- **Strategy**: Restructure `sheafH_filtered_colimit_aux` to add `hmono_transitions` as a hypothesis propagated from the call site. For the recursive IH call on Q, prove a SEPARATE helper that handles the case where all pieces have vanishing cohomology but coprojections need not be mono.
- This is the hardest item. Spend at most 30 min attempting; if stuck, document the blocking issue and move on.

### 5. Check Aristotle results (`/check-aristotle`)
- Job `6ecc7b79` is queued. Check if completed.

## Backlog

- **P1**: Blueprint deployment — no workflow exists. Not blocking correctness.
- **P2**: Strengthen `Subsingleton (Sheaf.H F n)` to `IsZero (Sheaf.H F n)`.
- **P3**: Upstream `PresheafFilteredColimit.lean` to Mathlib.
- **P3**: Upstream `ConstantSheafFlasque.lean` to Mathlib.
