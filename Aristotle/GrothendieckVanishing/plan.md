# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-04T22:00Z

## Status Summary

- **Sorry count**: 1 in `FiniteGeneratorReduction.lean`
  - Line 203: `hmono_transitions` (load-bearing false — asserted for all diagrams but FALSE for the recursive quotient diagram Q)
- **Files**: 16 `.lean` in `main/`, ~5740 total lines
- **CI**: Running (commit c2543f6)
- **Aristotle**: 1 job IN_PROGRESS (`sheafH_colim_v2.lean`, job `6ecc7b79`, 6%), 1 expired

## Fundamental Obstacle (unchanged from prior cycle)

The dimension-shifting proof for "H^n commutes with filtered colimits" creates a quotient diagram Q with non-mono coprojections (`ker(Q.map φ) ≅ coker(Y'.map φ) ≠ 0` by the snake lemma). The recursive IH call requires `hmono_transitions` for Q, which is provably FALSE. The sorry at line 223 is "load-bearing false" — it makes a false assertion that is accepted by `sorry`.

Valid alternative approaches (none yet in Mathlib):
1. Čech cohomology (Čech = derived on Noetherian spaces)
2. Universal δ-functor (T^0 = Hom preserves colimits → T^n = Ext^n)
3. Gabriel's theorem (filtered colimits of injectives are injective in locally Noetherian categories)

## This Cycle's Work Items

Items 1-3 from previous cycle are DONE (commit c2543f6).

### 1. Check Aristotle results (`/check-aristotle`)
- Job `6ecc7b79` IN_PROGRESS (6% as of 21:47Z). Check for completion.

### 2. Attempt `hmono_transitions` via restructured proof (`/prove`)
- Strategy: Add `hmono_transitions` as a hypothesis to the theorem signature.
  At the call site, provide it via `finsetGenFunctor_mono`.
  For the recursive IH call on Q, use a separate helper lemma.
- The helper must prove H^n(colim Q_j) = 0 from H^n(Q_j) = 0 WITHOUT mono transitions.
- This requires a fundamentally different proof (not dimension shifting).
- Spend at most 20 min; if blocked, wait for Aristotle.

## Backlog

- **P1**: Blueprint deployment — no workflow exists. Not blocking correctness.
- **P2**: Strengthen `Subsingleton (Sheaf.H F n)` to `IsZero (Sheaf.H F n)`.
- **P3**: Upstream `PresheafFilteredColimit.lean` to Mathlib.
- **P3**: Upstream `ConstantSheafFlasque.lean` to Mathlib.
