# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-04T06:30Z

## Status Summary
- **Sorry count**: 2 (both in `sheafH_filtered_colimit_aux` in FiniteGeneratorReduction.lean)
- **Files**: 16 `.lean` in `main/`, ~5200 total lines
- **CI**: Green
- **Architecture**: Main theorem `GrothendieckVanishing` → `grothendieck_vanishing_aux` → well-founded induction on Krull dim → `IrreduciblePosVanishing` → `directLimit_cohomology_vanishing` → `sheafH_preserves_filtered_colimits` → sorry

## Remaining Sorry's

### Sorry 1: h_van_Q n=0 (line ~781)
**Goal**: `Subsingleton (Sheaf.H (Q.obj j) 0)` where `Q.obj j = cokernel(c'.ι.app j ≫ ι')`
**Issue**: H^0(Q_j) = Γ(Q_j) = Γ(I/image(f_j)). Since Γ(I) ≠ 0, this is nonzero in general. Dimension shifting fails because H^0(I) ≠ 0.
**Approach needed**: Direct surjectivity argument for H^1 that bypasses h_van_Q at level 0. From SES with mono coprojections: Γ(I) ↠ Γ(Q_j) (via H^1(Y_j)=0), colimit preserves surjection, hence H^1=cokernel=0. BUT this needs mono coprojections which only the top-level call has.

### Sorry 2: h_van_Q n≥1 (line ~791)
**Goal**: `Mono (c'.ι.app j ≫ ι')` 
**Issue**: Provable at the top-level call site (finsetGenFunctor has mono transitions → `IsColimit.mono_ι_app_of_isFiltered` gives mono coprojections → composition with mono ι' is mono). But the theorem is universally quantified, and the recursive IH call on Q doesn't have mono.
**Approach needed**: Either add hmono_trans to the theorem (breaks recursive IH), or find a proof of H^n commuting with filtered colimits that doesn't use dimension shifting (Čech cohomology, functorial injective resolutions).

## Fundamental Obstacle

The dimension-shifting approach for "H^n commutes with filtered colimits" creates a Q-diagram with non-mono coprojections. The Ext LES requires `ShortExact` (hence `Mono`) for the SES `0 → Y_j → I → Q_j → 0`. Without mono, the proof cannot close.

The correct proof (Stacks 009E/Tohoku) uses one of:
1. **Čech cohomology**: Finite covers → finite products → commute with filtered colimits. Needs Čech-to-derived comparison.
2. **Functorial injective resolutions**: Γ commutes with colimits, AB5, cohomology of chain complexes commutes with filtered colimits. Needs chain complex infrastructure.
3. **Compact objects**: Show the constant sheaf Z is compact in derived category, so RHom(Z,-) preserves colimits.

None of these are available in the current codebase or Mathlib.

## Backlog
- P3: FiniteGeneratorReduction.lean at 972 lines (threshold: 600)
- P3: Duplicate dimension-shift lemmas (ext_dimension_shift vs sheafH_dimension_shift_ses)
- P4: Blanket `import Mathlib` in 3 files
