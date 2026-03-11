# Plan — Cycle 69

## Status summary

- **Sorry count**: 1 (in `CoulombConcreteTheorem42_nonvacuous`)
- **Files**: 22 files, ~8,300 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: CONDITIONAL ACCEPT — close (10) hVlasov
- **Aristotle jobs**: 0 pending

## Active multi-cycle strategies

### Non-vacuousness theorem (cycles 64–69)
1 remaining sorry goal:

| Goal | What to prove | Difficulty | Approach |
|------|---------------|------------|----------|
| (10) hVlasov | `0 = ν * LandauOperator coulombKernel eM` | **Medium** | Integrand vanishes: A(z)·z = 0 |

## This cycle's work items

### 1. Prove sorry (10) hVlasov — Maxwellian in kernel of Landau operator (`/prove`)

- **File**: `CoulombConcreteTheorem42.lean` line ~704
- **Mathematical argument**:
  1. LHS of Vlasov = 0 (f constant in x, E=B=0, so spatial transport and force terms vanish)
  2. RHS = ν * LandauOperator coulombKernel eM v
  3. The integrand in LandauOperator is:
     `mulVec A(v'-w) (eM(w) · vGrad eM v' - eM(v') · vGrad eM w)`
  4. For Maxwellian: `vGrad eM v = -(v/T) · eM(v)` (componentwise)
  5. So the bracket = `eM(v')·eM(w) · (-(v'-w)/T)` = scalar × `(v'-w)`
  6. Key property: `mulVec (landauMatrix Ψ z) z = 0` because (|z|²I - zzᵀ)·z = 0
  7. Hence integrand = 0, integral = 0, vDiv of 0 = 0

- **Sub-lemmas to prove**:

  **Sub-lemma A** (projection annihilation): `mulVec (innerLandauMatrix z) z = 0`
  - Proof: `(normSq z • I - vecMulVec z z) *ᵥ z = normSq z • z - (zᵀz) • z = 0`

  **Sub-lemma B** (Landau matrix annihilation): `mulVec (landauMatrix Ψ z) z = 0`
  - Proof: `Ψ(|z|) • (innerLandauMatrix z) *ᵥ z = Ψ(|z|) • 0 = 0`

  **Sub-lemma C** (integrand vanishes): For eM = equilibriumMaxwellian:
  `mulVec A(v-w) (eM(w) • vGrad eM v - eM(v) • vGrad eM w) = 0`
  - Uses: `vGrad eM v i = -(v i / T) * eM(v)`, then bracket simplifies to scalar × (v-w)

  **Sub-lemma D** (LandauOperator vanishes): `LandauOperator coulombKernel eM v = 0`
  - Uses sub-lemma C to show the integrand is 0, hence integral is 0
  - Then vDiv of zero function is 0

  **Final step**: Show LHS = 0 = ν * 0 = RHS

### 2. Extract general CLM lemmas to shared file (`/simplify`)
- Move `iteratedFDeriv_clm_zero` and `norm_iteratedFDeriv_one_clm` from CoulombConcreteTheorem42.lean to Section3Helpers.lean or a new helpers file
- Reduces CoulombConcreteTheorem42.lean by ~20 lines

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| #6b: 6 files over 600 lines | Code quality | TorusInstance 816, Defs 785, CoulombConcreteTheorem42 720 |
| 8c: Generalize beyond T³ | Epistemic | Hard — requires abstract manifold theory |
| 8e: Mathlib-upstreamable lemmas | Community | iteratedFDeriv_clm_zero, norm_iteratedFDeriv_one_clm |
