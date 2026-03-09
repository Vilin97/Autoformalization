# Log

## 2026-03-09 02:28 UTC — CoulombConcreteTheorem42 session (continued)

### Accomplished
- **CoulombConcreteTheorem42.lean**: 0 errors, 16 sorry warnings. File structure complete.
  - Proved: `schwartz_log_bound`, `schwartz_norm_pow_integrable`, `spatial_transport_integrable` (modulo 1 AEStronglyMeasurable sorry), `force_fderiv_log_component_integrable`, `force_transport_integrable_coulomb`, `force_ibp_f_dg_integrable_coulomb`, `force_ibp_fg_integrable_coulomb`, `spatial_transport_joint_integrable` (modulo 2 AEStronglyMeasurable sorry's)
  - Proved: `coulomb_landauMatrix_entry_le` (Coulomb matrix bound |A_{ij}(z)| ≤ eucNorm(z)⁻¹)
  - Proved: `pi_norm_le_eucNorm` and `coulomb_landauMatrix_entry_le_pi` (bridge to Pi norm)
  - Key sorry: `inv_norm_schwartz_integrable` — ‖v-w‖⁻¹ × Schwartz is integrable in ℝ³
  - 12 VelocityDecayConditions fields still sorry'd (most reduce to `inv_norm_schwartz_integrable`)
  - 3 AEStronglyMeasurable sorry's (joint x,v regularity — honest mathematical gaps)

### Aristotle jobs submitted (8 total, 1 completed)
- `inv_norm_schwartz_from_local` (1ba752be) — **COMPLETE**: proves `Integrable (fun w => ‖v-w‖⁻¹ * g w)` assuming local integrability of ‖·‖⁻¹ on B(0,1) + Schwartz decay of g
- `inv_norm_schwartz_integrable` (403eee35) — IN_PROGRESS: direct approach
- `inv_norm_local_integrable` (3dc1b4dc) — IN_PROGRESS: proves `IntegrableOn ‖·‖⁻¹ (closedBall 0 R)` in ℝ³
- `inv_norm_schwartz_product_integrable` (fb8f0314) — IN_PROGRESS: joint product integrability
- `psd_continuous_coulomb` (14300a69) — IN_PROGRESS: PSD integrand continuity despite Coulomb singularity
- `landau_flux_integrable_coulomb` (7d8c95bb) — IN_PROGRESS: Coulomb flux integrability
- `force_schwartz_log_integrable` (23440e88) — IN_PROGRESS
- `force_entropy_integrable` (b85fc67d) — IN_PROGRESS

### Key insight
The Coulomb kernel Ψ(r) = r⁻³ makes |A_{ij}(z)| ≤ ‖z‖⁻¹ (proved), which is locally integrable in 3D. Combined with Schwartz decay of f, all collision integrands are integrable. The chain is:
1. `inv_norm_local_integrable` (Aristotle, running) → ‖·‖⁻¹ integrable on B(0,1) in ℝ³
2. `convolution_local_int_schwartz` (Aristotle, proved!) → ‖v-w‖⁻¹ × Schwartz(w) integrable
3. → `inv_norm_schwartz_integrable` → all collision fields in VelocityDecayConditions

### Remaining sorry's (16 total)
- 1 key: `inv_norm_schwartz_integrable` (awaiting Aristotle)
- 12 VelocityDecayConditions fields (most follow from the key once proved)
- 3 AEStronglyMeasurable (honest gaps: joint x,v regularity of gradX)
