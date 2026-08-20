/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.DirectCappedOneHandleExtension

/-!
# Core-supported diffeomorphisms of the one-handle

For `ρ < 1`, the radial core `S¹ × {b | ‖b‖ < ρ}` lies away from the attaching
boundary of `S¹ × B³`.  A boundary-relative diffeomorphism supported in this core extends to
the direct-coordinate four-sphere and is literally the identity on the open outer band where the
second Euclidean coordinate block has norm greater than `sphereHandleRadius * ρ`.

This is the support control needed for a later smooth gluing argument.  The global extension is
still only bundled as a homeomorphism in this file.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SplittingSpheres

/-- The radial `ρ`-core in the closed three-ball factor of the one-handle. -/
def oneHandleCore (rho : ℝ) : Set OneHandlePiece :=
  {x | ‖x.2.1‖ < rho}

@[simp]
theorem mem_oneHandleCore {rho : ℝ} {x : OneHandlePiece} :
    x ∈ oneHandleCore rho ↔ ‖x.2.1‖ < rho :=
  Iff.rfl

/-- The radial core is open in the compact one-handle's underlying topology. -/
theorem isOpen_oneHandleCore (rho : ℝ) : IsOpen (oneHandleCore rho) := by
  exact isOpen_lt
    (continuous_norm.comp (continuous_subtype_val.comp continuous_snd)) continuous_const

/-- Boundary-relative diffeomorphisms supported in the radial core form a subgroup. -/
abbrev OneHandleCoreSupportedRelativeDiff (rho : ℝ) :=
  relativeDiffSupportedInSubgroup
    (IM := oneHandlePieceModel)
    (oneHandlePieceModel.boundary OneHandlePiece) (oneHandleCore rho)

/-- A self-diffeomorphism supported in a core of radius at most one automatically fixes the
model boundary and hence determines a core-supported relative diffeomorphism. -/
def oneHandleCoreSupportedRelativeDiffOfDiff
    {rho : ℝ} (hrho : rho ≤ 1)
    (f : TauCeti.Diff oneHandlePieceModel OneHandlePiece ∞)
    (hf : DiffeomorphSupportedIn f (oneHandleCore rho)) :
    OneHandleCoreSupportedRelativeDiff rho := by
  refine ⟨⟨f, ?_⟩, hf⟩
  apply TauCeti.Diffeomorph.mem_fixingSubgroup_of_forall
  intro x hx
  apply hf
  intro hcore
  have hx' : x ∈ (univ : Set (Sphere 1)) ×ˢ
      (Subtype.val ⁻¹' sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    rw [← oneHandlePieceModel_boundary_eq]
    exact hx
  have hnorm : ‖x.2.1‖ = 1 :=
    mem_sphere_zero_iff_norm.mp hx'.2
  exact (not_lt_of_ge (hrho.trans hnorm.ge)) hcore

@[simp]
theorem oneHandleCoreSupportedRelativeDiffOfDiff_apply
    {rho : ℝ} (hrho : rho ≤ 1)
    (f : TauCeti.Diff oneHandlePieceModel OneHandlePiece ∞)
    (hf : DiffeomorphSupportedIn f (oneHandleCore rho)) (x : OneHandlePiece) :
    (oneHandleCoreSupportedRelativeDiffOfDiff hrho f hf).1.1 x = f x :=
  rfl

/-- A core-supported relative diffeomorphism fixes every point at radius at least `rho`. -/
theorem OneHandleCoreSupportedRelativeDiff.apply_eq_of_le_norm
    {rho : ℝ} (f : OneHandleCoreSupportedRelativeDiff rho)
    {x : OneHandlePiece} (hx : rho ≤ ‖x.2.1‖) : f.1.1 x = x := by
  exact f.2 fun hcore ↦ (not_lt_of_ge hx) hcore

/-- The norm of the second Euclidean block of a point of the literal four-sphere. -/
def sphereHandleSecondNorm (q : Sphere 4) : ℝ :=
  ‖(sphereHandleSplitEquiv q.1).2‖

theorem continuous_sphereHandleSecondNorm : Continuous sphereHandleSecondNorm := by
  exact continuous_norm.comp
    (continuous_snd.comp (sphereHandleSplitEquiv.continuous.comp continuous_subtype_val))

/-- On the one-handle face, the second block norm is the scaled ball radius. -/
@[simp]
theorem sphereHandleSecondNorm_oneHandleSphereMap (x : OneHandlePiece) :
    sphereHandleSecondNorm (oneHandleSphereMap x) =
      sphereHandleRadius * ‖x.2.1‖ := by
  rw [sphereHandleSecondNorm, sphereHandleSplitEquiv_oneHandleSphereMap,
    norm_smul, Real.norm_eq_abs, abs_of_pos sphereHandleRadius_pos]

/-- On the cap face, the second block norm is the complementary square-root scale. -/
@[simp]
theorem sphereHandleSecondNorm_sphereHandleCapMap (x : CapPiece) :
    sphereHandleSecondNorm (sphereHandleCapMap x) =
      sphereHandleScale ‖x.1.1‖ := by
  rw [sphereHandleSecondNorm, sphereHandleSplitEquiv_sphereHandleCapMap,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (sphereHandleScale_nonneg _),
    mem_sphere_zero_iff_norm.mp x.2.2, mul_one]

/-- On the closed unit interval, the complementary scale is at least the seam radius. -/
theorem sphereHandleRadius_le_scale {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sphereHandleRadius ≤ sphereHandleScale t := by
  apply (sq_le_sq₀ sphereHandleRadius_pos.le (sphereHandleScale_nonneg _)).mp
  rw [sphereHandleRadius_sq, sphereHandleScale_sq ht0 ht1]
  have ht2 : t ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ ht0 zero_le_one).2 ht1
  rw [sphereHandleRadius_sq]
  nlinarith

/-- The outer spherical band on which a `rho`-core-supported extension is the identity. -/
def sphereHandleOuterBand (rho : ℝ) : Opens (Sphere 4) :=
  ⟨{x | sphereHandleRadius * rho < sphereHandleSecondNorm x},
    isOpen_lt continuous_const continuous_sphereHandleSecondNorm⟩

@[simp]
theorem mem_sphereHandleOuterBand {rho : ℝ} {q : Sphere 4} :
    q ∈ sphereHandleOuterBand rho ↔
      sphereHandleRadius * rho < sphereHandleSecondNorm q :=
  Iff.rfl

/-- The open spherical region strictly inside the one-handle face. -/
def sphereHandleInnerBand : Opens (Sphere 4) :=
  ⟨{x | sphereHandleSecondNorm x < sphereHandleRadius},
    isOpen_lt continuous_sphereHandleSecondNorm continuous_const⟩

@[simp]
theorem mem_sphereHandleInnerBand {q : Sphere 4} :
    q ∈ sphereHandleInnerBand ↔
      sphereHandleSecondNorm q < sphereHandleRadius :=
  Iff.rfl

/-- When `rho < 1`, the inner one-handle band and the outer identity band form an open cover of
the entire four-sphere. -/
theorem sphereHandleInnerBand_union_outerBand {rho : ℝ} (hrho : rho < 1) :
    (sphereHandleInnerBand : Set (Sphere 4)) ∪ sphereHandleOuterBand rho = univ := by
  ext q
  constructor
  · exact fun _ ↦ mem_univ q
  · intro _
    by_cases hq : sphereHandleSecondNorm q < sphereHandleRadius
    · exact Or.inl hq
    · apply Or.inr
      have hrho' : sphereHandleRadius * rho < sphereHandleRadius := by
        nlinarith [sphereHandleRadius_pos]
      exact hrho'.trans_le (le_of_not_gt hq)

/-- Smoothness on the inner-band set is equivalent to smoothness of the literal restriction to
the corresponding open subtype. -/
theorem contMDiffOn_sphereHandleInnerBand_iff_restrict
    (F : Sphere 4 → Sphere 4) :
    ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ F
      sphereHandleInnerBand ↔
    ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun q : sphereHandleInnerBand ↦ F q.1) := by
  constructor
  · intro h q
    apply contMDiffAt_subtype_iff.mpr
    exact (h q.1 q.2).contMDiffAt (sphereHandleInnerBand.2.mem_nhds q.2)
  · intro h q hq
    have hsub := h.contMDiffAt (x := ⟨q, hq⟩)
    exact (contMDiffAt_subtype_iff.mp hsub).contMDiffWithinAt

/-- If `rho < 1`, the open outer band contains the entire cap face, hence in particular an open
neighborhood of the gluing locus. -/
theorem sphereHandleCapMap_mem_outerBand {rho : ℝ} (hrho : rho < 1)
    (x : CapPiece) : sphereHandleCapMap x ∈ sphereHandleOuterBand rho := by
  rw [mem_sphereHandleOuterBand, sphereHandleSecondNorm_sphereHandleCapMap]
  have hscale : sphereHandleRadius ≤ sphereHandleScale ‖x.1.1‖ :=
    sphereHandleRadius_le_scale (norm_nonneg _)
      (mem_closedBall_zero_iff.mp x.1.2)
  nlinarith [sphereHandleRadius_pos]

/-- A core-supported direct extension fixes every point whose second block is at least the
scaled core radius. -/
theorem directCappedOneHandleExtensionSphere_eq_of_core_radius_le
    {rho : ℝ} (f : OneHandleCoreSupportedRelativeDiff rho)
    {q : Sphere 4}
    (hq : sphereHandleRadius * rho ≤ sphereHandleSecondNorm q) :
    directCappedOneHandleExtensionSphere f.1 q = q := by
  rcases exists_oneHandleSphereMap_or_sphereHandleCapMap q with ⟨x, hx⟩ | ⟨y, hy⟩
  · rw [← hx] at hq ⊢
    rw [directCappedOneHandleExtensionSphere_oneHandle]
    apply congr_arg oneHandleSphereMap
    apply OneHandleCoreSupportedRelativeDiff.apply_eq_of_le_norm f
    have hscaled : sphereHandleRadius * rho ≤
        sphereHandleRadius * ‖x.2.1‖ := by
      simpa only [sphereHandleSecondNorm_oneHandleSphereMap] using hq
    nlinarith [sphereHandleRadius_pos]
  · rw [← hy, directCappedOneHandleExtensionSphere_cap]

/-- In particular, the direct extension is pointwise the identity throughout the open outer
band. -/
theorem directCappedOneHandleExtensionSphere_eq_on_outerBand
    {rho : ℝ} (f : OneHandleCoreSupportedRelativeDiff rho)
    (q : sphereHandleOuterBand rho) :
    directCappedOneHandleExtensionSphere f.1 q.1 = q.1 :=
  directCappedOneHandleExtensionSphere_eq_of_core_radius_le f q.2.le

/-- Locality reduces global smoothness of a core-supported extension to smoothness on the inner
one-handle band.  On the other member of the open cover the map is literally the identity. -/
theorem contMDiff_directCappedOneHandleExtensionSphere_of_innerBand
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (hinner : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere f.1) sphereHandleInnerBand) :
    ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere f.1) := by
  apply contMDiff_of_contMDiffOn_union_of_isOpen hinner
  · exact contMDiff_id.contMDiffOn.congr fun (q : Sphere 4)
      (hq : q ∈ sphereHandleOuterBand rho) ↦ by
      simpa only [id_eq] using
        directCappedOneHandleExtensionSphere_eq_of_core_radius_le f hq.le
  · exact sphereHandleInnerBand_union_outerBand hrho
  · exact sphereHandleInnerBand.2
  · exact (sphereHandleOuterBand rho).2

/-- Restrict the faithful direct extension homomorphism to the core-supported subgroup. -/
def oneHandleCoreExtensionSphereHom (rho : ℝ) :
    OneHandleCoreSupportedRelativeDiff rho →* (Sphere 4 ≃ₜ Sphere 4) :=
  directCappedOneHandleExtensionSphereHom.comp
    (OneHandleCoreSupportedRelativeDiff rho).subtype

/-- Restricting to core-supported diffeomorphisms does not destroy faithfulness. -/
theorem oneHandleCoreExtensionSphereHom_injective (rho : ℝ) :
    Injective (oneHandleCoreExtensionSphereHom rho) :=
  directCappedOneHandleExtensionSphereHom_injective.comp
    (OneHandleCoreSupportedRelativeDiff rho).subtype_injective

/-- The direct extension of the inverse core-supported diffeomorphism is the inverse extended
homeomorphism. -/
@[simp]
theorem directCappedOneHandleExtensionSphere_inv
    {rho : ℝ} (f : OneHandleCoreSupportedRelativeDiff rho) :
    directCappedOneHandleExtensionSphere (f⁻¹).1 =
      (directCappedOneHandleExtensionSphere f.1).symm := by
  exact map_inv (oneHandleCoreExtensionSphereHom rho) f

end SplittingSpheres
