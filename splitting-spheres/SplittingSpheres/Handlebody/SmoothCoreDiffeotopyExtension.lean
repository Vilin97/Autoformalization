/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.SmoothCoreExtension
public import SplittingSpheres.Foundations.RelativeDiffeomorph

/-!
# Jointly smooth extension of core-supported one-handle diffeotopies

A source family records one jointly smooth evaluation map on the compact one-handle, together
with the assertion that every time slice is represented by a core-supported relative
diffeomorphism.  No topology or smooth structure on the diffeomorphism group is used.

For a core radius strictly smaller than one, its direct extensions form a jointly smooth family
on the literal four-sphere.  On the open one-handle region this follows from the explicit product
coordinates and joint smoothness of the source evaluation.  On the complementary outer band all
slices are literally the identity, so the two formulas glue by locality.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SplittingSpheres

/-- A genuine jointly smooth family of core-supported, boundary-relative one-handle
diffeomorphisms.  The slice field records invertibility and support at every time without
requiring a topology on the diffeomorphism group. -/
structure OneHandleCoreDiffeotopy (rho : ℝ)
    (f g : OneHandleCoreSupportedRelativeDiff rho) where
  /-- Joint evaluation in time and the one-handle variable. -/
  toFun : unitInterval × OneHandlePiece → OneHandlePiece
  /-- The evaluation is jointly smooth, including at the endpoints of the interval and at the
  model boundary of the closed ball factor. -/
  contMDiff_toFun :
    ContMDiff ((𝓡∂ 1).prod oneHandlePieceModel) oneHandlePieceModel ∞ toFun
  /-- Every time slice is an honest member of the fixed core-supported subgroup. -/
  slice : ∀ t : unitInterval,
    ∃ φ : OneHandleCoreSupportedRelativeDiff rho,
      ∀ x : OneHandlePiece, toFun (t, x) = φ.1.1 x
  /-- Exact initial endpoint. -/
  zero : ∀ x : OneHandlePiece, toFun (0, x) = f.1.1 x
  /-- Exact final endpoint. -/
  one : ∀ x : OneHandlePiece, toFun (1, x) = g.1.1 x

namespace OneHandleCoreDiffeotopy

variable {rho : ℝ} {f g : OneHandleCoreSupportedRelativeDiff rho}

/-- A representative of a time slice.  Later formulas are proved independent of this choice. -/
noncomputable def chosenSlice (H : OneHandleCoreDiffeotopy rho f g)
    (t : unitInterval) : OneHandleCoreSupportedRelativeDiff rho :=
  Classical.choose (H.slice t)

/-- The chosen slice represents the given joint evaluation exactly. -/
theorem toFun_eq_chosenSlice (H : OneHandleCoreDiffeotopy rho f g)
    (t : unitInterval) (x : OneHandlePiece) :
    H.toFun (t, x) = (H.chosenSlice t).1.1 x :=
  Classical.choose_spec (H.slice t) x

/-- Any two core-supported diffeomorphisms representing the same slice are equal. -/
theorem chosenSlice_eq_of_represents (H : OneHandleCoreDiffeotopy rho f g)
    (t : unitInterval) (φ : OneHandleCoreSupportedRelativeDiff rho)
    (hφ : ∀ x : OneHandlePiece, H.toFun (t, x) = φ.1.1 x) :
    H.chosenSlice t = φ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Diffeomorph.ext
  intro x
  exact (H.toFun_eq_chosenSlice t x).symm.trans (hφ x)

/-- The canonical extension family, defined using an arbitrary chosen representative of each
slice.  Its pointwise action is independent of that choice. -/
def sphereToFun (H : OneHandleCoreDiffeotopy rho f g) (hrho : rho < 1) :
    unitInterval × Sphere 4 → Sphere 4 :=
  fun p ↦ smoothOneHandleCoreExtensionDiffeomorph hrho (H.chosenSlice p.1) p.2

/-- The extended family agrees with the extension of every representative of the same source
slice, so the use of choice in `sphereToFun` has no mathematical content. -/
theorem sphereToFun_eq_extension_of_represents
    (H : OneHandleCoreDiffeotopy rho f g) (hrho : rho < 1)
    (t : unitInterval) (φ : OneHandleCoreSupportedRelativeDiff rho)
    (hφ : ∀ x : OneHandlePiece, H.toFun (t, x) = φ.1.1 x)
    (q : Sphere 4) :
    H.sphereToFun hrho (t, q) =
      smoothOneHandleCoreExtensionDiffeomorph hrho φ q := by
  rw [sphereToFun, H.chosenSlice_eq_of_represents t φ hφ]

/-- On the one-handle face, the extended family is exactly the source evaluation followed by
the direct coordinate map. -/
theorem sphereToFun_oneHandleSphereMap
    (H : OneHandleCoreDiffeotopy rho f g) (hrho : rho < 1)
    (t : unitInterval) (x : OneHandlePiece) :
    H.sphereToFun hrho (t, oneHandleSphereMap x) =
      oneHandleSphereMap (H.toFun (t, x)) := by
  rw [sphereToFun, smoothOneHandleCoreExtensionDiffeomorph_apply,
    directCappedOneHandleExtensionSphere_oneHandle,
    H.toFun_eq_chosenSlice]

/-- Exact inner-coordinate formula for the extended family. -/
theorem sphereToFun_interiorDiffeomorph
    (H : OneHandleCoreDiffeotopy rho f g) (hrho : rho < 1)
    (t : unitInterval) (p : Sphere 1 × SphereHandleOpenUnitBall) :
    H.sphereToFun hrho
        (t, ((sphereHandleInteriorDiffeomorph p : SphereHandleOneRegion) : Sphere 4)) =
      oneHandleSphereMap
        (H.toFun (t, sphereHandleInteriorProductInclusion p)) := by
  rw [sphereHandleInteriorDiffeomorph_apply_coe,
    ← sphereHandleInteriorProductInclusion_apply,
    H.sphereToFun_oneHandleSphereMap]

/-- Every extended slice is literally the identity on the common outer band. -/
theorem sphereToFun_eq_on_outerBand
    (H : OneHandleCoreDiffeotopy rho f g) (hrho : rho < 1)
    (t : unitInterval) (q : sphereHandleOuterBand rho) :
    H.sphereToFun hrho (t, q.1) = q.1 :=
  smoothOneHandleCoreExtensionDiffeomorph_eq_on_outerBand
    hrho (H.chosenSlice t) q

/-- Time crossed with the open one-handle region. -/
def familyInnerRegion : Opens (unitInterval × Sphere 4) :=
  ⟨(univ : Set unitInterval) ×ˢ (sphereHandleOneRegion : Set (Sphere 4)),
    isOpen_univ.prod sphereHandleOneRegion.2⟩

/-- Time crossed with the outer identity band. -/
def familyOuterRegion (rho : ℝ) : Opens (unitInterval × Sphere 4) :=
  ⟨(univ : Set unitInterval) ×ˢ (sphereHandleOuterBand rho : Set (Sphere 4)),
    isOpen_univ.prod (sphereHandleOuterBand rho).2⟩

@[simp]
theorem mem_familyInnerRegion {p : unitInterval × Sphere 4} :
    p ∈ familyInnerRegion ↔ p.2 ∈ sphereHandleOneRegion := by
  simp [familyInnerRegion]

@[simp]
theorem mem_familyOuterRegion {rho : ℝ} {p : unitInterval × Sphere 4} :
    p ∈ familyOuterRegion rho ↔ p.2 ∈ sphereHandleOuterBand rho := by
  simp [familyOuterRegion]

/-- The product inner and outer regions cover the whole time-space cylinder. -/
theorem familyInnerRegion_union_outerRegion (hrho : rho < 1) :
    (familyInnerRegion : Set (unitInterval × Sphere 4)) ∪ familyOuterRegion rho = univ := by
  change ((univ : Set unitInterval) ×ˢ (sphereHandleOneRegion : Set (Sphere 4))) ∪
    ((univ : Set unitInterval) ×ˢ (sphereHandleOuterBand rho : Set (Sphere 4))) = univ
  rw [← Set.prod_union, ← sphereHandleInnerBand_eq_oneRegion,
    sphereHandleInnerBand_union_outerBand hrho, Set.univ_prod_univ]

/-- Convert the product inner open subtype to explicit time and one-handle product coordinates. -/
def innerSourceCoordinates (p : familyInnerRegion) : unitInterval × OneHandlePiece :=
  (p.1.1,
    sphereHandleInteriorProductInclusion
      (sphereHandleInteriorDiffeomorph.symm ⟨p.1.2, p.2.2⟩))

/-- The explicit inner source-coordinate map is smooth. -/
theorem contMDiff_innerSourceCoordinates :
    ContMDiff ((𝓡∂ 1).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      ((𝓡∂ 1).prod oneHandlePieceModel) ∞ innerSourceCoordinates := by
  have ht : ContMDiff
      ((𝓡∂ 1).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (𝓡∂ 1) ∞ (fun p : familyInnerRegion ↦ p.1.1) :=
    contMDiff_fst.comp contMDiff_subtype_val
  have hq : ContMDiff
      ((𝓡∂ 1).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun p : familyInnerRegion ↦ (⟨p.1.2, p.2.2⟩ : SphereHandleOneRegion)) := by
    apply (ContMDiff.subtypeVal_comp_iff sphereHandleOneRegion _).mp
    exact contMDiff_snd.comp contMDiff_subtype_val
  exact ht.prodMk
    (contMDiff_sphereHandleInteriorProductInclusion.comp
      (sphereHandleInteriorDiffeomorph.symm.contMDiff.comp hq))

/-- Joint smoothness of the extended evaluation after restriction to the inner product-open
subtype, proved from the source family's joint smoothness. -/
theorem contMDiff_sphereToFun_restrict_inner
    (H : OneHandleCoreDiffeotopy rho f g) (hrho : rho < 1) :
    ContMDiff
      ((𝓡∂ 1).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun p : familyInnerRegion ↦ H.sphereToFun hrho p.1) := by
  have hsmooth : ContMDiff
      ((𝓡∂ 1).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun p : familyInnerRegion ↦
        oneHandleSphereMap (H.toFun (innerSourceCoordinates p))) :=
    contMDiff_oneHandleSphereMap.comp
      (H.contMDiff_toFun.comp contMDiff_innerSourceCoordinates)
  apply hsmooth.congr
  intro p
  let q : SphereHandleOneRegion := ⟨p.1.2, p.2.2⟩
  let a := sphereHandleInteriorDiffeomorph.symm q
  have hq : p.1.2 = oneHandleSphereMap
      (sphereHandleInteriorProductInclusion a) := by
    symm
    rw [sphereHandleInteriorProductInclusion_apply,
      ← sphereHandleInteriorDiffeomorph_apply_coe]
    exact congr_arg Subtype.val (sphereHandleInteriorDiffeomorph.apply_symm_apply q)
  change H.sphereToFun hrho (p.1.1, p.1.2) =
    oneHandleSphereMap
      (H.toFun (p.1.1, sphereHandleInteriorProductInclusion a))
  rw [hq, H.sphereToFun_oneHandleSphereMap]

/-- Joint smoothness after restriction to the outer product-open subtype. -/
theorem contMDiff_sphereToFun_restrict_outer
    (H : OneHandleCoreDiffeotopy rho f g) (hrho : rho < 1) :
    ContMDiff
      ((𝓡∂ 1).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun p : familyOuterRegion rho ↦ H.sphereToFun hrho p.1) := by
  have hid : ContMDiff
      ((𝓡∂ 1).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun p : familyOuterRegion rho ↦ p.1.2) :=
    contMDiff_snd.comp contMDiff_subtype_val
  apply hid.congr
  intro p
  exact H.sphereToFun_eq_on_outerBand hrho p.1.1 ⟨p.1.2, p.2.2⟩

/-- The canonical sphere extension is jointly smooth in time and the sphere variable. -/
theorem contMDiff_sphereToFun
    (H : OneHandleCoreDiffeotopy rho f g) (hrho : rho < 1) :
    ContMDiff
      ((𝓡∂ 1).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (H.sphereToFun hrho) := by
  apply contMDiff_of_contMDiffOn_union_of_isOpen
  · intro p hp
    have h := (H.contMDiff_sphereToFun_restrict_inner hrho).contMDiffAt
      (x := (⟨p, hp⟩ : familyInnerRegion))
    exact (contMDiffAt_subtype_iff.mp h).contMDiffWithinAt
  · intro p hp
    have h := (H.contMDiff_sphereToFun_restrict_outer hrho).contMDiffAt
      (x := (⟨p, hp⟩ : familyOuterRegion rho))
    exact (contMDiffAt_subtype_iff.mp h).contMDiffWithinAt
  · exact familyInnerRegion_union_outerRegion hrho
  · exact familyInnerRegion.2
  · exact (familyOuterRegion rho).2

/-- Extend a jointly smooth core-supported one-handle family to a genuine relative
diffeotopy of the four-sphere, relative to the empty set. -/
def extension (H : OneHandleCoreDiffeotopy rho f g) (hrho : rho < 1) :
    RelativeDiffeotopy (∅ : Set (Sphere 4))
      (smoothOneHandleCoreExtensionRelativeHom hrho f)
      (smoothOneHandleCoreExtensionRelativeHom hrho g) where
  toFun := H.sphereToFun hrho
  contMDiff_toFun := H.contMDiff_sphereToFun hrho
  slice t :=
    ⟨smoothOneHandleCoreExtensionRelativeHom hrho (H.chosenSlice t), fun _ ↦ rfl⟩
  zero q := by
    exact H.sphereToFun_eq_extension_of_represents hrho 0 f H.zero q
  one q := by
    exact H.sphereToFun_eq_extension_of_represents hrho 1 g H.one q

/-- The extended endpoint diffeomorphisms have the same relative smooth mapping class. -/
theorem extension_mappingClass_eq
    (H : OneHandleCoreDiffeotopy rho f g) (hrho : rho < 1) :
    relativeMappingClassMk
        (IM := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (∅ : Set (Sphere 4)) (smoothOneHandleCoreExtensionRelativeHom hrho f) =
      relativeMappingClassMk
        (IM := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (∅ : Set (Sphere 4)) (smoothOneHandleCoreExtensionRelativeHom hrho g) :=
  (H.extension hrho).mappingClass_eq

/-- The constant source family is a core-supported one-handle diffeotopy. -/
protected def refl (rho : ℝ) (f : OneHandleCoreSupportedRelativeDiff rho) :
    OneHandleCoreDiffeotopy rho f f where
  toFun p := f.1.1 p.2
  contMDiff_toFun := f.1.1.contMDiff.comp contMDiff_snd
  slice _ := ⟨f, fun _ ↦ rfl⟩
  zero _ := rfl
  one _ := rfl

end OneHandleCoreDiffeotopy

end SplittingSpheres
