/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothIsotopy
public import TauCeti.Geometry.Diffeomorphism.Group

/-!
# Abstract assembly of the inverse-image splitting-sphere family

This file formalizes the short final deduction independently of the barbell construction.  The
family is made from inverse images `βᵢ⁻¹(Σ)`.  Consequently, postcomposing a hypothetical isotopy
between its `i`th and `j`th members by `βᵢ` gives an isotopy from `Σ` to
`(βᵢ * βⱼ⁻¹)(Σ)`, in exactly that order.

The theorem here is deliberately conditional on the geometric detector.  It is an assembly lemma,
not a replacement for the handlebody, cover, Cerf, or Budney--Gabai arguments which must establish
that detector for the concrete barbell maps.
-/

@[expose] public section

open Function Set
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- The inverse image of an embedded sphere under an ambient diffeomorphism, represented by
postcomposition with the inverse. -/
def inverseImageSphere (S : SmoothSphereEmbedding 3 4)
    (e : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4) : SmoothSphereEmbedding 3 4 :=
  TauCeti.SmoothEmbedding.postcompDiffeomorph S e⁻¹

/-- The sphere obtained by the composite `e * f⁻¹`, with the diffeomorphism-group convention
that multiplication is function composition. -/
def relativeCompositeSphere (S : SmoothSphereEmbedding 3 4)
    (e f : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4) : SmoothSphereEmbedding 3 4 :=
  TauCeti.SmoothEmbedding.postcompDiffeomorph S (e * f⁻¹)

/-- Applying `e` to `e⁻¹(S)` recovers the original embedded image. -/
theorem range_inverseImageSphere_postcomp
    (S : SmoothSphereEmbedding 3 4)
    (e : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4) :
    range (TauCeti.SmoothEmbedding.postcompDiffeomorph (inverseImageSphere S e) e) =
      range S := by
  rw [TauCeti.SmoothEmbedding.range_postcompDiffeomorph,
    inverseImageSphere, TauCeti.SmoothEmbedding.range_postcompDiffeomorph]
  change e '' (e.symm '' range S) = range S
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hy
    exact ⟨e.symm y, ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩

/-- Applying `e` to `f⁻¹(S)` has the range of `(e * f⁻¹)(S)`.  This is the formal composition-order
calculation behind the inverse-image convention. -/
theorem range_inverseImageSphere_postcomp_eq_relativeComposite
    (S : SmoothSphereEmbedding 3 4)
    (e f : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4) :
    range (TauCeti.SmoothEmbedding.postcompDiffeomorph (inverseImageSphere S f) e) =
      range (relativeCompositeSphere S e f) := by
  rw [TauCeti.SmoothEmbedding.range_postcompDiffeomorph,
    inverseImageSphere, TauCeti.SmoothEmbedding.range_postcompDiffeomorph,
    relativeCompositeSphere, TauCeti.SmoothEmbedding.range_postcompDiffeomorph,
    image_image]
  rfl

/-- If a bijection preserves a set by image, it also preserves it by preimage. -/
theorem preimage_eq_of_image_eq (e : Sphere 4 ≃ Sphere 4) {A : Set (Sphere 4)}
    (hA : e '' A = A) : e ⁻¹' A = A := by
  exact (Set.preimage_eq_iff_eq_image e.bijective).2 hA.symm

/-- The inverse of a bijection preserving a set also preserves that set by image. -/
theorem image_symm_eq_of_image_eq (e : Sphere 4 ≃ Sphere 4) {A : Set (Sphere 4)}
    (hA : e '' A = A) : e.symm '' A = A := by
  calc
    e.symm '' A = e ⁻¹' A := by simpa using e.symm.image_eq_preimage_symm A
    _ = e ⁻¹' (e '' A) := congrArg (e ⁻¹' ·) hA.symm
    _ = A := e.preimage_image A

/-- A link-preserving ambient diffeomorphism carries a splitting sphere to its inverse image. -/
theorem IsSplittingSphere.inverseImageSphere
    {S : SmoothSphereEmbedding 3 4}
    (e : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4)
    (h₀ : e '' standardUnlinkComponent 0 = standardUnlinkComponent 0)
    (h₁ : e '' standardUnlinkComponent 1 = standardUnlinkComponent 1)
    (hS : IsSplittingSphere S) : IsSplittingSphere (inverseImageSphere S e) := by
  apply hS.postcompDiffeomorph e⁻¹
  · change e.symm '' standardUnlinkComponent 0 = standardUnlinkComponent 0
    exact image_symm_eq_of_image_eq e.toEquiv h₀
  · change e.symm '' standardUnlinkComponent 1 = standardUnlinkComponent 1
    exact image_symm_eq_of_image_eq e.toEquiv h₁

/-- Abstract final-family theorem.  Once a concrete link-preserving family `β` is shown by the
cyclic-cover detector to move `Σ` nontrivially under every relative composite
`βᵢ * βⱼ⁻¹`, its inverse images form the family required by the frozen statement. -/
theorem mainTheorem_of_ambientFamily
    (Sbase : SmoothSphereEmbedding 3 4) (hSbase : IsSplittingSphere Sbase)
    (β : ℕ → Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4)
    (hfix₀ : ∀ i, β i '' standardUnlinkComponent 0 = standardUnlinkComponent 0)
    (hfix₁ : ∀ i, β i '' standardUnlinkComponent 1 = standardUnlinkComponent 1)
    (hdetect : Pairwise fun i j ↦
      ¬SmoothlyIsotopicInComplement Sbase (relativeCompositeSphere Sbase (β i) (β j))) :
    MainTheorem := by
  refine ⟨fun i ↦ inverseImageSphere Sbase (β i), ?_, ?_⟩
  · intro i
    exact hSbase.inverseImageSphere (β i) (hfix₀ i) (hfix₁ i)
  · intro i j hij hfamily
    apply hdetect hij
    have hcarrierImage : β i '' standardUnlinkCarrier = standardUnlinkCarrier :=
      image_standardUnlinkCarrier_of_components_fixed (β i).toHomeomorph (hfix₀ i) (hfix₁ i)
    have hcarrierPreimage : β i ⁻¹' standardUnlinkCarrier = standardUnlinkCarrier :=
      preimage_eq_of_image_eq (β i).toEquiv hcarrierImage
    have htransport := hfamily.postcompDiffeomorph (β i) hcarrierPreimage
    exact htransport.congrRange
      (range_inverseImageSphere_postcomp Sbase (β i))
      (range_inverseImageSphere_postcomp_eq_relativeComposite Sbase (β i) (β j))

end SplittingSpheres
