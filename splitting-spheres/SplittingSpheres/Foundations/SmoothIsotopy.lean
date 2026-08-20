/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.Separation
public import SplittingSpheres.Foundations.SmoothEmbedding

/-!
# Elementary operations on smooth sphere isotopies

This file proves the operations on the frozen range-endpoint isotopy notion which do not require
an isotopy-extension theorem.  Reversing time gives symmetry, and an ambient diffeomorphism
transports both an isotopy and the splitting property.  The proofs retain joint smoothness on the
manifold-with-boundary interval.
-/

@[expose] public section

open Function Metric Set
open scoped ContDiff Manifold unitInterval

noncomputable section

namespace unitInterval

/-- Central reflection of the unit interval is smooth as a map of manifolds with boundary. -/
theorem contMDiff_symm : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ symm := by
  rw [contMDiff_iff_comp_subtypeVal_Icc]
  refine ⟨continuous_symm, ?_⟩
  change ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t : I ↦ 1 - (t : ℝ))
  exact contMDiff_const.sub contMDiff_subtypeVal_Icc

end unitInterval

namespace SplittingSpheres

/-- Retag the endpoints of an isotopy by bundled embeddings with the same ranges. -/
def SmoothSphereIsotopy.congrRange
    {S₀ S₁ T₀ T₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁)
    (h₀ : range S₀ = range T₀) (h₁ : range S₁ = range T₁) :
    SmoothSphereIsotopy T₀ T₁ where
  toFun := H.toFun
  contMDiff_toFun := H.contMDiff_toFun
  isSmoothEmbedding_slice := H.isSmoothEmbedding_slice
  range_zero := H.range_zero.trans h₀
  range_one := H.range_one.trans h₁

/-- The complement-isotopy relation depends only on the endpoint ranges. -/
theorem SmoothlyIsotopicInComplement.congrRange
    {S₀ S₁ T₀ T₁ : SmoothSphereEmbedding 3 4}
    (h₀ : range S₀ = range T₀) (h₁ : range S₁ = range T₁)
    (h : SmoothlyIsotopicInComplement S₀ S₁) :
    SmoothlyIsotopicInComplement T₀ T₁ := by
  obtain ⟨H, hH⟩ := h
  exact ⟨H.congrRange h₀ h₁, hH⟩

/-- Reverse the time parameter of a smooth sphere isotopy. -/
def SmoothSphereIsotopy.symm {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) : SmoothSphereIsotopy S₁ S₀ where
  toFun := fun p ↦ H.toFun (unitInterval.symm p.1, p.2)
  contMDiff_toFun := H.contMDiff_toFun.comp
    ((unitInterval.contMDiff_symm.comp contMDiff_fst).prodMk contMDiff_snd)
  isSmoothEmbedding_slice := fun t ↦ H.isSmoothEmbedding_slice (unitInterval.symm t)
  range_zero := by simpa using H.range_one
  range_one := by simpa using H.range_zero

/-- Smooth isotopy in the unlink complement is symmetric. -/
theorem smoothlyIsotopicInComplement_symm {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (h : SmoothlyIsotopicInComplement S₀ S₁) :
    SmoothlyIsotopicInComplement S₁ S₀ := by
  obtain ⟨H, hH⟩ := h
  refine ⟨H.symm, ?_⟩
  rintro ⟨t, x⟩
  exact hH (unitInterval.symm t, x)

/-- Postcompose every slice of an isotopy by an ambient diffeomorphism. -/
def SmoothSphereIsotopy.postcompDiffeomorph
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁)
    (e : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4) :
    SmoothSphereIsotopy
      (TauCeti.SmoothEmbedding.postcompDiffeomorph S₀ e)
      (TauCeti.SmoothEmbedding.postcompDiffeomorph S₁ e) where
  toFun := e ∘ H.toFun
  contMDiff_toFun := e.contMDiff.comp H.contMDiff_toFun
  isSmoothEmbedding_slice := fun t ↦
    (H.isSmoothEmbedding_slice t).postcomp_diffeomorph e
  range_zero := by
    change Set.range (e ∘ fun x ↦ H.toFun (0, x)) = _
    rw [Set.range_comp, H.range_zero,
      ← TauCeti.SmoothEmbedding.range_postcompDiffeomorph]
  range_one := by
    change Set.range (e ∘ fun x ↦ H.toFun (1, x)) = _
    rw [Set.range_comp, H.range_one,
      ← TauCeti.SmoothEmbedding.range_postcompDiffeomorph]

/-- An ambient diffeomorphism preserving the unlink carrier transports complement isotopies. -/
theorem SmoothlyIsotopicInComplement.postcompDiffeomorph
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (e : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4)
    (he : e ⁻¹' standardUnlinkCarrier = standardUnlinkCarrier)
    (h : SmoothlyIsotopicInComplement S₀ S₁) :
    SmoothlyIsotopicInComplement
      (TauCeti.SmoothEmbedding.postcompDiffeomorph S₀ e)
      (TauCeti.SmoothEmbedding.postcompDiffeomorph S₁ e) := by
  obtain ⟨H, hH⟩ := h
  refine ⟨H.postcompDiffeomorph e, ?_⟩
  intro p hp
  apply hH p
  rw [← he]
  exact hp

/-- An ambient diffeomorphism preserving each labelled link component carries splitting spheres
to splitting spheres. -/
theorem IsSplittingSphere.postcompDiffeomorph
    {S : SmoothSphereEmbedding 3 4}
    (e : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4)
    (h₀ : e '' standardUnlinkComponent 0 = standardUnlinkComponent 0)
    (h₁ : e '' standardUnlinkComponent 1 = standardUnlinkComponent 1)
    (hS : IsSplittingSphere S) :
    IsSplittingSphere (TauCeti.SmoothEmbedding.postcompDiffeomorph S e) := by
  rw [IsSplittingSphere, TauCeti.SmoothEmbedding.range_postcompDiffeomorph]
  exact hS.image_homeomorph_of_fixed e.toHomeomorph h₀ h₁

/-- A pairwise non-isotopic family of splitting spheres has pairwise distinct embedded images.
This rules out obtaining apparent infinitude merely by changing parametrizations. -/
theorem injective_range_of_pairwise_not_smoothlyIsotopicInComplement
    (S : ℕ → SmoothSphereEmbedding 3 4)
    (hsplit : ∀ k, IsSplittingSphere (S k))
    (hpair : Pairwise fun i j ↦ ¬SmoothlyIsotopicInComplement (S i) (S j)) :
    Function.Injective (fun k ↦ range (S k)) := by
  intro i j hij
  by_contra hne
  apply hpair hne
  exact SmoothlyIsotopicInComplement.congrRange rfl hij
    (smoothlyIsotopicInComplement_refl (hsplit i))

end SplittingSpheres
