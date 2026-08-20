/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothCover
public import SplittingSpheres.Geometry.UnlinkTubes

/-!
# The smooth open complement of the coordinate unlink

The frozen isotopy relation is stated in the ambient four-sphere together with pointwise
avoidance of the coordinate unlink.  This file packages the strict complement as an open
submanifold and shows that every such isotopy factors jointly smoothly through it.  This is the
base manifold to which smooth covering-space lifting applies.

No compactification or manifold-with-boundary structure on a tubular exterior is asserted here.
-/

@[expose] public section

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Manifold unitInterval

namespace SplittingSpheres

/-- The complement of the frozen coordinate unlink as an open subset of the four-sphere. -/
def standardUnlinkComplementOpens : Opens (Sphere 4) :=
  ⟨standardUnlinkCarrierᶜ, isCompact_standardUnlinkCarrier.isClosed.isOpen_compl⟩

/-- The strict coordinate-unlink complement, carrying the inherited smooth open-submanifold
structure. -/
abbrev StandardUnlinkComplement : Type := standardUnlinkComplementOpens

@[simp]
theorem mem_standardUnlinkComplementOpens (x : Sphere 4) :
    x ∈ standardUnlinkComplementOpens ↔ x ∉ standardUnlinkCarrier :=
  Iff.rfl

/-- Inclusion of the strict complement into the ambient sphere as a bundled smooth embedding. -/
def standardUnlinkComplementInclusion :
    TauCeti.SmoothEmbedding (𝓡 4) (𝓡 4) ∞ StandardUnlinkComplement (Sphere 4) :=
  TauCeti.SmoothEmbedding.ofOpens standardUnlinkComplementOpens

@[simp]
theorem standardUnlinkComplementInclusion_apply (x : StandardUnlinkComplement) :
    standardUnlinkComplementInclusion x = x.1 :=
  TauCeti.SmoothEmbedding.ofOpens_apply standardUnlinkComplementOpens x

@[simp]
theorem standardUnlinkComplementInclusion_coe :
    ⇑standardUnlinkComplementInclusion =
      (Subtype.val : StandardUnlinkComplement → Sphere 4) := by
  funext x
  exact standardUnlinkComplementInclusion_apply x

/-- A point in any positive-radius coordinate exterior canonically determines a point of the
strict link complement. -/
def coordinateUnlinkExteriorToComplement {r : ℝ} (hr : 0 < r) :
    ↑(coordinateUnlinkExterior r) → StandardUnlinkComplement :=
  fun x ↦ ⟨x.1, fun hx ↦ x.2 (standardUnlinkCarrier_subset_openTubes hr hx)⟩

@[simp]
theorem coordinateUnlinkExteriorToComplement_coe {r : ℝ} (hr : 0 < r)
    (x : ↑(coordinateUnlinkExterior r)) :
    (coordinateUnlinkExteriorToComplement hr x : Sphere 4) = x.1 :=
  rfl

theorem continuous_coordinateUnlinkExteriorToComplement {r : ℝ} (hr : 0 < r) :
    Continuous (coordinateUnlinkExteriorToComplement hr) :=
  continuous_subtype_val.subtype_mk _

/-- A link-avoiding smooth sphere isotopy, regarded as a jointly smooth map into the strict
coordinate-unlink complement. -/
def SmoothSphereIsotopy.toUnlinkComplement
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁)
    (havoid : ∀ p : I × Sphere 3, H.toFun p ∉ standardUnlinkCarrier) :
    ContMDiffMap ((𝓡∂ 1).prod (𝓡 3)) (𝓡 4)
      (I × Sphere 3) StandardUnlinkComplement ∞ :=
  ⟨fun p ↦ ⟨H.toFun p, havoid p⟩, by
    rw [← ContMDiff.subtypeVal_comp_iff standardUnlinkComplementOpens]
    exact H.contMDiff_toFun⟩

@[simp]
theorem SmoothSphereIsotopy.toUnlinkComplement_apply
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁)
    (havoid : ∀ p : I × Sphere 3, H.toFun p ∉ standardUnlinkCarrier)
    (p : I × Sphere 3) :
    (H.toUnlinkComplement havoid p : Sphere 4) = H.toFun p :=
  rfl

/-- Every witness to the frozen complement-isotopy relation has a jointly smooth realization in
the smooth strict complement. -/
theorem SmoothlyIsotopicInComplement.exists_contMDiffMap_toUnlinkComplement
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (h : SmoothlyIsotopicInComplement S₀ S₁) :
    ∃ H : SmoothSphereIsotopy S₀ S₁,
      ∃ F : ContMDiffMap ((𝓡∂ 1).prod (𝓡 3)) (𝓡 4)
        (I × Sphere 3) StandardUnlinkComplement ∞,
        ∀ p, (F p : Sphere 4) = H.toFun p := by
  obtain ⟨H, havoid⟩ := h
  exact ⟨H, H.toUnlinkComplement havoid, fun _ ↦ rfl⟩

end SplittingSpheres
