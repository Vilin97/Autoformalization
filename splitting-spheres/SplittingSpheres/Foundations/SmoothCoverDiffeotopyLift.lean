/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothCoverIsotopyLift

/-!
# Diffeomorphism slices of a jointly smooth cover lift

A jointly smooth family of base diffeomorphisms has a jointly smooth lift once the lifting
criterion is imposed on the whole product.  To know that each lifted slice is itself a
diffeomorphism, one must additionally know that both the base slice and its inverse preserve the
subgroup recovered by the cover.  Those two all-time assumptions are explicit in this file.

The final section bundles the lifted family as a `RelativeDiffeotopy`.  It either takes an honest
hypothesis saying that every lifted slice fixes a chosen total-space subset, or specializes to the
singleton containing the selected lift point, whose fixedness was proved by path-lift uniqueness.
-/

@[expose] public section

open Function
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

universe uE uX uHE uHX

variable {EE EX : Type*}
  [NormedAddCommGroup EE] [NormedSpace ℝ EE]
  [NormedAddCommGroup EX] [NormedSpace ℝ EX]
variable {HE : Type uHE} [TopologicalSpace HE]
  {HX : Type uHX} [TopologicalSpace HX]
variable {IE : ModelWithCorners ℝ EE HE} {IX : ModelWithCorners ℝ EX HX}
variable {E : Type uE} [TopologicalSpace E] [ChartedSpace HE E]
  {X : Type uX} [TopologicalSpace X] [ChartedSpace HX X]
variable {n : ℕ∞ω} {p : E → X}

namespace SmoothCover

/-- The evaluation map of a family of diffeomorphisms. -/
def diffeomorphismFamilyEval
    (φ : unitInterval → (X ≃ₘ^n⟮IX, IX⟯ X)) : unitInterval × X → X :=
  fun q ↦ φ q.1 q.2

/-- Forward recovered-subgroup preservation for every slice of a based diffeomorphism family. -/
def DiffeomorphismFamilyPreservesRecoveredSubgroup (hp : SmoothCover IE IX n p)
    (φ : unitInterval → (X ≃ₘ^n⟮IX, IX⟯ X)) (e₀ : E)
    (hfix : ∀ t, φ t (p e₀) = p e₀) : Prop :=
  ∀ t, hp.PreservesRecoveredSubgroup (φ t) (φ t).continuous e₀ (hfix t)

/-- Inverse recovered-subgroup preservation for every slice of a based diffeomorphism family. -/
def DiffeomorphismFamilyInversePreservesRecoveredSubgroup
    (hp : SmoothCover IE IX n p)
    (φ : unitInterval → (X ≃ₘ^n⟮IX, IX⟯ X)) (e₀ : E)
    (hfix : ∀ t, φ t (p e₀) = p e₀) : Prop :=
  ∀ t, hp.PreservesRecoveredSubgroup (φ t).symm (φ t).symm.continuous e₀
    (fixedPoint_symm_diffeomorph (φ t) (hfix t))

/-- The canonical diffeomorphism carried by the time-`t` slice of a lifted family.  Its inverse
is the canonical based lift of the inverse base diffeomorphism. -/
noncomputable def basedFamilyLiftDiffeomorphSlice (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (φ : unitInterval → (X ≃ₘ^n⟮IX, IX⟯ X))
    (e₀ : E) (hfix : ∀ t, φ t (p e₀) = p e₀)
    (hpres : hp.DiffeomorphismFamilyPreservesRecoveredSubgroup φ e₀ hfix)
    (hpresInv : hp.DiffeomorphismFamilyInversePreservesRecoveredSubgroup φ e₀ hfix)
    (t : unitInterval) : E ≃ₘ^n⟮IE, IE⟯ E :=
  hp.basedLiftDiffeomorph (φ t) e₀ (hfix t)
    (fixedPoint_symm_diffeomorph (φ t) (hfix t)) (hpres t) (hpresInv t)

/-- The bundled lifted slice is definitionally the existing canonical lifted diffeomorphism. -/
theorem basedFamilyLiftDiffeomorphSlice_eq_basedLiftDiffeomorph
    (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (φ : unitInterval → (X ≃ₘ^n⟮IX, IX⟯ X))
    (e₀ : E) (hfix : ∀ t, φ t (p e₀) = p e₀)
    (hpres : hp.DiffeomorphismFamilyPreservesRecoveredSubgroup φ e₀ hfix)
    (hpresInv : hp.DiffeomorphismFamilyInversePreservesRecoveredSubgroup φ e₀ hfix)
    (t : unitInterval) :
    hp.basedFamilyLiftDiffeomorphSlice φ e₀ hfix hpres hpresInv t =
      hp.basedLiftDiffeomorph (φ t) e₀ (hfix t)
        (fixedPoint_symm_diffeomorph (φ t) (hfix t)) (hpres t) (hpresInv t) :=
  rfl

/-- The underlying map of the bundled diffeomorphism slice is exactly the corresponding slice of
the jointly smooth product lift. -/
theorem basedFamilyLiftDiffeomorphSlice_apply (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (φ : unitInterval → (X ≃ₘ^n⟮IX, IX⟯ X))
    (hφ : ContMDiff ((𝓡∂ 1).prod IX) IX n (diffeomorphismFamilyEval φ))
    (e₀ : E) (hfix : ∀ t, φ t (p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion (diffeomorphismFamilyEval φ) hφ e₀ (hfix 0).symm)
    (hpres : hp.DiffeomorphismFamilyPreservesRecoveredSubgroup φ e₀ hfix)
    (hpresInv : hp.DiffeomorphismFamilyInversePreservesRecoveredSubgroup φ e₀ hfix)
    (t : unitInterval) (z : E) :
    hp.basedFamilyLiftDiffeomorphSlice φ e₀ hfix hpres hpresInv t z =
      hp.basedFamilyLift (diffeomorphismFamilyEval φ) hφ e₀ hfix hle (t, z) := by
  rw [basedFamilyLiftDiffeomorphSlice_eq_basedLiftDiffeomorph,
    hp.basedLiftDiffeomorph_apply]
  have hslice :
      (fun w ↦ hp.basedFamilyLift (diffeomorphismFamilyEval φ) hφ e₀ hfix hle (t, w)) =
        hp.basedLift (φ t) (φ t).contMDiff e₀ (hfix t) (hpres t) := by
    apply hp.eq_basedLift (φ t) (φ t).contMDiff e₀ (hfix t) (hpres t)
    · exact hp.basedFamilyLift_slice_contMDiff
        (diffeomorphismFamilyEval φ) hφ e₀ hfix hle t
    · exact hp.basedFamilyLift_basepoint (diffeomorphismFamilyEval φ) hφ e₀ hfix hle t
    · funext w
      exact hp.proj_basedFamilyLift (diffeomorphismFamilyEval φ) hφ e₀ hfix hle t w
  exact (congrFun hslice z).symm

/-- Bundle a lifted diffeomorphism slice as relative to a set which the joint lift fixes
pointwise.  The fixed-set hypothesis is deliberately about the actual joint lift. -/
noncomputable def basedFamilyLiftRelativeSlice (hp : SmoothCover IE IX ∞ p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (φ : unitInterval → (X ≃ₘ^∞⟮IX, IX⟯ X))
    (hφ : ContMDiff ((𝓡∂ 1).prod IX) IX ∞ (diffeomorphismFamilyEval φ))
    (e₀ : E) (hfix : ∀ t, φ t (p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion (diffeomorphismFamilyEval φ) hφ e₀ (hfix 0).symm)
    (hpres : hp.DiffeomorphismFamilyPreservesRecoveredSubgroup φ e₀ hfix)
    (hpresInv : hp.DiffeomorphismFamilyInversePreservesRecoveredSubgroup φ e₀ hfix)
    (r : Set E)
    (hrel : ∀ (t : unitInterval) (z : E), z ∈ r →
      hp.basedFamilyLift (diffeomorphismFamilyEval φ) hφ e₀ hfix hle (t, z) = z)
    (t : unitInterval) : TauCeti.RelativeDiff (I := IE) E ∞ r := by
  refine ⟨hp.basedFamilyLiftDiffeomorphSlice φ e₀ hfix hpres hpresInv t, ?_⟩
  apply TauCeti.Diffeomorph.mem_fixingSubgroup_of_forall
  intro z hz
  rw [hp.basedFamilyLiftDiffeomorphSlice_apply φ hφ e₀ hfix hle hpres hpresInv]
  exact hrel t z hz

/-- The underlying map of a relative lifted slice is the corresponding slice of the joint lift. -/
theorem basedFamilyLiftRelativeSlice_apply (hp : SmoothCover IE IX ∞ p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (φ : unitInterval → (X ≃ₘ^∞⟮IX, IX⟯ X))
    (hφ : ContMDiff ((𝓡∂ 1).prod IX) IX ∞ (diffeomorphismFamilyEval φ))
    (e₀ : E) (hfix : ∀ t, φ t (p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion (diffeomorphismFamilyEval φ) hφ e₀ (hfix 0).symm)
    (hpres : hp.DiffeomorphismFamilyPreservesRecoveredSubgroup φ e₀ hfix)
    (hpresInv : hp.DiffeomorphismFamilyInversePreservesRecoveredSubgroup φ e₀ hfix)
    (r : Set E)
    (hrel : ∀ (t : unitInterval) (z : E), z ∈ r →
      hp.basedFamilyLift (diffeomorphismFamilyEval φ) hφ e₀ hfix hle (t, z) = z)
    (t : unitInterval) (z : E) :
    (hp.basedFamilyLiftRelativeSlice φ hφ e₀ hfix hle hpres hpresInv r hrel t).1 z =
      hp.basedFamilyLift (diffeomorphismFamilyEval φ) hφ e₀ hfix hle (t, z) :=
  hp.basedFamilyLiftDiffeomorphSlice_apply φ hφ e₀ hfix hle hpres hpresInv t z

/-- The relative lifted slice forgets exactly to the canonical lifted diffeomorphism. -/
theorem basedFamilyLiftRelativeSlice_toDiffeomorph (hp : SmoothCover IE IX ∞ p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (φ : unitInterval → (X ≃ₘ^∞⟮IX, IX⟯ X))
    (hφ : ContMDiff ((𝓡∂ 1).prod IX) IX ∞ (diffeomorphismFamilyEval φ))
    (e₀ : E) (hfix : ∀ t, φ t (p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion (diffeomorphismFamilyEval φ) hφ e₀ (hfix 0).symm)
    (hpres : hp.DiffeomorphismFamilyPreservesRecoveredSubgroup φ e₀ hfix)
    (hpresInv : hp.DiffeomorphismFamilyInversePreservesRecoveredSubgroup φ e₀ hfix)
    (r : Set E)
    (hrel : ∀ (t : unitInterval) (z : E), z ∈ r →
      hp.basedFamilyLift (diffeomorphismFamilyEval φ) hφ e₀ hfix hle (t, z) = z)
    (t : unitInterval) :
    (hp.basedFamilyLiftRelativeSlice φ hφ e₀ hfix hle hpres hpresInv r hrel t).1 =
      hp.basedFamilyLiftDiffeomorphSlice φ e₀ hfix hpres hpresInv t :=
  rfl

/-- Direct canonical-lift law for every relative slice, including both endpoints. -/
theorem basedFamilyLiftRelativeSlice_toBasedLiftDiffeomorph
    (hp : SmoothCover IE IX ∞ p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (φ : unitInterval → (X ≃ₘ^∞⟮IX, IX⟯ X))
    (hφ : ContMDiff ((𝓡∂ 1).prod IX) IX ∞ (diffeomorphismFamilyEval φ))
    (e₀ : E) (hfix : ∀ t, φ t (p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion (diffeomorphismFamilyEval φ) hφ e₀ (hfix 0).symm)
    (hpres : hp.DiffeomorphismFamilyPreservesRecoveredSubgroup φ e₀ hfix)
    (hpresInv : hp.DiffeomorphismFamilyInversePreservesRecoveredSubgroup φ e₀ hfix)
    (r : Set E)
    (hrel : ∀ (t : unitInterval) (z : E), z ∈ r →
      hp.basedFamilyLift (diffeomorphismFamilyEval φ) hφ e₀ hfix hle (t, z) = z)
    (t : unitInterval) :
    (hp.basedFamilyLiftRelativeSlice φ hφ e₀ hfix hle hpres hpresInv r hrel t).1 =
      hp.basedLiftDiffeomorph (φ t) e₀ (hfix t)
        (fixedPoint_symm_diffeomorph (φ t) (hfix t)) (hpres t) (hpresInv t) :=
  rfl

/-- Under an explicit all-time fixed-set hypothesis, the canonical joint lift is a genuine
relative diffeotopy between its canonical endpoint slices. -/
noncomputable def basedFamilyLiftRelativeDiffeotopy (hp : SmoothCover IE IX ∞ p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (φ : unitInterval → (X ≃ₘ^∞⟮IX, IX⟯ X))
    (hφ : ContMDiff ((𝓡∂ 1).prod IX) IX ∞ (diffeomorphismFamilyEval φ))
    (e₀ : E) (hfix : ∀ t, φ t (p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion (diffeomorphismFamilyEval φ) hφ e₀ (hfix 0).symm)
    (hpres : hp.DiffeomorphismFamilyPreservesRecoveredSubgroup φ e₀ hfix)
    (hpresInv : hp.DiffeomorphismFamilyInversePreservesRecoveredSubgroup φ e₀ hfix)
    (r : Set E)
    (hrel : ∀ (t : unitInterval) (z : E), z ∈ r →
      hp.basedFamilyLift (diffeomorphismFamilyEval φ) hφ e₀ hfix hle (t, z) = z) :
    RelativeDiffeotopy r
      (hp.basedFamilyLiftRelativeSlice φ hφ e₀ hfix hle hpres hpresInv r hrel 0)
      (hp.basedFamilyLiftRelativeSlice φ hφ e₀ hfix hle hpres hpresInv r hrel 1) where
  toFun := hp.basedFamilyLift (diffeomorphismFamilyEval φ) hφ e₀ hfix hle
  contMDiff_toFun := hp.basedFamilyLift_contMDiff
    (diffeomorphismFamilyEval φ) hφ e₀ hfix hle
  slice t := ⟨hp.basedFamilyLiftRelativeSlice φ hφ e₀ hfix hle hpres hpresInv r hrel t,
    fun z ↦ (hp.basedFamilyLiftRelativeSlice_apply φ hφ e₀ hfix hle hpres hpresInv
      r hrel t z).symm⟩
  zero z := (hp.basedFamilyLiftRelativeSlice_apply φ hφ e₀ hfix hle hpres hpresInv
    r hrel 0 z).symm
  one z := (hp.basedFamilyLiftRelativeSlice_apply φ hφ e₀ hfix hle hpres hpresInv
    r hrel 1 z).symm

/-- The joint lift fixes the singleton containing its selected point. -/
theorem basedFamilyLift_fixes_singleton (hp : SmoothCover IE IX ∞ p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (φ : unitInterval → (X ≃ₘ^∞⟮IX, IX⟯ X))
    (hφ : ContMDiff ((𝓡∂ 1).prod IX) IX ∞ (diffeomorphismFamilyEval φ))
    (e₀ : E) (hfix : ∀ t, φ t (p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion (diffeomorphismFamilyEval φ) hφ e₀ (hfix 0).symm) :
    ∀ (t : unitInterval) (z : E), z ∈ ({e₀} : Set E) →
      hp.basedFamilyLift (diffeomorphismFamilyEval φ) hφ e₀ hfix hle (t, z) = z := by
  intro t z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  exact hp.basedFamilyLift_basepoint (diffeomorphismFamilyEval φ) hφ e₀ hfix hle t

/-- With no further relative hypothesis, the lifted family is a relative diffeotopy fixing the
selected point `e₀`. -/
noncomputable def basedFamilyLiftSingletonDiffeotopy (hp : SmoothCover IE IX ∞ p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (φ : unitInterval → (X ≃ₘ^∞⟮IX, IX⟯ X))
    (hφ : ContMDiff ((𝓡∂ 1).prod IX) IX ∞ (diffeomorphismFamilyEval φ))
    (e₀ : E) (hfix : ∀ t, φ t (p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion (diffeomorphismFamilyEval φ) hφ e₀ (hfix 0).symm)
    (hpres : hp.DiffeomorphismFamilyPreservesRecoveredSubgroup φ e₀ hfix)
    (hpresInv : hp.DiffeomorphismFamilyInversePreservesRecoveredSubgroup φ e₀ hfix) :
    RelativeDiffeotopy ({e₀} : Set E)
      (hp.basedFamilyLiftRelativeSlice φ hφ e₀ hfix hle hpres hpresInv {e₀}
        (hp.basedFamilyLift_fixes_singleton φ hφ e₀ hfix hle) 0)
      (hp.basedFamilyLiftRelativeSlice φ hφ e₀ hfix hle hpres hpresInv {e₀}
        (hp.basedFamilyLift_fixes_singleton φ hφ e₀ hfix hle) 1) :=
  hp.basedFamilyLiftRelativeDiffeotopy φ hφ e₀ hfix hle hpres hpresInv {e₀}
    (hp.basedFamilyLift_fixes_singleton φ hφ e₀ hfix hle)

end SmoothCover

end SplittingSpheres
