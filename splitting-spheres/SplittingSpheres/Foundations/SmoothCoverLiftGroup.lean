/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothCoverDiffeotopyLift

/-!
# The group of two-sided liftable diffeomorphisms

For a pointed smooth cover, this file isolates the honest subgroup of base diffeomorphisms which
fix the projected point and for which both the diffeomorphism and its inverse preserve the
subgroup recovered by the cover.  The two preservation conditions are precisely those used by
`SmoothCover.basedLiftDiffeomorph`; neither one is inferred from the other.

Canonical based lifting is then a group homomorphism into the relative diffeomorphism group of
the total space fixing the selected point.
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

/-- A base diffeomorphism is two-sided liftable at `e₀` when it fixes `p e₀` and both it and its
inverse preserve the subgroup recovered by the pointed cover. -/
def TwoSidedLiftable (hp : SmoothCover IE IX n p) (e₀ : E)
    (f : X ≃ₘ^n⟮IX, IX⟯ X) : Prop :=
  ∃ hfix : f (p e₀) = p e₀,
    hp.PreservesRecoveredSubgroup f f.continuous e₀ hfix ∧
      hp.PreservesRecoveredSubgroup f.symm f.symm.continuous e₀
        (fixedPoint_symm_diffeomorph f hfix)

/-- Recovered-subgroup preservation is invariant under equality of the underlying self-maps;
the continuity and fixed-point proof arguments are propositions and hence proof-irrelevant. -/
theorem preservesRecoveredSubgroup_congr (hp : SmoothCover IE IX n p)
    {f g : X → X} (hf : Continuous f) (hg : Continuous g)
    (hfixF : f (p e₀) = p e₀) (hfixG : g (p e₀) = p e₀)
    (hfg : f = g) (hpres : hp.PreservesRecoveredSubgroup f hf e₀ hfixF) :
    hp.PreservesRecoveredSubgroup g hg e₀ hfixG := by
  subst g
  exact hpres

/-- The identity base diffeomorphism is two-sided liftable. -/
theorem twoSidedLiftable_one (hp : SmoothCover IE IX n p) (e₀ : E) :
    hp.TwoSidedLiftable e₀ (1 : X ≃ₘ^n⟮IX, IX⟯ X) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact hp.preservesRecoveredSubgroup_id e₀
  · exact hp.preservesRecoveredSubgroup_id e₀

/-- Two-sided liftability is closed under diffeomorphism composition, in TauCeti's group order
`(f * g) x = f (g x)`. -/
theorem TwoSidedLiftable.mul (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    {f g : X ≃ₘ^n⟮IX, IX⟯ X}
    (hf : hp.TwoSidedLiftable e₀ f) (hg : hp.TwoSidedLiftable e₀ g) :
    hp.TwoSidedLiftable e₀ (f * g) := by
  obtain ⟨hfixF, hpresF, hpresFInv⟩ := hf
  obtain ⟨hfixG, hpresG, hpresGInv⟩ := hg
  have hfix : (f * g) (p e₀) = p e₀ := by
    rw [TauCeti.Diffeomorph.mul_apply, hfixG, hfixF]
  refine ⟨hfix, ?_, ?_⟩
  · apply hp.preservesRecoveredSubgroup_congr
      (f.continuous.comp g.continuous) (f * g).continuous
      (fixedPoint_comp hfixG hfixF) hfix
    · funext x
      rfl
    · exact hp.preservesRecoveredSubgroup_comp g f g.contMDiff f.contMDiff e₀
        hfixG hfixF hpresG hpresF
  · apply hp.preservesRecoveredSubgroup_congr
      (g.symm.continuous.comp f.symm.continuous) (f * g).symm.continuous
      (fixedPoint_comp (fixedPoint_symm_diffeomorph f hfixF)
        (fixedPoint_symm_diffeomorph g hfixG))
      (fixedPoint_symm_diffeomorph (f * g) hfix)
    · funext x
      rfl
    · exact hp.preservesRecoveredSubgroup_comp f.symm g.symm
        f.symm.contMDiff g.symm.contMDiff e₀
        (fixedPoint_symm_diffeomorph f hfixF)
        (fixedPoint_symm_diffeomorph g hfixG) hpresFInv hpresGInv

/-- Two-sided liftability is closed under inverse by swapping its two preservation witnesses. -/
theorem TwoSidedLiftable.inv (hp : SmoothCover IE IX n p)
    {f : X ≃ₘ^n⟮IX, IX⟯ X} (hf : hp.TwoSidedLiftable e₀ f) :
    hp.TwoSidedLiftable e₀ f⁻¹ := by
  obtain ⟨hfix, hpres, hpresInv⟩ := hf
  let hfixInv := fixedPoint_symm_diffeomorph f hfix
  refine ⟨hfixInv, ?_, ?_⟩
  · exact hpresInv
  · apply hp.preservesRecoveredSubgroup_congr f.continuous f⁻¹.symm.continuous hfix
      (fixedPoint_symm_diffeomorph f⁻¹ hfixInv)
    · funext x
      rfl
    · exact hpres

/-- The subgroup of base diffeomorphisms admitting canonical based lifts in both directions. -/
def twoSidedLiftableSubgroup (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E) :
    Subgroup (X ≃ₘ^n⟮IX, IX⟯ X) where
  carrier := hp.TwoSidedLiftable e₀
  one_mem' := hp.twoSidedLiftable_one e₀
  mul_mem' hf hg := hf.mul hp hg
  inv_mem' hf := hf.inv hp

/-- The canonical fixed-point proof carried by an element of the liftable subgroup. -/
theorem twoSidedLiftable_fixed (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : hp.twoSidedLiftableSubgroup e₀) : f.1 (p e₀) = p e₀ :=
  Classical.choose f.2

/-- Forward preservation extracted from a liftable subgroup element. -/
theorem twoSidedLiftable_preserves (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : hp.twoSidedLiftableSubgroup e₀) :
    hp.PreservesRecoveredSubgroup f.1 f.1.continuous e₀
      (hp.twoSidedLiftable_fixed e₀ f) := by
  exact (Classical.choose_spec f.2).1

/-- Inverse preservation extracted from a liftable subgroup element. -/
theorem twoSidedLiftable_preserves_symm (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : hp.twoSidedLiftableSubgroup e₀) :
    hp.PreservesRecoveredSubgroup f.1.symm f.1.symm.continuous e₀
      (fixedPoint_symm_diffeomorph f.1 (hp.twoSidedLiftable_fixed e₀ f)) := by
  exact (Classical.choose_spec f.2).2

/-- The canonical total-space diffeomorphism lifting a two-sided liftable base diffeomorphism. -/
noncomputable def liftableDiffeomorphLift (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : hp.twoSidedLiftableSubgroup e₀) : E ≃ₘ^n⟮IE, IE⟯ E :=
  hp.basedLiftDiffeomorph f.1 e₀ (hp.twoSidedLiftable_fixed e₀ f)
    (fixedPoint_symm_diffeomorph f.1 (hp.twoSidedLiftable_fixed e₀ f))
    (hp.twoSidedLiftable_preserves e₀ f) (hp.twoSidedLiftable_preserves_symm e₀ f)

/-- The lift's underlying map is the canonical forward based lift. -/
@[simp]
theorem liftableDiffeomorphLift_apply (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : hp.twoSidedLiftableSubgroup e₀) (z : E) :
    hp.liftableDiffeomorphLift e₀ f z =
      hp.basedLift f.1 f.1.contMDiff e₀ (hp.twoSidedLiftable_fixed e₀ f)
        (hp.twoSidedLiftable_preserves e₀ f) z :=
  rfl

/-- Projection of the canonical group lift recovers the base action. -/
theorem proj_liftableDiffeomorphLift (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : hp.twoSidedLiftableSubgroup e₀) (z : E) :
    p (hp.liftableDiffeomorphLift e₀ f z) = f.1 (p z) :=
  hp.proj_basedLift f.1 f.1.contMDiff e₀ z (hp.twoSidedLiftable_fixed e₀ f)
    (hp.twoSidedLiftable_preserves e₀ f)

/-- Every canonical group lift fixes the selected point upstairs. -/
@[simp]
theorem liftableDiffeomorphLift_basepoint (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : hp.twoSidedLiftableSubgroup e₀) :
    hp.liftableDiffeomorphLift e₀ f e₀ = e₀ :=
  hp.basedLift_basepoint f.1 f.1.contMDiff e₀ (hp.twoSidedLiftable_fixed e₀ f)
    (hp.twoSidedLiftable_preserves e₀ f)

/-- Canonical lifting respects TauCeti diffeomorphism multiplication. -/
theorem liftableDiffeomorphLift_mul (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f g : hp.twoSidedLiftableSubgroup e₀) :
    hp.liftableDiffeomorphLift e₀ (f * g) =
      hp.liftableDiffeomorphLift e₀ f * hp.liftableDiffeomorphLift e₀ g := by
  have hEq :
      (fun z ↦ hp.liftableDiffeomorphLift e₀ (f * g) z) =
        hp.liftableDiffeomorphLift e₀ f ∘ hp.liftableDiffeomorphLift e₀ g := by
    apply hp.eq_of_contMDiff_lifts (e₀ := e₀)
    · exact (hp.liftableDiffeomorphLift e₀ (f * g)).contMDiff
    · exact (hp.liftableDiffeomorphLift e₀ f).contMDiff.comp
        (hp.liftableDiffeomorphLift e₀ g).contMDiff
    · funext z
      change p (hp.liftableDiffeomorphLift e₀ (f * g) z) =
        p (hp.liftableDiffeomorphLift e₀ f (hp.liftableDiffeomorphLift e₀ g z))
      rw [hp.proj_liftableDiffeomorphLift e₀ (f * g) z,
        hp.proj_liftableDiffeomorphLift e₀ f,
        hp.proj_liftableDiffeomorphLift e₀ g,
        Subgroup.coe_mul, TauCeti.Diffeomorph.mul_apply]
    · change hp.liftableDiffeomorphLift e₀ (f * g) e₀ =
        hp.liftableDiffeomorphLift e₀ f (hp.liftableDiffeomorphLift e₀ g e₀)
      rw [hp.liftableDiffeomorphLift_basepoint e₀,
        hp.liftableDiffeomorphLift_basepoint e₀,
        hp.liftableDiffeomorphLift_basepoint e₀]
  apply Diffeomorph.ext
  intro z
  exact congrFun hEq z

/-- Regard the canonical lift as a relative diffeomorphism fixing `{e₀}`. -/
noncomputable def liftableDiffeomorphRelativeLift (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : hp.twoSidedLiftableSubgroup e₀) :
    TauCeti.RelativeDiff (I := IE) E n ({e₀} : Set E) := by
  refine ⟨hp.liftableDiffeomorphLift e₀ f, ?_⟩
  apply TauCeti.Diffeomorph.mem_fixingSubgroup_of_forall
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  exact hp.liftableDiffeomorphLift_basepoint e₀ f

/-- Forgetting relative fixedness recovers the canonical lifted diffeomorphism. -/
@[simp]
theorem liftableDiffeomorphRelativeLift_toDiffeomorph (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : hp.twoSidedLiftableSubgroup e₀) :
    (hp.liftableDiffeomorphRelativeLift e₀ f).1 = hp.liftableDiffeomorphLift e₀ f :=
  rfl

/-- Canonical based lifting is a group homomorphism into the smooth diffeomorphisms of the total
space fixing `e₀`. -/
noncomputable def liftableDiffeomorphLiftHom (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E) :
    hp.twoSidedLiftableSubgroup e₀ →*
      TauCeti.RelativeDiff (I := IE) E n ({e₀} : Set E) :=
  MonoidHom.mk' (hp.liftableDiffeomorphRelativeLift e₀) fun f g ↦ by
    apply Subtype.ext
    exact hp.liftableDiffeomorphLift_mul e₀ f g

/-- Application law for the canonical lift homomorphism. -/
@[simp]
theorem liftableDiffeomorphLiftHom_apply (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : hp.twoSidedLiftableSubgroup e₀) (z : E) :
    (hp.liftableDiffeomorphLiftHom e₀ f).1 z = hp.liftableDiffeomorphLift e₀ f z :=
  rfl

/-- Projection law for the canonical lift homomorphism. -/
theorem proj_liftableDiffeomorphLiftHom (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : hp.twoSidedLiftableSubgroup e₀) (z : E) :
    p ((hp.liftableDiffeomorphLiftHom e₀ f).1 z) = f.1 (p z) :=
  hp.proj_liftableDiffeomorphLift e₀ f z

/-- Multiplication law for canonical group lifts. -/
@[simp]
theorem liftableDiffeomorphLiftHom_mul (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f g : hp.twoSidedLiftableSubgroup e₀) :
    hp.liftableDiffeomorphLiftHom e₀ (f * g) =
      hp.liftableDiffeomorphLiftHom e₀ f * hp.liftableDiffeomorphLiftHom e₀ g :=
  map_mul (hp.liftableDiffeomorphLiftHom e₀) f g

/-- Inverse law for canonical group lifts. -/
@[simp]
theorem liftableDiffeomorphLiftHom_inv (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : hp.twoSidedLiftableSubgroup e₀) :
    hp.liftableDiffeomorphLiftHom e₀ f⁻¹ = (hp.liftableDiffeomorphLiftHom e₀ f)⁻¹ :=
  map_inv (hp.liftableDiffeomorphLiftHom e₀) f

/-- Identity law for canonical group lifts. -/
@[simp]
theorem liftableDiffeomorphLiftHom_one (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E) :
    hp.liftableDiffeomorphLiftHom e₀ 1 = 1 :=
  map_one (hp.liftableDiffeomorphLiftHom e₀)

end SmoothCover

end SplittingSpheres
