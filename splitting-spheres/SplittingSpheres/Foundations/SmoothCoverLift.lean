/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothCover
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph

/-!
# Based smooth lifts through smooth covers

This file packages the unique lift of a smooth based self-map through a smooth cover.  The
hypothesis is stated intrinsically: the induced map sends the subgroup recovered by the cover
into that same subgroup, transported along the supplied fixed-point equality.
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

/-- The subgroup of the fundamental group of the base recovered by a pointed cover. -/
def recoveredSubgroup (hp : SmoothCover IE IX n p) (e₀ : E) :
    Subgroup (_root_.FundamentalGroup X (p e₀)) :=
  (_root_.FundamentalGroup.map ⟨p, hp.continuous⟩ e₀).range

/-- A based self-map preserves the subgroup recovered by a smooth cover.

The codomain subgroup is transported from the basepoint `p e₀` to `f (p e₀)` along the
inverse of the supplied fixed-point equality.  Thus this formulation is definitionally aligned
with the fundamental-group lifting criterion. -/
def PreservesRecoveredSubgroup (hp : SmoothCover IE IX n p) (f : X → X)
    (hf : Continuous f) (e₀ : E) (hfix : f (p e₀) = p e₀) : Prop :=
  (hp.recoveredSubgroup e₀).map
      (_root_.FundamentalGroup.map ⟨f, hf⟩ (p e₀)) ≤
    (_root_.FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hfix.symm).range

/-- Preservation of the recovered subgroup supplies the range inclusion in the lifting
criterion for `f ∘ p`. -/
theorem range_map_comp_le_of_preservesRecoveredSubgroup
    (hp : SmoothCover IE IX n p) (f : X → X) (hf : Continuous f)
    (e₀ : E) (hfix : f (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup f hf e₀ hfix) :
    (_root_.FundamentalGroup.map ⟨f ∘ p, hf.comp hp.continuous⟩ e₀).range ≤
      (_root_.FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hfix.symm).range := by
  rintro _ ⟨γ, rfl⟩
  apply hpres
  refine ⟨_root_.FundamentalGroup.map ⟨p, hp.continuous⟩ e₀ γ, ⟨γ, rfl⟩, ?_⟩
  let fC : C(X, X) := ⟨f, hf⟩
  let pC : C(E, X) := ⟨p, hp.continuous⟩
  let fpC : C(E, X) := ⟨f ∘ p, hf.comp hp.continuous⟩
  have hcomp := TauCeti.FundamentalGroup.mapOfEq_comp fC pC rfl rfl γ
  have hmaps : fC.comp pC = fpC := by
    ext z
    rfl
  have hcongr := TauCeti.FundamentalGroup.mapOfEq_congr hmaps rfl rfl γ
  simpa [fC, pC, fpC] using hcomp.trans hcongr

/-- The range form of the lifting criterion also recovers subgroup preservation. -/
theorem preservesRecoveredSubgroup_of_range_map_comp_le
    (hp : SmoothCover IE IX n p) (f : X → X) (hf : Continuous f)
    (e₀ : E) (hfix : f (p e₀) = p e₀)
    (hle : (_root_.FundamentalGroup.map ⟨f ∘ p, hf.comp hp.continuous⟩ e₀).range ≤
      (_root_.FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hfix.symm).range) :
    hp.PreservesRecoveredSubgroup f hf e₀ hfix := by
  rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩
  let fC : C(X, X) := ⟨f, hf⟩
  let pC : C(E, X) := ⟨p, hp.continuous⟩
  let fpC : C(E, X) := ⟨f ∘ p, hf.comp hp.continuous⟩
  have hcomp := TauCeti.FundamentalGroup.mapOfEq_comp fC pC rfl rfl γ
  have hmaps : fC.comp pC = fpC := by
    ext z
    rfl
  have hcongr := TauCeti.FundamentalGroup.mapOfEq_congr hmaps rfl rfl γ
  have happly :
      _root_.FundamentalGroup.map ⟨f, hf⟩ (p e₀)
          (_root_.FundamentalGroup.map ⟨p, hp.continuous⟩ e₀ γ) =
        _root_.FundamentalGroup.map ⟨f ∘ p, hf.comp hp.continuous⟩ e₀ γ := by
    simpa [fC, pC, fpC] using hcomp.trans hcongr
  rw [happly]
  exact hle ⟨γ, rfl⟩

/-- Recovered-subgroup preservation is exactly the range inclusion used by the covering-space
lifting criterion. -/
theorem preservesRecoveredSubgroup_iff_range_map_comp_le
    (hp : SmoothCover IE IX n p) (f : X → X) (hf : Continuous f)
    (e₀ : E) (hfix : f (p e₀) = p e₀) :
    hp.PreservesRecoveredSubgroup f hf e₀ hfix ↔
      (_root_.FundamentalGroup.map ⟨f ∘ p, hf.comp hp.continuous⟩ e₀).range ≤
        (_root_.FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hfix.symm).range :=
  ⟨hp.range_map_comp_le_of_preservesRecoveredSubgroup f hf e₀ hfix,
    hp.preservesRecoveredSubgroup_of_range_map_comp_le f hf e₀ hfix⟩

/-- The existence of a continuous based lift implies the range inclusion in the lifting
criterion.  Unlike the converse, this direction needs no connectedness assumptions. -/
theorem range_map_comp_le_of_continuous_lift
    (hp : SmoothCover IE IX n p) (f : X → X) (hf : Continuous f)
    (e₀ : E) (hfix : f (p e₀) = p e₀) {F : E → E}
    (hF : Continuous F) (hF₀ : F e₀ = e₀) (hFproj : p ∘ F = f ∘ p) :
    (_root_.FundamentalGroup.map ⟨f ∘ p, hf.comp hp.continuous⟩ e₀).range ≤
      (_root_.FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hfix.symm).range := by
  let FC : C(E, E) := ⟨F, hF⟩
  let pC : C(E, X) := ⟨p, hp.continuous⟩
  let fpC : C(E, X) := ⟨f ∘ p, hf.comp hp.continuous⟩
  have hmaps : pC.comp FC = fpC := by
    ext z
    exact congrFun hFproj z
  rintro _ ⟨γ, rfl⟩
  refine ⟨_root_.FundamentalGroup.mapOfEq FC hF₀ γ, ?_⟩
  rw [TauCeti.FundamentalGroup.mapOfEq_comp pC FC hF₀ hfix.symm]
  simpa [fpC, TauCeti.FundamentalGroup.mapOfEq_rfl] using
    TauCeti.FundamentalGroup.mapOfEq_congr hmaps _ rfl γ

/-- A smooth based self-map preserving the recovered subgroup has a unique smooth lift fixing
the selected point of the fibre. -/
theorem existsUnique_basedLift (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (f : X → X) (hf : ContMDiff IX IX n f) (e₀ : E)
    (hfix : f (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup f hf.continuous e₀ hfix) :
    ∃! F : E → E,
      ContMDiff IE IE n F ∧ F e₀ = e₀ ∧ p ∘ F = f ∘ p := by
  exact hp.existsUnique_contMDiff_lift_of_range_le
    (hf.comp hp.contMDiff) hfix.symm
    (hp.range_map_comp_le_of_preservesRecoveredSubgroup f hf.continuous e₀ hfix hpres)

/-- The canonical smooth lift of a based self-map preserving the subgroup recovered by the
cover.  It is selected from `existsUnique_basedLift`; its equations are exposed below. -/
noncomputable def basedLift (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (f : X → X) (hf : ContMDiff IX IX n f) (e₀ : E)
    (hfix : f (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup f hf.continuous e₀ hfix) : E → E :=
  Classical.choose (hp.existsUnique_basedLift f hf e₀ hfix hpres)

/-- The defining properties of the canonical based lift. -/
theorem basedLift_spec (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (f : X → X) (hf : ContMDiff IX IX n f) (e₀ : E)
    (hfix : f (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup f hf.continuous e₀ hfix) :
    ContMDiff IE IE n (hp.basedLift f hf e₀ hfix hpres) ∧
      hp.basedLift f hf e₀ hfix hpres e₀ = e₀ ∧
      p ∘ hp.basedLift f hf e₀ hfix hpres = f ∘ p :=
  (Classical.choose_spec (hp.existsUnique_basedLift f hf e₀ hfix hpres)).1

/-- The canonical based lift is smooth. -/
theorem basedLift_contMDiff (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (f : X → X) (hf : ContMDiff IX IX n f) (e₀ : E)
    (hfix : f (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup f hf.continuous e₀ hfix) :
    ContMDiff IE IE n (hp.basedLift f hf e₀ hfix hpres) :=
  (hp.basedLift_spec f hf e₀ hfix hpres).1

/-- The canonical lift fixes the selected point in the fibre. -/
@[simp]
theorem basedLift_basepoint (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (f : X → X) (hf : ContMDiff IX IX n f) (e₀ : E)
    (hfix : f (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup f hf.continuous e₀ hfix) :
    hp.basedLift f hf e₀ hfix hpres e₀ = e₀ :=
  (hp.basedLift_spec f hf e₀ hfix hpres).2.1

/-- Projecting the canonical lift gives the original self-map after projection. -/
theorem comp_basedLift (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (f : X → X) (hf : ContMDiff IX IX n f) (e₀ : E)
    (hfix : f (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup f hf.continuous e₀ hfix) :
    p ∘ hp.basedLift f hf e₀ hfix hpres = f ∘ p :=
  (hp.basedLift_spec f hf e₀ hfix hpres).2.2

/-- Pointwise projection formula for the canonical based lift. -/
theorem proj_basedLift (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (f : X → X) (hf : ContMDiff IX IX n f) (e₀ z : E)
    (hfix : f (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup f hf.continuous e₀ hfix) :
    p (hp.basedLift f hf e₀ hfix hpres z) = f (p z) :=
  congrFun (hp.comp_basedLift f hf e₀ hfix hpres) z

/-- Any smooth based lift with the required projection formula is the canonical lift. -/
theorem eq_basedLift (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (f : X → X) (hf : ContMDiff IX IX n f) (e₀ : E)
    (hfix : f (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup f hf.continuous e₀ hfix)
    {F : E → E} (hF : ContMDiff IE IE n F) (hF₀ : F e₀ = e₀)
    (hFproj : p ∘ F = f ∘ p) :
    F = hp.basedLift f hf e₀ hfix hpres :=
  (Classical.choose_spec (hp.existsUnique_basedLift f hf e₀ hfix hpres)).2 F
    ⟨hF, hF₀, hFproj⟩

/-- A convenient bundled smooth-map form of the canonical lift. -/
noncomputable def basedLiftContMDiffMap (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (f : X → X) (hf : ContMDiff IX IX n f) (e₀ : E)
    (hfix : f (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup f hf.continuous e₀ hfix) :
    C^n⟮IE, E; IE, E⟯ :=
  ⟨hp.basedLift f hf e₀ hfix hpres,
    hp.basedLift_contMDiff f hf e₀ hfix hpres⟩

/-- Uniqueness of continuous (hence, in particular, smooth) based lifts through a connected
cover.  This form does not require either lift to have been obtained from the lifting criterion. -/
theorem eq_of_contMDiff_lifts (hp : SmoothCover IE IX n p)
    [PreconnectedSpace E] {F G : E → E} (hF : ContMDiff IE IE n F)
    (hG : ContMDiff IE IE n G) (hproj : p ∘ F = p ∘ G)
    (e₀ : E) (hbase : F e₀ = G e₀) : F = G :=
  hp.isCoveringMap.eq_of_comp_eq hF.continuous hG.continuous hproj e₀ hbase

/-- The identity self-map preserves every recovered subgroup. -/
theorem preservesRecoveredSubgroup_id (hp : SmoothCover IE IX n p) (e₀ : E) :
    hp.PreservesRecoveredSubgroup id continuous_id e₀ rfl := by
  let iC : C(X, X) := ⟨id, continuous_id⟩
  have hi : iC = ContinuousMap.id X := by
    ext z
    rfl
  have hmapid :
      _root_.FundamentalGroup.map iC (p e₀) =
        MonoidHom.id (_root_.FundamentalGroup X (p e₀)) := by
    ext δ
    have hcongr := TauCeti.FundamentalGroup.mapOfEq_congr hi rfl rfl δ
    have hid := TauCeti.FundamentalGroup.mapOfEq_id
      (X := X) (x := p e₀) rfl δ
    simpa only [TauCeti.FundamentalGroup.mapOfEq_rfl, MonoidHom.id_apply] using
      hcongr.trans hid
  unfold PreservesRecoveredSubgroup
  change (hp.recoveredSubgroup e₀).map
      (_root_.FundamentalGroup.map iC (p e₀)) ≤
    (_root_.FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ rfl).range
  rw [hmapid, Subgroup.map_id]
  simpa only [recoveredSubgroup, TauCeti.FundamentalGroup.mapOfEq_rfl] using
    (le_refl (_root_.FundamentalGroup.map ⟨p, hp.continuous⟩ e₀).range)

/-- The canonical based lift of the identity is the identity. -/
theorem basedLift_id (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E) :
    hp.basedLift id contMDiff_id e₀ rfl (hp.preservesRecoveredSubgroup_id e₀) = id := by
  symm
  apply hp.eq_basedLift id contMDiff_id e₀ rfl (hp.preservesRecoveredSubgroup_id e₀)
  · exact contMDiff_id
  · rfl
  · funext z
    rfl

omit [TopologicalSpace X] in
/-- The composite of two self-maps fixing a point fixes that point. -/
theorem fixedPoint_comp {f g : X → X} {x : X} (hfixF : f x = x) (hfixG : g x = x) :
    (g ∘ f) x = x := by
  rw [Function.comp_apply, hfixF, hfixG]

/-- Preservation of the recovered subgroup is closed under composition.  The proof composes the
two canonical lifts and then applies the forward direction of the lifting criterion. -/
theorem preservesRecoveredSubgroup_comp (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (f g : X → X) (hf : ContMDiff IX IX n f) (hg : ContMDiff IX IX n g)
    (e₀ : E) (hfixF : f (p e₀) = p e₀) (hfixG : g (p e₀) = p e₀)
    (hpresF : hp.PreservesRecoveredSubgroup f hf.continuous e₀ hfixF)
    (hpresG : hp.PreservesRecoveredSubgroup g hg.continuous e₀ hfixG) :
    hp.PreservesRecoveredSubgroup (g ∘ f) (hg.continuous.comp hf.continuous) e₀
      (fixedPoint_comp hfixF hfixG) := by
  apply hp.preservesRecoveredSubgroup_of_range_map_comp_le
  apply hp.range_map_comp_le_of_continuous_lift (g ∘ f)
    (hg.continuous.comp hf.continuous) e₀ (fixedPoint_comp hfixF hfixG)
    (F := hp.basedLift g hg e₀ hfixG hpresG ∘ hp.basedLift f hf e₀ hfixF hpresF)
  · exact (hp.basedLift_contMDiff g hg e₀ hfixG hpresG).continuous.comp
      (hp.basedLift_contMDiff f hf e₀ hfixF hpresF).continuous
  · change hp.basedLift g hg e₀ hfixG hpresG
        (hp.basedLift f hf e₀ hfixF hpresF e₀) = e₀
    rw [hp.basedLift_basepoint f hf e₀ hfixF hpresF,
      hp.basedLift_basepoint g hg e₀ hfixG hpresG]
  · funext z
    change p (hp.basedLift g hg e₀ hfixG hpresG
      (hp.basedLift f hf e₀ hfixF hpresF z)) = g (f (p z))
    rw [hp.proj_basedLift g hg e₀ _ hfixG hpresG,
      hp.proj_basedLift f hf e₀ z hfixF hpresF]

/-- Canonical based lifts respect composition.  The order agrees with function composition: the
lift of `g ∘ f` is the lift of `g` after the lift of `f`. -/
theorem basedLift_comp (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (f g : X → X) (hf : ContMDiff IX IX n f) (hg : ContMDiff IX IX n g)
    (e₀ : E) (hfixF : f (p e₀) = p e₀) (hfixG : g (p e₀) = p e₀)
    (hpresF : hp.PreservesRecoveredSubgroup f hf.continuous e₀ hfixF)
    (hpresG : hp.PreservesRecoveredSubgroup g hg.continuous e₀ hfixG) :
    hp.basedLift (g ∘ f) (hg.comp hf) e₀ (fixedPoint_comp hfixF hfixG)
        (hp.preservesRecoveredSubgroup_comp f g hf hg e₀ hfixF hfixG hpresF hpresG) =
      hp.basedLift g hg e₀ hfixG hpresG ∘
        hp.basedLift f hf e₀ hfixF hpresF := by
  symm
  apply hp.eq_basedLift (g ∘ f) (hg.comp hf) e₀ (fixedPoint_comp hfixF hfixG)
    (hp.preservesRecoveredSubgroup_comp f g hf hg e₀ hfixF hfixG hpresF hpresG)
  · exact (hp.basedLift_contMDiff g hg e₀ hfixG hpresG).comp
      (hp.basedLift_contMDiff f hf e₀ hfixF hpresF)
  · change hp.basedLift g hg e₀ hfixG hpresG
        (hp.basedLift f hf e₀ hfixF hpresF e₀) = e₀
    rw [hp.basedLift_basepoint f hf e₀ hfixF hpresF,
      hp.basedLift_basepoint g hg e₀ hfixG hpresG]
  · funext z
    change p (hp.basedLift g hg e₀ hfixG hpresG
      (hp.basedLift f hf e₀ hfixF hpresF z)) = g (f (p z))
    rw [hp.proj_basedLift g hg e₀ _ hfixG hpresG,
      hp.proj_basedLift f hf e₀ z hfixF hpresF]

/-- A fixed point of a diffeomorphism is also fixed by its inverse. -/
theorem fixedPoint_symm_diffeomorph (e : X ≃ₘ^n⟮IX, IX⟯ X) {x : X}
    (hfix : e x = x) : e.symm x = x :=
  e.toEquiv.symm_apply_eq.mpr hfix.symm

/-- The lift of the inverse followed by the lift of a diffeomorphism is the identity, provided
both directions preserve the recovered subgroup. -/
theorem basedLift_symm_comp (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e : X ≃ₘ^n⟮IX, IX⟯ X) (e₀ : E)
    (hfix : e (p e₀) = p e₀) (hfixSymm : e.symm (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup e e.continuous e₀ hfix)
    (hpresSymm : hp.PreservesRecoveredSubgroup e.symm e.symm.continuous e₀ hfixSymm) :
    hp.basedLift e.symm e.symm.contMDiff e₀ hfixSymm hpresSymm ∘
      hp.basedLift e e.contMDiff e₀ hfix hpres = id := by
  apply hp.eq_of_contMDiff_lifts (e₀ := e₀)
  · exact (hp.basedLift_contMDiff e.symm e.symm.contMDiff e₀ hfixSymm hpresSymm).comp
      (hp.basedLift_contMDiff e e.contMDiff e₀ hfix hpres)
  · exact contMDiff_id
  · funext z
    change p (hp.basedLift e.symm e.symm.contMDiff e₀ hfixSymm hpresSymm
      (hp.basedLift e e.contMDiff e₀ hfix hpres z)) = p z
    rw [hp.proj_basedLift e.symm e.symm.contMDiff e₀ _ hfixSymm hpresSymm,
      hp.proj_basedLift e e.contMDiff e₀ z hfix hpres, e.symm_apply_apply]
  · change hp.basedLift e.symm e.symm.contMDiff e₀ hfixSymm hpresSymm
        (hp.basedLift e e.contMDiff e₀ hfix hpres e₀) = e₀
    rw [hp.basedLift_basepoint e e.contMDiff e₀ hfix hpres,
      hp.basedLift_basepoint e.symm e.symm.contMDiff e₀ hfixSymm hpresSymm]

/-- The lift of a diffeomorphism followed by the lift of its inverse is the identity. -/
theorem basedLift_comp_symm (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e : X ≃ₘ^n⟮IX, IX⟯ X) (e₀ : E)
    (hfix : e (p e₀) = p e₀) (hfixSymm : e.symm (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup e e.continuous e₀ hfix)
    (hpresSymm : hp.PreservesRecoveredSubgroup e.symm e.symm.continuous e₀ hfixSymm) :
    hp.basedLift e e.contMDiff e₀ hfix hpres ∘
      hp.basedLift e.symm e.symm.contMDiff e₀ hfixSymm hpresSymm = id := by
  apply hp.eq_of_contMDiff_lifts (e₀ := e₀)
  · exact (hp.basedLift_contMDiff e e.contMDiff e₀ hfix hpres).comp
      (hp.basedLift_contMDiff e.symm e.symm.contMDiff e₀ hfixSymm hpresSymm)
  · exact contMDiff_id
  · funext z
    change p (hp.basedLift e e.contMDiff e₀ hfix hpres
      (hp.basedLift e.symm e.symm.contMDiff e₀ hfixSymm hpresSymm z)) = p z
    rw [hp.proj_basedLift e e.contMDiff e₀ _ hfix hpres,
      hp.proj_basedLift e.symm e.symm.contMDiff e₀ z hfixSymm hpresSymm,
      e.apply_symm_apply]
  · change hp.basedLift e e.contMDiff e₀ hfix hpres
        (hp.basedLift e.symm e.symm.contMDiff e₀ hfixSymm hpresSymm e₀) = e₀
    rw [hp.basedLift_basepoint e.symm e.symm.contMDiff e₀ hfixSymm hpresSymm,
      hp.basedLift_basepoint e e.contMDiff e₀ hfix hpres]

/-- A based diffeomorphism whose forward and inverse maps preserve the recovered subgroup lifts
to a diffeomorphism of the total space. -/
noncomputable def basedLiftDiffeomorph (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e : X ≃ₘ^n⟮IX, IX⟯ X) (e₀ : E)
    (hfix : e (p e₀) = p e₀) (hfixSymm : e.symm (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup e e.continuous e₀ hfix)
    (hpresSymm : hp.PreservesRecoveredSubgroup e.symm e.symm.continuous e₀ hfixSymm) :
    E ≃ₘ^n⟮IE, IE⟯ E where
  toEquiv :=
    { toFun := hp.basedLift e e.contMDiff e₀ hfix hpres
      invFun := hp.basedLift e.symm e.symm.contMDiff e₀ hfixSymm hpresSymm
      left_inv := congrFun (hp.basedLift_symm_comp e e₀ hfix hfixSymm hpres hpresSymm)
      right_inv := congrFun (hp.basedLift_comp_symm e e₀ hfix hfixSymm hpres hpresSymm) }
  contMDiff_toFun := hp.basedLift_contMDiff e e.contMDiff e₀ hfix hpres
  contMDiff_invFun :=
    hp.basedLift_contMDiff e.symm e.symm.contMDiff e₀ hfixSymm hpresSymm

/-- The one-fixed-point convenience form of `basedLiftDiffeomorph`; the inverse fixed-point
equation is derived rather than requested separately. -/
noncomputable def basedLiftDiffeomorphOfFixedPoint (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e : X ≃ₘ^n⟮IX, IX⟯ X) (e₀ : E)
    (hfix : e (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup e e.continuous e₀ hfix)
    (hpresSymm : hp.PreservesRecoveredSubgroup e.symm e.symm.continuous e₀
      (fixedPoint_symm_diffeomorph e hfix)) : E ≃ₘ^n⟮IE, IE⟯ E :=
  hp.basedLiftDiffeomorph e e₀ hfix (fixedPoint_symm_diffeomorph e hfix) hpres hpresSymm

/-- The lifted diffeomorphism has the canonical forward based lift as its underlying map. -/
@[simp]
theorem basedLiftDiffeomorph_apply (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e : X ≃ₘ^n⟮IX, IX⟯ X) (e₀ z : E)
    (hfix : e (p e₀) = p e₀) (hfixSymm : e.symm (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup e e.continuous e₀ hfix)
    (hpresSymm : hp.PreservesRecoveredSubgroup e.symm e.symm.continuous e₀ hfixSymm) :
    hp.basedLiftDiffeomorph e e₀ hfix hfixSymm hpres hpresSymm z =
      hp.basedLift e e.contMDiff e₀ hfix hpres z :=
  rfl

/-- The inverse of the lifted diffeomorphism is the canonical lift of the inverse downstairs. -/
@[simp]
theorem basedLiftDiffeomorph_symm_apply (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e : X ≃ₘ^n⟮IX, IX⟯ X) (e₀ z : E)
    (hfix : e (p e₀) = p e₀) (hfixSymm : e.symm (p e₀) = p e₀)
    (hpres : hp.PreservesRecoveredSubgroup e e.continuous e₀ hfix)
    (hpresSymm : hp.PreservesRecoveredSubgroup e.symm e.symm.continuous e₀ hfixSymm) :
    (hp.basedLiftDiffeomorph e e₀ hfix hfixSymm hpres hpresSymm).symm z =
      hp.basedLift e.symm e.symm.contMDiff e₀ hfixSymm hpresSymm z :=
  rfl

end SmoothCover

end SplittingSpheres
