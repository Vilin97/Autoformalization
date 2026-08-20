/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import SplittingSpheres.Geometry.UnlinkSphereIsotopyPowerComplementTransport

/-!
# Lifting ambient isotopies to the unlink power cover

An ambient isotopy of the base of a covering map has a canonical lift which starts at the
identity of the total space.  The forward lift and the lift of the pointwise inverse ambient
isotopy are inverse at every time: covering-space uniqueness proves this without connectedness
or a chosen basepoint in the total space.  Consequently the level-preserving lifted map is a
homeomorphism and defines an ambient isotopy upstairs.

For the standard unlink power cover, this gives a precise reduction of the conditional ambient
extension used by complement transport.  It is enough to supply an ambient isotopy of the strict
unlink complement which agrees at every time with the normalized sphere isotopy on the initial
equator.  Its canonical lift then agrees, at every time and for every sheet label, with the
existing `standardUnlinkPowerIsotopyLift`.  This file does not assert that such a downstairs
ambient extension exists.
-/

@[expose] public section

noncomputable section

open Function Topology
open scoped unitInterval

namespace SplittingSpheres

namespace IsCoveringMap

open ContinuousMap unitInterval

universe uE uX

variable {E : Type uE} {X : Type uX}
variable [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X}

/-- Evaluate a downstairs ambient isotopy after the covering projection in the space
coordinate. -/
def ambientIsotopyBaseHomotopy (hp : IsCoveringMap p)
    (Φ : TauCeti.AmbientIsotopy X) : C(I × E, X) where
  toFun te := Φ.toContinuousMap (te.1, p te.2)
  continuous_toFun := Φ.continuous.comp
    (continuous_fst.prodMk (hp.continuous.comp continuous_snd))

@[simp]
theorem ambientIsotopyBaseHomotopy_apply (hp : IsCoveringMap p)
    (Φ : TauCeti.AmbientIsotopy X) (te : I × E) :
    ambientIsotopyBaseHomotopy hp Φ te =
      Φ.toContinuousMap (te.1, p te.2) :=
  rfl

/-- The homotopy lift of a downstairs ambient isotopy which starts at the identity on the
covering space. -/
def ambientIsotopyLift (hp : IsCoveringMap p)
    (Φ : TauCeti.AmbientIsotopy X) : C(I × E, E) :=
  hp.liftHomotopy (ambientIsotopyBaseHomotopy hp Φ) (ContinuousMap.id E)
    (fun e ↦ by simp [ambientIsotopyBaseHomotopy])

/-- The lifted homotopy starts at the identity on every point of the covering space. -/
@[simp]
theorem ambientIsotopyLift_zero (hp : IsCoveringMap p)
    (Φ : TauCeti.AmbientIsotopy X) (e : E) :
    ambientIsotopyLift hp Φ (0, e) = e :=
  hp.liftHomotopy_zero (ambientIsotopyBaseHomotopy hp Φ) (ContinuousMap.id E)
    (fun e ↦ by simp [ambientIsotopyBaseHomotopy]) e

/-- Exact full-time projection law for the lifted homotopy. -/
theorem proj_ambientIsotopyLift (hp : IsCoveringMap p)
    (Φ : TauCeti.AmbientIsotopy X) (te : I × E) :
    p (ambientIsotopyLift hp Φ te) =
      Φ.toContinuousMap (te.1, p te.2) :=
  congrFun (hp.liftHomotopy_lifts (ambientIsotopyBaseHomotopy hp Φ)
    (ContinuousMap.id E)
    (fun e ↦ by simp [ambientIsotopyBaseHomotopy])) te

private theorem ambientIsotopyLift_symm_ambientIsotopyLift
    (hp : IsCoveringMap p) (Φ : TauCeti.AmbientIsotopy X) (t : I) (e : E) :
    ambientIsotopyLift hp Φ.symm (t, ambientIsotopyLift hp Φ (t, e)) = e := by
  let g₁ : I → E := fun s ↦
    ambientIsotopyLift hp Φ.symm (s, ambientIsotopyLift hp Φ (s, e))
  let g₂ : I → E := fun _ ↦ e
  have hg₁ : Continuous g₁ := by
    exact (ambientIsotopyLift hp Φ.symm).continuous.comp
      (continuous_id.prodMk ((ambientIsotopyLift hp Φ).continuous.comp
        (continuous_id.prodMk continuous_const)))
  have hg₂ : Continuous g₂ := continuous_const
  have hcomp : p ∘ g₁ = p ∘ g₂ := by
    funext s
    simp only [Function.comp_apply, g₁, g₂]
    rw [proj_ambientIsotopyLift hp Φ.symm
      (s, ambientIsotopyLift hp Φ (s, e))]
    rw [proj_ambientIsotopyLift hp Φ (s, e)]
    rw [← Φ.homeomorph_apply s (p e)]
    rw [← Φ.symm.homeomorph_apply s (Φ.homeomorph s (p e))]
    rw [Φ.homeomorph_symm]
    exact (Φ.homeomorph s).symm_apply_apply (p e)
  have hzero : g₁ 0 = g₂ 0 := by
    simp [g₁, g₂]
  have heq : g₁ = g₂ := hp.eq_of_comp_eq hg₁ hg₂ hcomp 0 hzero
  exact congrFun heq t

private theorem ambientIsotopyLift_ambientIsotopyLift_symm
    (hp : IsCoveringMap p) (Φ : TauCeti.AmbientIsotopy X) (t : I) (e : E) :
    ambientIsotopyLift hp Φ (t, ambientIsotopyLift hp Φ.symm (t, e)) = e := by
  let g₁ : I → E := fun s ↦
    ambientIsotopyLift hp Φ (s, ambientIsotopyLift hp Φ.symm (s, e))
  let g₂ : I → E := fun _ ↦ e
  have hg₁ : Continuous g₁ := by
    exact (ambientIsotopyLift hp Φ).continuous.comp
      (continuous_id.prodMk ((ambientIsotopyLift hp Φ.symm).continuous.comp
        (continuous_id.prodMk continuous_const)))
  have hg₂ : Continuous g₂ := continuous_const
  have hcomp : p ∘ g₁ = p ∘ g₂ := by
    funext s
    simp only [Function.comp_apply, g₁, g₂]
    rw [proj_ambientIsotopyLift hp Φ
      (s, ambientIsotopyLift hp Φ.symm (s, e))]
    rw [proj_ambientIsotopyLift hp Φ.symm (s, e)]
    rw [← Φ.symm.homeomorph_apply s (p e)]
    rw [← Φ.homeomorph_apply s (Φ.symm.homeomorph s (p e))]
    rw [Φ.homeomorph_symm]
    exact (Φ.homeomorph s).apply_symm_apply (p e)
  have hzero : g₁ 0 = g₂ 0 := by
    simp [g₁, g₂]
  have heq : g₁ = g₂ := hp.eq_of_comp_eq hg₁ hg₂ hcomp 0 hzero
  exact congrFun heq t

/-- An ambient isotopy lifts through an arbitrary covering map, starting from the identity on the
total space.  No connectedness, chosen sheet, or fundamental-group preservation hypothesis is
needed. -/
noncomputable def liftAmbientIsotopy (hp : IsCoveringMap p)
    (Φ : TauCeti.AmbientIsotopy X) : TauCeti.AmbientIsotopy E where
  toContinuousMap := ambientIsotopyLift hp Φ
  isHomeomorph_total' := by
    rw [isHomeomorph_iff_exists_inverse]
    refine ⟨continuous_fst.prodMk (ambientIsotopyLift hp Φ).continuous, ?_⟩
    refine ⟨(fun te : I × E ↦ (te.1, ambientIsotopyLift hp Φ.symm te)), ?_, ?_, ?_⟩
    · rintro ⟨t, e⟩
      exact Prod.ext rfl (ambientIsotopyLift_symm_ambientIsotopyLift hp Φ t e)
    · rintro ⟨t, e⟩
      exact Prod.ext rfl (ambientIsotopyLift_ambientIsotopyLift_symm hp Φ t e)
    · exact continuous_fst.prodMk (ambientIsotopyLift hp Φ.symm).continuous
  map_zero_left' := ambientIsotopyLift_zero hp Φ

@[simp]
theorem liftAmbientIsotopy_apply (hp : IsCoveringMap p)
    (Φ : TauCeti.AmbientIsotopy X) (te : I × E) :
    (liftAmbientIsotopy hp Φ).toContinuousMap te = ambientIsotopyLift hp Φ te :=
  rfl

/-- Exact full-time projection law for the lifted ambient isotopy. -/
theorem proj_liftAmbientIsotopy (hp : IsCoveringMap p)
    (Φ : TauCeti.AmbientIsotopy X) (te : I × E) :
    p ((liftAmbientIsotopy hp Φ).toContinuousMap te) =
      Φ.toContinuousMap (te.1, p te.2) :=
  proj_ambientIsotopyLift hp Φ te

end IsCoveringMap

/-! ## The standard unlink power cover -/

open ContinuousMap unitInterval

variable {S : SmoothSphereEmbedding 3 4}

/-- If a downstairs ambient isotopy agrees with the normalized sphere isotopy on the initial
equator at every time, its canonical lift agrees at every time with the existing labelled lift
in the standard unlink power cover. -/
theorem liftAmbientIsotopy_agrees_standardUnlinkPowerIsotopyLift
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier)
    (Φ : TauCeti.AmbientIsotopy StandardUnlinkComplement)
    (hΦ : ∀ t x,
      Φ.toContinuousMap (t, equatorUnlinkComplementMap x) =
        standardUnlinkNormalizedComplementHomotopy H havoid (t, x))
    (t : I) (x : Sphere 3) :
    (IsCoveringMap.liftAmbientIsotopy
      (isCoveringMap_standardUnlinkPowerPullbackProj m) Φ).toContinuousMap
        (t, equatorUnlinkPowerLift m a x) =
      standardUnlinkPowerIsotopyLift m a H havoid (t, x) := by
  let transported : C(I × Sphere 3, StandardUnlinkPowerPullback m) :=
    ⟨fun q ↦
        (IsCoveringMap.liftAmbientIsotopy
          (isCoveringMap_standardUnlinkPowerPullbackProj m) Φ).toContinuousMap
          (q.1, equatorUnlinkPowerLift m a q.2),
      (IsCoveringMap.liftAmbientIsotopy
        (isCoveringMap_standardUnlinkPowerPullbackProj m) Φ).continuous.comp
        (continuous_fst.prodMk
          ((continuous_equatorUnlinkPowerLift m a).comp continuous_snd))⟩
  have htransported : transported =
      (isCoveringMap_standardUnlinkPowerPullbackProj m).liftHomotopy
        (standardUnlinkNormalizedComplementHomotopy H havoid)
        ⟨equatorUnlinkPowerLift m a, continuous_equatorUnlinkPowerLift m a⟩
        (fun x ↦ by
          rw [standardUnlinkNormalizedComplementHomotopy_zero]
          exact (equatorUnlinkPowerLift_proj m a x).symm) := by
    apply ((isCoveringMap_standardUnlinkPowerPullbackProj m).eq_liftHomotopy_iff'
      (H_0 := fun x ↦ by
        rw [standardUnlinkNormalizedComplementHomotopy_zero]
        exact (equatorUnlinkPowerLift_proj m a x).symm) transported).2
    constructor
    · funext q
      change standardUnlinkPowerPullbackProj m
          ((IsCoveringMap.liftAmbientIsotopy
            (isCoveringMap_standardUnlinkPowerPullbackProj m) Φ).toContinuousMap
            (q.1, equatorUnlinkPowerLift m a q.2)) = _
      rw [IsCoveringMap.proj_liftAmbientIsotopy
        (isCoveringMap_standardUnlinkPowerPullbackProj m) Φ
        (q.1, equatorUnlinkPowerLift m a q.2)]
      rw [equatorUnlinkPowerLift_proj]
      exact hΦ q.1 q.2
    · intro y
      change (IsCoveringMap.liftAmbientIsotopy
        (isCoveringMap_standardUnlinkPowerPullbackProj m) Φ).toContinuousMap
          (0, equatorUnlinkPowerLift m a y) = equatorUnlinkPowerLift m a y
      exact IsCoveringMap.ambientIsotopyLift_zero
        (isCoveringMap_standardUnlinkPowerPullbackProj m) Φ _
  change transported (t, x) = standardUnlinkPowerIsotopyLift m a H havoid (t, x)
  exact congrFun (congrArg DFunLike.coe htransported) (t, x)

/-- An explicit ambient extension of the normalized sphere isotopy in the strict unlink
complement produces the conditional ambient-extension witness in every power cover and for every
sheet label.  The input `hΦ` is full-time agreement downstairs; no existence claim is made here. -/
noncomputable def standardUnlinkPowerIsotopyLiftAmbientExtension_of_complementAmbientIsotopy
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier)
    (Φ : TauCeti.AmbientIsotopy StandardUnlinkComplement)
    (hΦ : ∀ t x,
      Φ.toContinuousMap (t, equatorUnlinkComplementMap x) =
        standardUnlinkNormalizedComplementHomotopy H havoid (t, x)) :
    StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid where
  ambientIsotopy :=
    IsCoveringMap.liftAmbientIsotopy
      (isCoveringMap_standardUnlinkPowerPullbackProj m) Φ
  final_agrees x := by
    rw [TauCeti.AmbientIsotopy.final_apply]
    exact liftAmbientIsotopy_agrees_standardUnlinkPowerIsotopyLift
      m a H havoid Φ hΦ 1 x

end SplittingSpheres
