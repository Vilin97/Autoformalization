/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Topology.Homotopy.Isotopy.Basic

/-!
# Ambient isotopies from smooth families of diffeomorphisms

A jointly smooth family of diffeomorphisms of a compact Hausdorff manifold, starting at the
identity, determines an ambient isotopy.  Compactness and the Hausdorff property turn the
continuous bijective total map into a homeomorphism; no joint regularity of the inverse family is
required.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold unitInterval

namespace SplittingSpheres

universe uEM uHM uN

/-- A jointly smooth family of diffeomorphisms of a compact Hausdorff manifold, starting at the
identity, defines an ambient isotopy. -/
def ambientIsotopyOfDiffeomorphismFamily
    {EM : Type uEM} {HM : Type uHM}
    [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
    (JM : ModelWithCorners ℝ EM HM)
    (N : Type uN) [TopologicalSpace N] [ChartedSpace HM N]
    [CompactSpace N] [T2Space N]
    (psi : I → N ≃ₘ^∞⟮JM, JM⟯ N)
    (hpsi : ContMDiff ((𝓡∂ 1).prod JM) JM ∞
      (fun p : I × N ↦ psi p.1 p.2))
    (hzero : ∀ x : N, psi 0 x = x) : TauCeti.AmbientIsotopy N where
  toContinuousMap :=
    ⟨fun p ↦ psi p.1 p.2, hpsi.continuous⟩
  isHomeomorph_total' := by
    rw [isHomeomorph_iff_continuous_bijective]
    refine ⟨continuous_fst.prodMk hpsi.continuous, ?_⟩
    constructor
    · rintro ⟨t, x⟩ ⟨s, y⟩ h
      have hts : t = s := congrArg Prod.fst h
      subst s
      refine Prod.ext rfl ?_
      exact (psi t).injective (congrArg Prod.snd h)
    · rintro ⟨t, y⟩
      exact ⟨⟨t, (psi t).symm y⟩,
        Prod.ext rfl ((psi t).apply_symm_apply y)⟩
  map_zero_left' := hzero

/-- The ambient isotopy evaluates to the given time-slice diffeomorphism. -/
@[simp]
theorem ambientIsotopyOfDiffeomorphismFamily_apply
    {EM : Type uEM} {HM : Type uHM}
    [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
    (JM : ModelWithCorners ℝ EM HM)
    (N : Type uN) [TopologicalSpace N] [ChartedSpace HM N]
    [CompactSpace N] [T2Space N]
    (psi : I → N ≃ₘ^∞⟮JM, JM⟯ N)
    (hpsi : ContMDiff ((𝓡∂ 1).prod JM) JM ∞
      (fun p : I × N ↦ psi p.1 p.2))
    (hzero : ∀ x : N, psi 0 x = x) (p : I × N) :
    (ambientIsotopyOfDiffeomorphismFamily JM N psi hpsi hzero).toContinuousMap p =
      psi p.1 p.2 :=
  rfl

/-- The resulting ambient isotopy has the prescribed identity zero slice. -/
@[simp]
theorem ambientIsotopyOfDiffeomorphismFamily_zero
    {EM : Type uEM} {HM : Type uHM}
    [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
    (JM : ModelWithCorners ℝ EM HM)
    (N : Type uN) [TopologicalSpace N] [ChartedSpace HM N]
    [CompactSpace N] [T2Space N]
    (psi : I → N ≃ₘ^∞⟮JM, JM⟯ N)
    (hpsi : ContMDiff ((𝓡∂ 1).prod JM) JM ∞
      (fun p : I × N ↦ psi p.1 p.2))
    (hzero : ∀ x : N, psi 0 x = x) (x : N) :
    (ambientIsotopyOfDiffeomorphismFamily JM N psi hpsi hzero).toContinuousMap (0, x) = x :=
  hzero x

end SplittingSpheres
