/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CoordinateBallSupport

/-!
# The standard coordinate four-ball

This file constructs a concrete inhabitant of `CoordinateFourBall` in Euclidean four-space and
computes its carrier.  It is a small non-vacuity test for the displayed-ball support API: the
abstract carrier definition reduces exactly to the usual closed unit ball in its standard chart.
-/

@[expose] public section

open Function Metric Set TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- The tautological smooth coordinates from the universal open subset of Euclidean four-space. -/
def euclideanUnivDiffeomorph :
    (⊤ : Opens FourSpace) ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ FourSpace :=
  Diffeomorph.mk (Equiv.Set.univ FourSpace) contMDiff_subtype_val (by
    rw [← ContMDiff.subtypeVal_comp_iff (⊤ : Opens FourSpace)]
    convert (contMDiff_id : ContMDiff (𝓡 4) (𝓡 4) ∞
      (id : FourSpace → FourSpace)) using 1
    ext x
    rfl)

/-- The usual closed unit four-ball, displayed in the global Euclidean chart. -/
def standardCoordinateFourBall : CoordinateFourBall FourSpace where
  domain := ⊤
  chart := euclideanUnivDiffeomorph

/-- The abstract displayed-ball carrier is literally the Euclidean closed unit ball in the
standard example. -/
theorem standardCoordinateFourBall_carrier :
    standardCoordinateFourBall.carrier = closedBall (0 : FourSpace) 1 := by
  ext x
  constructor
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    exact hv
  · intro hx
    refine ⟨⟨x, Set.mem_univ x⟩, ?_, rfl⟩
    exact ⟨x, hx, rfl⟩

end SplittingSpheres
