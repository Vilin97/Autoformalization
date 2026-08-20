/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.BudneyGabai.DeltaIndependence

/-!
# Abstract detection by the formal delta normal forms

This file isolates the exact algebraic interface which a future geometric invariant must satisfy.
For a group-valued family `delta`, the data consists of a homomorphism to the multiplicative copy
of the free abelian symbol group whose value on `delta n` is the already computed formal normal
form.  Linear independence of those normal forms then detects every `delta n`, distinguishes all
members of the family, and detects every pairwise quotient.

No instance of this interface is constructed here.  In particular, this file does not define
`W3`, prove invariance of a geometric construction, realize a formal sum by a diffeomorphism, or
identify a mapping-class quotient.  Those are precisely the geometric inputs needed before these
conditional algebraic consequences can be applied to the splitting-sphere detector.
-/

@[expose] public section

open Function

namespace SplittingSpheres

universe u

/-- A group family together with a homomorphism detecting its values as the explicit formal
delta normal forms.  This is an interface for a future geometric invariant, not a construction
of such an invariant. -/
structure BudneyGabaiDeltaDetectionData (G : Type u) [Group G] where
  /-- The group-valued family to be detected. -/
  delta : ℕ → G
  /-- A multiplicative homomorphism to the additive formal-symbol group. -/
  detector : G →* Multiplicative BudneyGabaiSymbolGroup
  /-- Exact value of the detector on every member of the family. -/
  detector_delta : ∀ n,
    Multiplicative.toAdd (detector (delta n)) = budneyGabaiDeltaFamily n

namespace BudneyGabaiDeltaDetectionData

variable {G : Type u} [Group G] (D : BudneyGabaiDeltaDetectionData G)

/-- Exact formal delta values force the detected group family to be injective. -/
theorem injective_delta : Injective D.delta := by
  intro i j hij
  apply injective_budneyGabaiDeltaFamily
  calc
    budneyGabaiDeltaFamily i =
        Multiplicative.toAdd (D.detector (D.delta i)) :=
      (D.detector_delta i).symm
    _ = Multiplicative.toAdd (D.detector (D.delta j)) := by rw [hij]
    _ = budneyGabaiDeltaFamily j := D.detector_delta j

/-- Every detected family member is nontrivial. -/
theorem delta_ne_one (n : ℕ) : D.delta n ≠ 1 := by
  intro hn
  have hdetector := D.detector_delta n
  rw [hn, map_one] at hdetector
  exact budneyGabaiDeltaFamily_ne_zero n hdetector.symm

/-- Distinct indices give distinct detected group elements. -/
theorem pairwise_ne_delta : Pairwise fun i j => D.delta i ≠ D.delta j :=
  D.injective_delta.pairwise_ne

/-- The quotient of two distinctly indexed detected elements is nontrivial. -/
theorem delta_div_ne_one {i j : ℕ} (hij : i ≠ j) :
    D.delta i / D.delta j ≠ 1 :=
  div_ne_one.mpr (D.injective_delta.ne hij)

/-- Every pairwise quotient in the detected family is nontrivial. -/
theorem pairwise_delta_div_ne_one :
    Pairwise fun i j => D.delta i / D.delta j ≠ 1 :=
  fun _ _ hij => D.delta_div_ne_one hij

end BudneyGabaiDeltaDetectionData

end SplittingSpheres
