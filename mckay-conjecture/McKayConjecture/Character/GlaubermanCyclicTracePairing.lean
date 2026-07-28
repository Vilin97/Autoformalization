/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionTransport
import McKayConjecture.Character.GlaubermanCyclicReduction

/-!
# Pairing transport for the cyclic Glauberman trace

The cyclic trace is first constructed on the centralizer of a chosen
generator and then relabelled as a class function on `C_K(P)`.  This file
records that the relabelling preserves its normalized self-pairing.
-/

noncomputable section

namespace McKayConjecture

variable {G : Type} [Group G] [Finite G]
variable (K P : Subgroup G) [K.Normal]
variable [IsCyclic P]
variable {p : ℕ} [Fact p.Prime]

/-- The transported cyclic trace is literally pullback along the canonical
fixed-point group equivalence. -/
theorem cyclicSubgroupGlaubermanTrace_eq_comapLinearEquiv
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    cyclicSubgroupGlaubermanTrace
        K P hK hP hgenerate θ =
      ClassFunction.comapLinearEquiv
        (MulEquiv.subgroupCongr
          (cyclicFixedPoints_cyclicSubgroupGenerator
            K P)).symm
        (determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ) :=
  rfl

/-- Passing from the chosen-generator centralizer to `C_K(P)` preserves
the normalized norm of the cyclic trace. -/
theorem normalizedPairing_cyclicSubgroupGlaubermanTrace
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    ClassFunction.normalizedPairing
        (cyclicSubgroupGlaubermanTrace
          K P hK hP hgenerate θ)
        (cyclicSubgroupGlaubermanTrace
          K P hK hP hgenerate θ) =
      ClassFunction.normalizedPairing
        (determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ)
        (determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ) := by
  rw [cyclicSubgroupGlaubermanTrace_eq_comapLinearEquiv]
  exact
    ClassFunction.normalizedPairing_comapLinearEquiv
      (MulEquiv.subgroupCongr
        (cyclicFixedPoints_cyclicSubgroupGenerator
          K P)).symm
      (determinantNormalizedCyclicTrace
        K P hK hP hgenerate θ)
      (determinantNormalizedCyclicTrace
        K P hK hP hgenerate θ)

end McKayConjecture
