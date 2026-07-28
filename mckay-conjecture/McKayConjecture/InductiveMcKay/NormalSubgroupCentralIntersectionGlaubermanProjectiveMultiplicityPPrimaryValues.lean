/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.EquivariantMultiplicityMismatchPPrimaryValues
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanProjectiveMultiplicity

/-!
# `q`-primary scalar criteria for the kernel Glauberman mismatch

This file specializes the finite `q`-group coefficient criterion to the
canonical projective multiplicity mismatch on the normal `q'`-kernel.
It is the factor-value route suggested by finite-order projective
operators: it remains to show that the mismatch scalars lie in a finite
group of `q`-power roots of unity.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open CharacterTriple

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- If the kernel mismatch has an actual realization in a finite
commutative `q`-group of scalars, then it is `q`-primary. -/
theorem productGlaubermanKernelProjectiveMultiplicityMismatchIsQPrimary_of_pGroup_coefficients
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q)
    (A : Type) [CommGroup A] [Finite A]
    (hA : IsPGroup q A)
    (c :
      FactorSet
        (ProductGlaubermanKernelCharacterStabilizer
          S C hcentral θ) A)
    (ι : A →* ℂˣ)
    (hfactor :
      productGlaubermanKernelProjectiveMultiplicityFactorSet
          S C hcentral g θ =
        c.map ι) :
    ProductGlaubermanKernelProjectiveMultiplicityMismatchIsQPrimary
      S C hcentral g θ := by
  exact
    EquivariantMultiplicityMismatch.isQPrimary_of_pGroup_coefficients
      (productGlaubermanKernelStabilizerAction
        S C hcentral θ)
      (productGlaubermanFixedPointsStabilizerAction
        S C hcentral θ)
      θ.1.1
      (g.characterEquiv θ).1
      (productGlaubermanKernelCharacter_isInvariant
        S C hcentral θ)
      (productGlaubermanFixedPointCharacter_isInvariant
        S C hcentral g θ)
      q hA c ι hfactor

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
