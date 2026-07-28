/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.EquivariantMultiplicityMismatchPGroup
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanProjectiveMultiplicity

/-!
# `q`-group criteria for the kernel Glauberman mismatch

This file specializes the finite-`q`-group pullback criterion to the
canonical projective multiplicity mismatch on the normal `q'`-kernel in
the central-intersection reduction.

It exposes two constructive routes:

* the whole kernel-character stabilizer is a `q`-group; or
* its mismatch factor set factors pointwise through a finite `q`-group.

The second formulation is the useful one for Dade--Glauberman transport.
The actual ambient-normalizer stabilizer need not be a `q`-group, so
finite order of its projective operators by itself only gives an
annihilator equal to the full stabilizer order.
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

/-- If the full ambient-normalizer stabilizer of the selected kernel
character is a `q`-group, finite-group annihilation proves the desired
`q`-primary assertion. -/
theorem productGlaubermanKernelProjectiveMultiplicityMismatchIsQPrimary_of_isPGroup
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q)
    (hstabilizer :
      IsPGroup q
        (ProductGlaubermanKernelCharacterStabilizer
          S C hcentral θ)) :
    ProductGlaubermanKernelProjectiveMultiplicityMismatchIsQPrimary
      S C hcentral g θ := by
  exact
    EquivariantMultiplicityMismatch.isQPrimary_of_isPGroup
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
      q hstabilizer

/-- More generally, an explicit factorization of the kernel mismatch
through any finite `q`-group proves that it is `q`-primary.  The equality
is between actual factor sets, not merely an abstract cohomology class. -/
theorem productGlaubermanKernelProjectiveMultiplicityMismatchIsQPrimary_of_pGroup_factorization
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q)
    (D : Type) [Group D] [Finite D]
    (hD : IsPGroup q D)
    (ρ :
      ProductGlaubermanKernelCharacterStabilizer
          S C hcentral θ →* D)
    (c : FactorSet D ℂˣ)
    (hfactor :
      productGlaubermanKernelProjectiveMultiplicityFactorSet
          S C hcentral g θ =
        c.comap ρ) :
    ProductGlaubermanKernelProjectiveMultiplicityMismatchIsQPrimary
      S C hcentral g θ := by
  exact
    EquivariantMultiplicityMismatch.isQPrimary_of_pGroup_factorization
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
      q hD ρ c hfactor

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
