/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoRowEquivariance

/-!
# Equivariance certificate for the `p = 2` McKay table of `SL(2, 𝔽₅)`

Every automorphism stabilizing the chosen Sylow-two subgroup is either inner
by an element of its normalizer or the fixed diagonal outer automorphism
followed by such an inner automorphism.  Inner automorphisms fix characters,
and the explicit outer row calculation proves equivariance in the remaining
case.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeTwoForEquivariance :
    Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The exact four-row ordinary character table completion at `p = 2`. -/
def specialLinearTwoFiveTwoCharacterTableCompletion :
    SpecialLinearTwoFiveTwoCharacterTableCompletion where
  indexEquivariance := by
    intro a i
    obtain ⟨g, ha | ha⟩ :=
      specialLinearTwoFive_sylowTwoStabilizer_eq_inner_or_outer_inner a
    · have hamb :
          a • specialLinearTwoFiveTwoPPrimeCharacterEquiv i =
            specialLinearTwoFiveTwoPPrimeCharacterEquiv i := by
        change
          a.1 • specialLinearTwoFiveTwoPPrimeCharacterEquiv i =
            specialLinearTwoFiveTwoPPrimeCharacterEquiv i
        rw [ha]
        exact pPrime_conj_smul 2 g.1 _
      have hrestriction :=
        specialLinearTwoFive_sylowTwoNormalizerRestriction_eq_inner
          a g ha
      have hnorm :
          a •
              specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
                (specialLinearTwoFiveTwoMcKayRowEquiv i) =
            specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
              (specialLinearTwoFiveTwoMcKayRowEquiv i) := by
        change
          (SylowAutStabilizer.normalizerRestrictionHom
              specialLinearTwoFiveSylowTwo a) •
                specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
                  (specialLinearTwoFiveTwoMcKayRowEquiv i) =
            specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
              (specialLinearTwoFiveTwoMcKayRowEquiv i)
        rw [hrestriction]
        exact pPrime_conj_smul 2 g _
      rw [hamb, hnorm]
      simp
    · have hamb :
          a • specialLinearTwoFiveTwoPPrimeCharacterEquiv i =
            specialLinearTwoFiveTwoPPrimeCharacterEquiv
              (specialLinearTwoFiveTwoOuterPPrimeRow i) := by
        change
          a.1 • specialLinearTwoFiveTwoPPrimeCharacterEquiv i =
            specialLinearTwoFiveTwoPPrimeCharacterEquiv
              (specialLinearTwoFiveTwoOuterPPrimeRow i)
        rw [ha, mul_smul, pPrime_conj_smul]
        exact
          specialLinearTwoFiveDiagonalOuterAutomorphism_smul_pPrimeCharacter
            i
      have hrestriction :=
        specialLinearTwoFive_sylowTwoNormalizerRestriction_eq_outer_inner
          a g ha
      have hnorm :
          a •
              specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
                (specialLinearTwoFiveTwoMcKayRowEquiv i) =
            specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
              (specialLinearTwoFiveTwoNormalizerOuterPPrimeRow
                (specialLinearTwoFiveTwoMcKayRowEquiv i)) := by
        change
          (SylowAutStabilizer.normalizerRestrictionHom
              specialLinearTwoFiveSylowTwo a) •
                specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
                  (specialLinearTwoFiveTwoMcKayRowEquiv i) =
            specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
              (specialLinearTwoFiveTwoNormalizerOuterPPrimeRow
                (specialLinearTwoFiveTwoMcKayRowEquiv i))
        rw [hrestriction, mul_smul, pPrime_conj_smul]
        exact
          specialLinearTwoFiveSylowTwoOuterAutomorphism_smul_normalizerPPrime
            (specialLinearTwoFiveTwoMcKayRowEquiv i)
      rw [hamb, hnorm]
      simp only [Equiv.symm_apply_apply]
      exact specialLinearTwoFiveTwoMcKayRowEquiv_outer i

end InductiveMcKay
end McKayConjecture
