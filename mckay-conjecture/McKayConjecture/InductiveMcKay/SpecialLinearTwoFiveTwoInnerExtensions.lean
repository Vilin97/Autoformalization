/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalar
import McKayConjecture.Character.SurjectiveActionSemidirectExtension
import McKayConjecture.InductiveMcKay.InnerCharacterStabilizer
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoTrivialProjectiveRow

/-!
# Inner-stabilizer extensions for the `p = 2` degree-three rows

The diagonal outer automorphism swaps the two ambient degree-three
characters.  Their stabilizers therefore consist exactly of inner
automorphisms induced by the binary-tetrahedral Sylow normalizer.  Both the
ambient degree-three characters and their matched normalizer linear
characters kill the central kernel of this cover, producing honest
extensions to the two full character-stabilizer semidirect products.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeTwoForInnerExtensions :
    Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The two degree-three rows of the ambient odd-degree table. -/
def specialLinearTwoFiveTwoSymmetricSquarePPrimeRow
    (k : Fin 2) :
    SpecialLinearTwoFivePPrimeCharacterRow 2 :=
  ⟨.symmetricSquare k, by
    simp [specialLinearTwoFiveCharacterRowDegree]⟩

/-- The outer row permutation has no fixed point on the two degree-three
rows. -/
theorem specialLinearTwoFiveTwoOuter_symmetricSquare_ne
    (k : Fin 2) :
    specialLinearTwoFiveTwoOuterPPrimeRow
        (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k) ≠
      specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k := by
  intro h
  have hk := congrArg (fun r ↦ r.1) h
  fin_cases k <;> contradiction

/-- Every automorphism stabilizing either degree-three character is inner by
an element of the exact Sylow-two normalizer. -/
theorem specialLinearTwoFiveTwo_innerCharacterStabilizer_surjective
    (k : Fin 2) :
    Function.Surjective
      (normalizerInnerCharacterStabilizerHom
        specialLinearTwoFiveSylowTwo
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k))) := by
  intro a
  obtain ⟨g, hg | hg⟩ :=
    specialLinearTwoFive_sylowTwoStabilizer_eq_inner_or_outer_inner a.1
  · refine ⟨g, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hg.symm
  · have hfix :
        a.1 •
            specialLinearTwoFiveTwoPPrimeCharacterEquiv
              (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k) =
          specialLinearTwoFiveTwoPPrimeCharacterEquiv
            (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k) :=
      MulAction.mem_stabilizer_iff.mp a.2
    have houter :
        specialLinearTwoFiveTwoPPrimeCharacterEquiv
              (specialLinearTwoFiveTwoOuterPPrimeRow
                (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k)) =
          specialLinearTwoFiveTwoPPrimeCharacterEquiv
            (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k) := by
      calc
        specialLinearTwoFiveTwoPPrimeCharacterEquiv
              (specialLinearTwoFiveTwoOuterPPrimeRow
                (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k)) =
            specialLinearTwoFiveDiagonalOuterAutomorphism •
              specialLinearTwoFiveTwoPPrimeCharacterEquiv
                (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k) :=
          (specialLinearTwoFiveDiagonalOuterAutomorphism_smul_pPrimeCharacter
            (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k)).symm
        _ =
            a.1.1 •
              specialLinearTwoFiveTwoPPrimeCharacterEquiv
                (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k) := by
          rw [hg, mul_smul, pPrime_conj_smul]
        _ =
            specialLinearTwoFiveTwoPPrimeCharacterEquiv
              (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k) :=
          hfix
    exact (
      (specialLinearTwoFiveTwoOuter_symmetricSquare_ne k)
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv.injective houter)).elim

/-- The center of the concrete binary icosahedral group is exactly
`{1,-1}`. -/
theorem specialLinearTwoFive_center_eq_one_or_neg_one
    (z : Subgroup.center SpecialLinearTwoFive) :
    (z : SpecialLinearTwoFive) = 1 ∨
      (z : SpecialLinearTwoFive) = -1 := by
  revert z
  native_decide

/-- The center of the binary-tetrahedral normalizer is likewise
`{1,-1}` in ambient coordinates. -/
theorem specialLinearTwoFiveTwoNormalizer_center_eq_one_or_neg_one
    (z : Subgroup.center SpecialLinearTwoFiveSylowTwoNormalizer) :
    (z.1 : SpecialLinearTwoFive) = 1 ∨
      (z.1 : SpecialLinearTwoFive) = -1 := by
  revert z
  native_decide

/-- Both ambient degree-three characters are trivial on the center. -/
theorem specialLinearTwoFiveTwoSymmetricSquare_trivialOn_center
    (k : Fin 2) :
    (specialLinearTwoFiveTwoPPrimeCharacterEquiv
      (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k)).1.TrivialOn
        (Subgroup.center SpecialLinearTwoFive) := by
  apply
    (IrreducibleCharacter.trivialOn_iff_values_eq_degree
      _ _ le_rfl).2
  intro z
  rcases specialLinearTwoFive_center_eq_one_or_neg_one z with hz | hz
  · rw [hz]
    exact IrreducibleCharacter.value_one _
  · change
      (specialLinearTwoFiveIrreducibleCharacter
        (.symmetricSquare k)).values z.1 =
          ((specialLinearTwoFiveIrreducibleCharacter
            (.symmetricSquare k)).degree : ℂ)
    rw [specialLinearTwoFiveIrreducibleCharacter_degree]
    rw [hz]
    change
      (specialLinearTwoFiveIrreducibleCharacter
        (.symmetricSquare k)).values
          (specialLinearTwoFiveConjugacyRepresentative 1) = 3
    rw [specialLinearTwoFiveIrreducibleCharacter_values_representative]
    fin_cases k <;>
      norm_num [specialLinearTwoFiveCharacterTableValue,
        binaryIcosahedralSymmetricSquareValue,
        binaryIcosahedralDefiningTrace]

/-- Every matched nontrivial normalizer linear character is trivial on the
normalizer center. -/
theorem specialLinearTwoFiveTwoMatchedLinear_trivialOn_center
    (k : Fin 2) :
    (specialLinearTwoFiveTwoCharacterTableCompletion
      |>.toEquivariantMcKayEquiv
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k))).1.TrivialOn
      (Subgroup.center SpecialLinearTwoFiveSylowTwoNormalizer) := by
  let e :=
    specialLinearTwoFiveTwoCharacterTableCompletion
      |>.toEquivariantMcKayEquiv
  have hmatched :
      (e
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k))).1 =
        specialLinearTwoFiveTwoNormalizerLinearCharacter
          ((k.val + 1 : ℕ) : ZMod 3) := by
    rw [SpecialLinearTwoFiveTwoCharacterTableCompletion.toEquivariantMcKayEquiv_apply_enumerated]
    rfl
  rw [hmatched]
  apply
    (IrreducibleCharacter.trivialOn_iff_values_eq_degree
      _ _ le_rfl).2
  intro z
  rw [specialLinearTwoFiveTwoNormalizerLinearCharacter_degree]
  rw [specialLinearTwoFiveTwoNormalizerLinearCharacter_values]
  have hquotient :
      specialLinearTwoFiveSylowTwoNormalizerCyclicQuotient z.1 = 1 := by
    rcases
        specialLinearTwoFiveTwoNormalizer_center_eq_one_or_neg_one z
      with hz | hz
    · have hz' : z.1 = 1 :=
        Subtype.ext hz
      rw [hz', map_one]
    · revert z
      native_decide
  rw [specialLinearTwoFiveTwoNormalizerLinearHom, MonoidHom.comp_apply,
    hquotient, map_one]
  simp

end InductiveMcKay
end McKayConjecture
