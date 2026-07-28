/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedRescale
import McKayConjecture.CharacterTriple.CentralProjectiveScalarMismatch

/-!
# Correcting a projective scalar mismatch by a linear character

Suppose two associated projective representations have the same factor set
along a central restriction.  Their scalar discrepancy on the comparison
centralizer is then a linear character.  If that character extends to the
right ambient group, trivially on the distinguished normal subgroup, one
can multiply the right projective lift by the extension.  This preserves
both associatedness and the factor set, and makes the scalar discrepancy
identically one.

This is the abstract projective-representation step used in the
Dade--Glauberman--Nagao construction: the substantive input is extension of
the scalar character, rather than its accidental triviality before the
correction.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple

universe u v

variable {A : Type u} {B : Type v}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
variable {Q : ProjectiveRepresentation ℂ B W}

namespace AssociatedProjectiveRepresentation

/-- Rescaling by a linear character which is trivial on the distinguished
normal subgroup preserves associatedness. -/
def rescaleByNormalTrivialCharacter
    (S : AssociatedProjectiveRepresentation U W Q)
    (χ : B →* ℂˣ)
    (hχ :
      ∀ x : U.normalSubgroup, χ (x : B) = 1) :
    AssociatedProjectiveRepresentation U W
      (Q.rescale χ) :=
  S.rescaleOfNormalTrivialCosetConstant χ hχ
    (fun x b ↦ by
      rw [map_mul, hχ x, one_mul])
    (fun b x ↦ by
      rw [map_mul, hχ x, mul_one])

/-- A character rescaling has zero coboundary, so it does not change the
factor set. -/
@[simp]
theorem rescaleByCharacter_factor
    (Q : ProjectiveRepresentation ℂ B W)
    (χ : B →* ℂˣ)
    (b c : B) :
    (Q.rescale χ).factor b c = Q.factor b c := by
  rw [ProjectiveRepresentation.rescale_factor, map_mul]
  simp

/-- On the comparison centralizer, character rescaling multiplies the
selected right scalar by the value of the character. -/
theorem rightComparisonCentralScalar_rescaleByNormalTrivialCharacter
    (S : AssociatedProjectiveRepresentation U W Q)
    (χ : B →* ℂˣ)
    (hχ :
      ∀ x : U.normalSubgroup, χ (x : B) = 1)
    (centralizer_preimage_le :
      projectiveComparisonCentralizer T e ≤
        Subgroup.centralizer
          (U.normalSubgroup : Set B))
    (b : projectiveComparisonCentralizer T e) :
    (S.rescaleByNormalTrivialCharacter χ hχ
      ).rightComparisonCentralScalar
        centralizer_preimage_le b =
      χ b *
        S.rightComparisonCentralScalar
          centralizer_preimage_le b := by
  apply scalarLinearEquiv_injective ℂ W
  rw [←
    (S.rescaleByNormalTrivialCharacter χ hχ
      ).operator_rightComparisonCentralScalar
        centralizer_preimage_le b]
  rw [ProjectiveRepresentation.rescale_operator,
    S.operator_rightComparisonCentralScalar
      centralizer_preimage_le b,
    scalarLinearEquiv_mul]

/-- Extending the scalar mismatch to the ambient right group, trivially on
the normal subgroup, kills the mismatch after rescaling. -/
theorem comparisonCentralScalarMismatch_rescaleByNormalTrivialCharacter_eq_one
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (centralizer_preimage_le :
      projectiveComparisonCentralizer T e ≤
        Subgroup.centralizer
          (U.normalSubgroup : Set B))
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c)
    (χ : B →* ℂˣ)
    (hχnormal :
      ∀ x : U.normalSubgroup, χ (x : B) = 1)
    (hχrestrict :
      ∀ b : projectiveComparisonCentralizer T e,
        χ b =
          R.comparisonCentralScalarMismatch
            S centralizer_preimage_le factorAgreement b) :
    R.comparisonCentralScalarMismatch
        (S.rescaleByNormalTrivialCharacter χ hχnormal)
        centralizer_preimage_le
        (fun b c ↦ by
          simpa using factorAgreement b c) =
      1 := by
  apply MonoidHom.ext
  intro b
  rw [comparisonCentralScalarMismatch_apply,
    rightComparisonCentralScalar_rescaleByNormalTrivialCharacter]
  rw [hχrestrict,
    comparisonCentralScalarMismatch_apply]
  simp only [div_eq_mul_inv, MonoidHom.one_apply]
  group

end AssociatedProjectiveRepresentation

end CharacterTriple
end McKayConjecture
