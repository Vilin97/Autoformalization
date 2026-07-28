/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveGeneralLinearCover
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeOuterActions

/-!
# General-linear invariance of fixed `SL(2, 𝔽₅)` character rows

The only non-inner automorphism class exchanges the two faithful rows and
the two symmetric-square rows.  Every other row is therefore invariant
under conjugation by the full general linear group.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- A row fixed by the displayed outer permutation is invariant under
every automorphism of `SL(2, 𝔽₅)`. -/
theorem specialLinearTwoFive_irreducibleCharacter_invariant_of_outer_fixed
    (r : SpecialLinearTwoFiveCharacterRow)
    (hr : specialLinearTwoFiveOuterCharacterRow r = r)
    (a : MulAut SpecialLinearTwoFive) :
    a • specialLinearTwoFiveIrreducibleCharacter r =
      specialLinearTwoFiveIrreducibleCharacter r := by
  obtain ⟨g, hinner | houter⟩ :=
    specialLinearTwoFive_automorphism_eq_inner_or_outer_inner a
  · rw [hinner, IrreducibleCharacter.conj_smul]
  · rw [houter, mul_smul, IrreducibleCharacter.conj_smul,
      specialLinearTwoFiveOuterAutomorphism_smul_irreducibleCharacter,
      hr]

/-- The corresponding value-level invariance under conjugation by
`GL(2, 𝔽₅)`. -/
theorem
    specialLinearTwoFive_irreducibleCharacter_generalLinear_invariant_of_outer_fixed
    (r : SpecialLinearTwoFiveCharacterRow)
    (hr : specialLinearTwoFiveOuterCharacterRow r = r)
    (u : GeneralLinearTwoFive)
    (g : SpecialLinearTwoFive) :
    (specialLinearTwoFiveIrreducibleCharacter r).values
        (generalLinearTwoFiveConjugation u g) =
      (specialLinearTwoFiveIrreducibleCharacter r).values g := by
  let a := generalLinearTwoFiveConjugation u
  have hfix :
      a • specialLinearTwoFiveIrreducibleCharacter r =
        specialLinearTwoFiveIrreducibleCharacter r :=
    specialLinearTwoFive_irreducibleCharacter_invariant_of_outer_fixed
      r hr a
  have hvalue :=
    congrArg
      (fun ψ : IrreducibleCharacter SpecialLinearTwoFive ↦
        ψ.values (a g)) hfix
  rw [IrreducibleCharacter.smul_values,
    MulEquiv.symm_apply_apply] at hvalue
  exact hvalue.symm

end InductiveMcKay
end McKayConjecture
