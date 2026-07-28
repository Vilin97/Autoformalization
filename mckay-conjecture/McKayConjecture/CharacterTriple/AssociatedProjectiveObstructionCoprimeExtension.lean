/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedProjectiveObstructionDeterminant
import McKayConjecture.CharacterTriple.AssociatedProjectiveObstructionExponent
import McKayConjecture.CharacterTriple.FactorSetCoprimeClassVanishing
import McKayConjecture.CharacterTriple.ProjectiveObstructionExtension

/-!
# Coprime criteria for automatic extension

The outer quotient order annihilates every factor-set class.  Combining this
with either the conditional determinant bound or the unconditional
association-preserving exponent bound gives two coprime criteria under which
the projective obstruction vanishes.  The intrinsic obstruction-extension
criterion then produces an honest irreducible extension.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

variable {A : Type} [Group A] [Finite A]
variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- If the normal restriction has trivial determinant and the representation
dimension is coprime to the outer quotient order, then the intrinsic
projective obstruction vanishes. -/
theorem projectiveObstructionClass_eq_zero_of_finrank_coprime
    (R : AssociatedProjectiveRepresentation T V P)
    (hdet : R.NormalRestrictionDeterminantIsTrivial)
    (hcoprime :
      Nat.Coprime
        (Module.finrank ℂ V)
        (Nat.card (A ⧸ T.normalSubgroup))) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    T.projectiveObstructionClass = 0 := by
  rw [← R.quotientFactorSet_h2Class_eq_projectiveObstructionClass]
  exact
    R.quotientFactorSet.h2Class_eq_zero_of_coprime
      (Module.finrank ℂ V)
      hcoprime
      (R.finrank_nsmul_quotientFactorSet_h2Class_eq_zero hdet)

/-- Under the determinant-descent hypothesis, coprimality of the
representation dimension and the outer quotient order produces an honest
irreducible extension. -/
theorem exists_extension_of_finrank_coprime
    (R : AssociatedProjectiveRepresentation T V P)
    (hdet : R.NormalRestrictionDeterminantIsTrivial)
    (hcoprime :
      Nat.Coprime
        (Module.finrank ℂ V)
        (Nat.card (A ⧸ T.normalSubgroup))) :
    ∃ psi : IrreducibleCharacter A,
      IrreducibleCharacter.IsExtensionAlong
        T.normalSubgroup.subtype T.character psi := by
  exact
    T.exists_extension_of_projectiveObstructionClass_eq_zero
      (R.projectiveObstructionClass_eq_zero_of_finrank_coprime
        hdet hcoprime)

/-- If the association-preserving factor exponent is coprime to the outer
quotient order, then the intrinsic projective obstruction vanishes. -/
theorem projectiveObstructionClass_eq_zero_of_associatedFactorExponent_coprime
    (R : AssociatedProjectiveRepresentation T V P)
    (hcoprime :
      Nat.Coprime
        (associatedFactorExponent T V)
        (Nat.card (A ⧸ T.normalSubgroup))) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    T.projectiveObstructionClass = 0 := by
  rw [← R.quotientFactorSet_h2Class_eq_projectiveObstructionClass]
  exact
    R.quotientFactorSet.h2Class_eq_zero_of_coprime
      (associatedFactorExponent T V)
      hcoprime
      R.associatedFactorExponent_nsmul_quotientFactorSet_h2Class_eq_zero

/-- Coprimality of the unconditional association-preserving factor exponent
and the outer quotient order produces an honest irreducible extension. -/
theorem exists_extension_of_associatedFactorExponent_coprime
    (R : AssociatedProjectiveRepresentation T V P)
    (hcoprime :
      Nat.Coprime
        (associatedFactorExponent T V)
        (Nat.card (A ⧸ T.normalSubgroup))) :
    ∃ psi : IrreducibleCharacter A,
      IrreducibleCharacter.IsExtensionAlong
        T.normalSubgroup.subtype T.character psi := by
  exact
    T.exists_extension_of_projectiveObstructionClass_eq_zero
      (R.projectiveObstructionClass_eq_zero_of_associatedFactorExponent_coprime
        hcoprime)

end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
