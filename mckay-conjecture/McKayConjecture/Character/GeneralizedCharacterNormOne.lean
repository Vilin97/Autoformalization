/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GeneralizedCharacter
import McKayConjecture.Character.SignedIrreducibilityCriterion
import McKayConjecture.Character.DegreeOneLinear

/-!
# Generalized characters of norm and degree one

In the Dade--Glauberman--Nagao construction one first builds a class
function locally, proves that it is a generalized character, and computes
its norm and value at the identity.  Integral norm one makes the function
a signed irreducible character; value one at the identity chooses the
positive sign and forces degree one.
-/

noncomputable section

namespace McKayConjecture
namespace ClassFunction

variable {G : Type} [Group G] [Finite G]

/-- A generalized character of norm one is a signed irreducible
character. -/
theorem IsGeneralizedCharacter.eq_signedIrreducible_of_norm_one
    {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f)
    (hnorm : normalizedPairing f f = 1) :
    ∃ χ : IrreducibleCharacter G,
      f = χ.toClassFunction ∨
        f = -χ.toClassFunction := by
  obtain ⟨c, rfl⟩ := hf
  have hsqCast :
      (IrreducibleCharacter.integerCoefficientSqSum c : ℂ) =
        ((1 : ℤ) : ℂ) := by
    rw [
      ← IrreducibleCharacter.normalizedPairing_integerCharacterCombination]
    simpa only [Int.cast_one] using hnorm
  have hsq :
      IrreducibleCharacter.integerCoefficientSqSum c = 1 :=
    Int.cast_injective hsqCast
  exact
    IrreducibleCharacter.eq_signedIrreducible_of_integerExpansion_sqSum_eq_one
      (IrreducibleCharacter.integerCharacterCombination c) c rfl hsq

/-- A generalized character with norm one and value one at the identity
is an irreducible character of degree one. -/
theorem IsGeneralizedCharacter.eq_irreducible_of_norm_one_of_value_one
    {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f)
    (hnorm : normalizedPairing f f = 1)
    (hone : f 1 = 1) :
    ∃ χ : IrreducibleCharacter G,
      f = χ.toClassFunction ∧ χ.degree = 1 := by
  obtain ⟨χ, hχ | hχ⟩ :=
    hf.eq_signedIrreducible_of_norm_one hnorm
  · refine ⟨χ, hχ, ?_⟩
    apply Nat.cast_injective (R := ℂ)
    calc
      (χ.degree : ℂ) = χ.toClassFunction 1 := by simp
      _ = f 1 := by rw [hχ]
      _ = 1 := hone
      _ = ((1 : ℕ) : ℂ) := by simp
  · exfalso
    have hvalue :=
      congrArg (fun k : ClassFunction G ↦ k 1) hχ
    have hdegree :
        -(χ.degree : ℂ) = 1 := by
      simpa using hvalue.symm.trans hone
    have hnonnegative :
        0 ≤ (χ.degree : ℝ) :=
      Nat.cast_nonneg χ.degree
    have himpossible :
        -(χ.degree : ℝ) = 1 := by
      exact_mod_cast hdegree
    linarith

/-- Equivalently, the preceding hypotheses recover an actual
multiplicative complex linear character. -/
theorem IsGeneralizedCharacter.eq_linear_of_norm_one_of_value_one
    {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f)
    (hnorm : normalizedPairing f f = 1)
    (hone : f 1 = 1) :
    ∃ lam : G →* ℂˣ,
      f = (IrreducibleCharacter.linear lam).toClassFunction := by
  obtain ⟨χ, hχ, hdegree⟩ :=
    hf.eq_irreducible_of_norm_one_of_value_one hnorm hone
  let lam :=
    IrreducibleCharacter.linearParameterOfDegreeOne χ hdegree
  refine ⟨lam, hχ.trans ?_⟩
  exact
    congrArg IrreducibleCharacter.toClassFunction
      (IrreducibleCharacter.linear_linearParameterOfDegreeOne
        χ hdegree).symm

end ClassFunction
end McKayConjecture
