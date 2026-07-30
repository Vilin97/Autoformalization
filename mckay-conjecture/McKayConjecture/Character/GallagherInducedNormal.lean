/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionCosetFormula
import McKayConjecture.Character.GallagherCommutatorFibre

/-!
# Induction of an invariant normal-subgroup character

If an irreducible character `θ` of a normal subgroup `N` is invariant
under the ambient finite group `A`, its induced character vanishes off
`N`.  On `N` it is the quotient order times `θ`.

Substituting this exact value formula into Gallagher's induced
commutator identity gives a division-free count of the commutators that
land in `N`.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace CliffordCorrespondence

variable {A : Type} [Group A] [Finite A]

noncomputable local instance (priority := 2000)
    gallagherInducedNormalGroupFintype
    (G : Type) [Group G] [Finite G] : Fintype G :=
  Fintype.ofFinite G

noncomputable local instance gallagherInducedNormalMembershipDecidable
    {G : Type} [Group G] (H : Subgroup G) :
    DecidablePred (fun g : G => g ∈ H) :=
  Classical.decPred _

/-- Induction from a normal subgroup vanishes outside that subgroup. -/
theorem inducedCharacter_apply_eq_zero_of_not_mem_normal
    (N : Subgroup A) [N.Normal]
    (θ : IrreducibleCharacter N)
    (z : A) (hz : z ∉ N) :
    (FDRep.characterClassFunction
      (FDRep.ind N.subtype θ.realization)) z = 0 := by
  rw [InductionCharacter.ind_characterClassFunction_eq_induce,
    ClassFunction.induce_apply_eq_sum_quotient]
  apply Finset.sum_eq_zero
  intro q _
  apply ClassFunction.inductionTerm_of_not_mem
  intro hconj
  apply hz
  have hrestore :=
    (inferInstance : N.Normal).conj_mem
      (q.out⁻¹ * z * q.out) hconj q.out
  have heq :
      q.out * (q.out⁻¹ * z * q.out) * q.out⁻¹ = z := by
    group
  rw [heq] at hrestore
  exact hrestore

/-- On a normal subgroup, the character induced from an invariant
irreducible character is the quotient order times that character. -/
theorem inducedCharacter_apply_of_mem_normal
    (N : Subgroup A) [N.Normal]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ a : A, a • θ = θ)
    (z : A) (hz : z ∈ N) :
    (FDRep.characterClassFunction
      (FDRep.ind N.subtype θ.realization)) z =
        (Nat.card (A ⧸ N) : ℂ) *
          θ.values ⟨z, hz⟩ := by
  rw [InductionCharacter.ind_characterClassFunction_eq_induce,
    ClassFunction.induce_apply_eq_sum_quotient]
  have hterm (q : A ⧸ N) :
      ClassFunction.inductionTerm
          N θ.realization.characterClassFunction q.out z =
        θ.values ⟨z, hz⟩ := by
    have hmem : q.out⁻¹ * z * q.out ∈ N :=
      (inferInstance : N.Normal).conj_mem' z hz q.out
    rw [ClassFunction.inductionTerm_of_mem N
      θ.realization.characterClassFunction hmem]
    change
      θ.realization.character
          ⟨q.out⁻¹ * z * q.out, hmem⟩ =
        θ.values ⟨z, hz⟩
    rw [θ.realization_character]
    have hinvariantValue :=
      congrArg
        (fun χ : IrreducibleCharacter N =>
          χ.values ⟨z, hz⟩)
        (hinvariant q.out)
    rw [IrreducibleCharacter.conjBy_values] at hinvariantValue
    calc
      θ.values ⟨q.out⁻¹ * z * q.out, hmem⟩ =
          θ.values
            ((MulAut.conjNormal q.out).symm
              (⟨z, hz⟩ : N)) := by
        apply congrArg θ.values
        apply Subtype.ext
        simp only [MulAut.conjNormal_symm_apply]
      _ = θ.values ⟨z, hz⟩ :=
        hinvariantValue
  rw [Finset.sum_congr rfl (fun q _ => hterm q)]
  simp [Finset.card_univ, ← Nat.card_eq_fintype_card,
    nsmul_eq_mul]

/-- Piecewise form of the induced-character value formula for an
invariant irreducible character of a normal subgroup. -/
theorem inducedCharacter_apply_normal
    (N : Subgroup A) [N.Normal]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ a : A, a • θ = θ)
    (z : A) :
    (FDRep.characterClassFunction
      (FDRep.ind N.subtype θ.realization)) z =
        if hz : z ∈ N then
          (Nat.card (A ⧸ N) : ℂ) *
            θ.values ⟨z, hz⟩
        else 0 := by
  by_cases hz : z ∈ N
  · simp only [hz, ↓reduceDIte]
    exact
      inducedCharacter_apply_of_mem_normal
        N θ hinvariant z hz
  · simp only [hz, ↓reduceDIte]
    exact
      inducedCharacter_apply_eq_zero_of_not_mem_normal
        N θ z hz

/-- Direct substitution of the normal-subgroup induced-character value
formula into Gallagher's commutator identity. -/
theorem degree_mul_quotientCard_mul_filteredCommutatorSum
    (N : Subgroup A) [N.Normal]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ a : A, a • θ = θ) :
    (θ.degree : ℂ) *
        (Nat.card (A ⧸ N) : ℂ) *
          (∑ x : A, ∑ y : A,
            if hcomm :
                x⁻¹ * y⁻¹ * x * y ∈ N then
              θ.values
                ⟨x⁻¹ * y⁻¹ * x * y, hcomm⟩
            else 0) =
      (Nat.card A : ℂ) ^ 2 *
        (Nat.card
          (IrreducibleCharactersOverAlong N.subtype θ) : ℂ) := by
  have hmain :=
    degree_mul_sum_inducedCharacter_gallagherCommutator
      N θ hinvariant
  calc
    (θ.degree : ℂ) *
          (Nat.card (A ⧸ N) : ℂ) *
            (∑ x : A, ∑ y : A,
              if hcomm :
                  x⁻¹ * y⁻¹ * x * y ∈ N then
                θ.values
                  ⟨x⁻¹ * y⁻¹ * x * y, hcomm⟩
              else 0) =
        (θ.degree : ℂ) *
          ((Nat.card (A ⧸ N) : ℂ) *
            (∑ x : A, ∑ y : A,
              if hcomm :
                  x⁻¹ * y⁻¹ * x * y ∈ N then
                θ.values
                  ⟨x⁻¹ * y⁻¹ * x * y, hcomm⟩
              else 0)) := by
      ring
    _ =
        (θ.degree : ℂ) *
          ∑ x : A, ∑ y : A,
            (FDRep.characterClassFunction
              (FDRep.ind N.subtype θ.realization))
                (x⁻¹ * y⁻¹ * x * y) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [inducedCharacter_apply_normal N θ hinvariant]
      by_cases hcomm :
          x⁻¹ * y⁻¹ * x * y ∈ N <;>
        simp [hcomm]
    _ =
        (Nat.card A : ℂ) ^ 2 *
          (Nat.card
            (IrreducibleCharactersOverAlong
              N.subtype θ) : ℂ) :=
      hmain

/-- Clean division-free filtered commutator identity.  Only pairs whose
commutator lies in `N` contribute to the sum. -/
theorem degree_mul_filteredCommutatorSum
    (N : Subgroup A) [N.Normal]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ a : A, a • θ = θ) :
    (θ.degree : ℂ) *
        (∑ x : A, ∑ y : A,
          if hcomm :
              x⁻¹ * y⁻¹ * x * y ∈ N then
            θ.values
              ⟨x⁻¹ * y⁻¹ * x * y, hcomm⟩
          else 0) =
      (Nat.card A : ℂ) * (Nat.card N : ℂ) *
        (Nat.card
          (IrreducibleCharactersOverAlong N.subtype θ) : ℂ) := by
  have hquotient :
      (Nat.card (A ⧸ N) : ℂ) ≠ 0 := by
    exact_mod_cast
      (Nat.card_pos : 0 < Nat.card (A ⧸ N)).ne'
  have hcard :
      (Nat.card A : ℂ) =
        (Nat.card (A ⧸ N) : ℂ) *
          (Nat.card N : ℂ) := by
    exact_mod_cast
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
  apply mul_left_cancel₀ hquotient
  calc
    (Nat.card (A ⧸ N) : ℂ) *
          ((θ.degree : ℂ) *
            (∑ x : A, ∑ y : A,
              if hcomm :
                  x⁻¹ * y⁻¹ * x * y ∈ N then
                θ.values
                  ⟨x⁻¹ * y⁻¹ * x * y, hcomm⟩
              else 0)) =
        (θ.degree : ℂ) *
          (Nat.card (A ⧸ N) : ℂ) *
            (∑ x : A, ∑ y : A,
              if hcomm :
                  x⁻¹ * y⁻¹ * x * y ∈ N then
                θ.values
                  ⟨x⁻¹ * y⁻¹ * x * y, hcomm⟩
              else 0) := by
      ring
    _ =
        (Nat.card A : ℂ) ^ 2 *
          (Nat.card
            (IrreducibleCharactersOverAlong
              N.subtype θ) : ℂ) :=
      degree_mul_quotientCard_mul_filteredCommutatorSum
        N θ hinvariant
    _ =
        (Nat.card (A ⧸ N) : ℂ) *
          ((Nat.card A : ℂ) * (Nat.card N : ℂ) *
            (Nat.card
              (IrreducibleCharactersOverAlong
                N.subtype θ) : ℂ)) := by
      rw [hcard]
      ring

end CliffordCorrespondence
end McKayConjecture
