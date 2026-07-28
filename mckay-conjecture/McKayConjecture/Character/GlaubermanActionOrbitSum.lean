/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Automorphism
import McKayConjecture.Character.GlaubermanAction
import McKayConjecture.Character.InductionMultiplicityDegree
import McKayConjecture.Character.OverAlongTransport
import McKayConjecture.Character.PPrimeMultiplicitySum
import McKayConjecture.GroupTheory.PGroupInvariantSum
import McKayConjecture.GroupTheory.PPrimeCore

/-!
# Orbit-sum existence in the Glauberman correspondence

Let a finite `p`-group `P` act on a finite `p'`-group `A`, and write
`C = A^P`.  For an irreducible character `φ` of `C`, the degree of
`Ind_C^A φ` is the sum of

`restrictionMultiplicity(C ↪ A, φ, χ) * χ.degree`

over irreducible characters `χ` of `A`.  The summand is constant on
`P`-orbits.  The weighted fixed-point congruence therefore shows that, if
`φ` has `p'`-degree, some `P`-invariant constituent has both `p'` degree
and `p'` restriction multiplicity.  This supplies the target-to-source
existence half of the numerical Glauberman correspondence without using
the divisibility theorem for irreducible character degrees.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture

open CliffordCorrespondence

variable (P A : Type) [Group P] [Group A]
variable [MulDistribMulAction P A]
variable [Finite P] [Finite A]
variable {p : ℕ} [Fact p.Prime]

/-- The action on irreducible characters induced by the action of `P` on
the group `A`. -/
def actionIrreducibleCharacterMulAction :
    MulAction P (IrreducibleCharacter A) :=
  MulAction.compHom
    (IrreducibleCharacter A)
    (MulDistribMulAction.toMulAut P A)

local instance actionIrreducibleCharacterAction :
    MulAction P (IrreducibleCharacter A) :=
  actionIrreducibleCharacterMulAction P A

@[simp]
theorem actionIrreducibleCharacter_smul_values
    (g : P) (χ : IrreducibleCharacter A) (a : A) :
    (g • χ).values a = χ.values (g⁻¹ • a) :=
  rfl

@[simp]
theorem actionIrreducibleCharacter_smul_degree
    (g : P) (χ : IrreducibleCharacter A) :
    (g • χ).degree = χ.degree :=
  rfl

/-- A fixed point for the induced action on irreducible characters is
exactly a character whose values are invariant under the given action on
`A`. -/
theorem mem_actionIrreducibleCharacter_fixedPoints_iff
    (χ : IrreducibleCharacter A) :
    χ ∈ MulAction.fixedPoints P (IrreducibleCharacter A) ↔
      ∀ g : P, ∀ a : A,
        χ.values (g • a) = χ.values a := by
  constructor
  · intro hχ g a
    have hfixed :=
      congrArg
        (fun η : IrreducibleCharacter A ↦ η.values a)
        (MulAction.mem_fixedPoints.mp hχ g⁻¹)
    simpa using hfixed
  · intro hχ
    apply MulAction.mem_fixedPoints.mpr
    intro g
    apply IrreducibleCharacter.ext
    funext a
    rw [actionIrreducibleCharacter_smul_values]
    exact hχ g⁻¹ a

/-- Restriction to the fixed-point subgroup has the same multiplicity
after acting on the ambient irreducible character. -/
theorem restrictionMultiplicity_actionIrreducibleCharacter
    (g : P)
    (φ : IrreducibleCharacter
      (FixedPoints.subgroup P A))
    (χ : IrreducibleCharacter A) :
    restrictionMultiplicity
        (actionFixedPointsInclusion P A)
        φ (g • χ) =
      restrictionMultiplicity
        (actionFixedPointsInclusion P A)
        φ χ := by
  let eA : A ≃* A :=
    (MulDistribMulAction.toMulAut P A g).symm
  let eC :
      FixedPoints.subgroup P A ≃*
        FixedPoints.subgroup P A :=
    MulEquiv.refl _
  have hcomm :
      eA.toMonoidHom.comp
          (actionFixedPointsInclusion P A) =
        (actionFixedPointsInclusion P A).comp
          eC.toMonoidHom := by
    ext x
    change g⁻¹ • (x : A) = (x : A)
    exact x.2 g⁻¹
  change
    restrictionMultiplicity
        (actionFixedPointsInclusion P A)
        φ
        (χ.comap
          (MulDistribMulAction.toMulEquiv A g).symm) =
      restrictionMultiplicity
        (actionFixedPointsInclusion P A)
        φ χ
  simpa [eA, eC] using
    restrictionMultiplicity_comap_equiv
      eA eC
      (actionFixedPointsInclusion P A)
      (actionFixedPointsInclusion P A)
      hcomm φ χ

/-- The multiplicity-times-degree summand in the induced-character degree
formula is constant on `P`-orbits. -/
theorem restrictionMultiplicity_mul_degree_action_invariant
    (φ : IrreducibleCharacter
      (FixedPoints.subgroup P A))
    (g : P)
    (χ : IrreducibleCharacter A) :
    restrictionMultiplicity
          (actionFixedPointsInclusion P A)
          φ (g • χ) *
        (g • χ).degree =
      restrictionMultiplicity
          (actionFixedPointsInclusion P A)
          φ χ *
        χ.degree := by
  rw [restrictionMultiplicity_actionIrreducibleCharacter,
    actionIrreducibleCharacter_smul_degree]

/-- The degree of `Ind_{A^P}^A φ` is congruent modulo `p` to the
multiplicity-weighted degree sum over invariant irreducible characters. -/
theorem index_mul_degree_modEq_fixed_irreducible_sum
    (hP : IsPGroup p P)
    (φ : IrreducibleCharacter
      (FixedPoints.subgroup P A)) :
    letI := Fintype.ofFinite
      (MulAction.fixedPoints P (IrreducibleCharacter A))
    (FixedPoints.subgroup P A).index * φ.degree ≡
      ∑ χ :
          MulAction.fixedPoints P
            (IrreducibleCharacter A),
        restrictionMultiplicity
            (actionFixedPointsInclusion P A)
            φ χ.1 *
          χ.1.degree [MOD p] := by
  letI : Fintype (IrreducibleCharacter A) :=
    Fintype.ofFinite _
  letI := Fintype.ofFinite
    (MulAction.fixedPoints P (IrreducibleCharacter A))
  let f : IrreducibleCharacter A → ℕ :=
    fun χ ↦
      restrictionMultiplicity
          (actionFixedPointsInclusion P A)
          φ χ *
        χ.degree
  have hmod :=
    PGroupInvariantSum.sum_modEq_sum_fixedPoints
      hP f
      (restrictionMultiplicity_mul_degree_action_invariant
        P A φ)
  have hdegree :=
    index_mul_degree_eq_sum_restrictionMultiplicity_mul_degree_nat
      (FixedPoints.subgroup P A) φ
  change
    (FixedPoints.subgroup P A).index * φ.degree =
      ∑ χ : IrreducibleCharacter A,
        restrictionMultiplicity
            (actionFixedPointsInclusion P A)
            φ χ *
          χ.degree at hdegree
  exact hdegree.symm ▸ hmod

/-- Every `p'`-degree irreducible character of `A^P` lies with
`p'` multiplicity under some `P`-invariant `p'`-degree irreducible
character of `A`. -/
theorem exists_actionInvariantPPrime_of_target
    (hP : IsPGroup p P)
    (hA : GroupTheory.IsPPrimeGroup p A)
    (φ :
      PPrimeIrreducibleCharacter
        (FixedPoints.subgroup P A) p) :
    ∃ θ : ActionInvariantPPrimeIrreducibleCharacter P A p,
      ActionGlaubermanCorrespondence.HasPPrimeRestrictionMultiplicity
        θ φ := by
  classical
  letI : Fintype (IrreducibleCharacter A) :=
    Fintype.ofFinite _
  letI := Fintype.ofFinite
    (MulAction.fixedPoints P (IrreducibleCharacter A))
  let fixedIrr :=
    MulAction.fixedPoints P (IrreducibleCharacter A)
  let multiplicity : fixedIrr → ℕ :=
    fun χ ↦
      restrictionMultiplicity
        (actionFixedPointsInclusion P A)
        φ.1 χ.1
  let degree : fixedIrr → ℕ :=
    fun χ ↦ χ.1.degree
  have hindex :
      ¬p ∣ (FixedPoints.subgroup P A).index := by
    intro hdiv
    have hcard :
        ¬p ∣ Nat.card A :=
      (GroupTheory.isPPrimeGroup_iff_not_dvd
        (Fact.out : p.Prime)).mp hA
    exact hcard
      (hdiv.trans
        (FixedPoints.subgroup P A).index_dvd_card)
  have hleft :
      ¬p ∣
        (FixedPoints.subgroup P A).index *
          φ.1.degree :=
    (not_dvd_mul_iff (Fact.out : p.Prime)).2
      ⟨hindex, φ.2⟩
  have hmod :=
    index_mul_degree_modEq_fixed_irreducible_sum
      P A hP φ.1
  have hfixedSum :
      ¬p ∣ ∑ χ : fixedIrr,
        multiplicity χ * degree χ := by
    intro hdiv
    apply hleft
    apply Nat.modEq_zero_iff_dvd.mp
    exact hmod.trans
      (Nat.modEq_zero_iff_dvd.mpr hdiv)
  obtain ⟨χ, _hχmem, hmult, hdegree⟩ :=
    exists_not_dvd_both_of_not_dvd_sum_mul
      (Fact.out : p.Prime)
      Finset.univ multiplicity degree
      (by simpa using hfixedSum)
  let θ :
      ActionInvariantPPrimeIrreducibleCharacter P A p :=
    ⟨⟨χ.1, hdegree⟩,
      (mem_actionIrreducibleCharacter_fixedPoints_iff
        P A χ.1).mp χ.2⟩
  exact ⟨θ, hmult⟩

end McKayConjecture
