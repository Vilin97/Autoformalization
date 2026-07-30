/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordPartition
import McKayConjecture.Character.CyclicExtensionIntertwiner
import McKayConjecture.Character.InductionMultiplicityDegree
import McKayConjecture.Character.RestrictionMultiplicityDegree
import Mathlib.RepresentationTheory.Maschke

/-!
# Character identities for Gallagher's good-class count

This file collects the character-theoretic identities used in Gallagher's
commutator-sum proof of the ordinary good-class counting theorem.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace CliffordCorrespondence

variable {A : Type} [Group A] [Finite A]

noncomputable local instance irreducibleCharactersOverAlongFintype
    {G H : Type} [Group G] [Group H] [Finite G]
    (φ : H →* G) (η : IrreducibleCharacter H) :
    Fintype (IrreducibleCharactersOverAlong φ η) := by
  classical
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  unfold IrreducibleCharactersOverAlong
  infer_instance

/-- If `θ` is invariant under the ambient group, it is the unique
irreducible constituent of an ambient irreducible character lying over
`θ`. -/
theorem eq_of_liesOverAlong_of_invariant
    (N : Subgroup A) [N.Normal]
    (θ η : IrreducibleCharacter N)
    (χ : IrreducibleCharacter A)
    (hinvariant : ∀ a : A, a • θ = θ)
    (hθ : LiesOverAlong N.subtype θ χ)
    (hη : LiesOverAlong N.subtype η χ) :
    η = θ := by
  letI : Fintype A := Fintype.ofFinite A
  obtain ⟨g, hg⟩ :=
    CliffordPartition.exists_conjBy_normalSimpleConstituent_eq
      N χ θ hθ
  obtain ⟨a, ha⟩ :=
    CliffordPartition.exists_conjBy_normalSimpleConstituent_eq
      N χ η hη
  have hcanonical :
      χ.normalSimpleConstituent N = θ := by
    calc
      χ.normalSimpleConstituent N =
          g⁻¹ • (g • χ.normalSimpleConstituent N) := by
            simp
      _ = g⁻¹ • θ := congrArg (fun ξ => g⁻¹ • ξ) hg
      _ = θ := hinvariant g⁻¹
  calc
    η = a • χ.normalSimpleConstituent N := ha.symm
    _ = a • θ := congrArg (fun ξ => a • ξ) hcanonical
    _ = θ := hinvariant a

/-- For an invariant normal-subgroup character, restriction multiplicity
times the normal character degree is the ambient irreducible degree. -/
theorem restrictionMultiplicity_mul_degree_eq_degree_of_invariant
    (N : Subgroup A) [N.Normal]
    (θ : IrreducibleCharacter N)
    (χ : IrreducibleCharacter A)
    (hinvariant : ∀ a : A, a • θ = θ)
    (hχ : LiesOverAlong N.subtype θ χ) :
    restrictionMultiplicity N.subtype θ χ * θ.degree =
      χ.degree := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype (IrreducibleCharacter N) :=
    Fintype.ofFinite _
  rw [degree_eq_sum_restrictionMultiplicity_mul_degree_nat
    N.subtype χ]
  rw [Finset.sum_eq_single θ]
  · intro η _ hη
    have hmultiplicity :
        restrictionMultiplicity N.subtype η χ = 0 := by
      by_contra hne
      have hlies :
          LiesOverAlong N.subtype η χ :=
        Nat.pos_of_ne_zero hne
      exact hη
        (eq_of_liesOverAlong_of_invariant
          N θ η χ hinvariant hχ hlies)
    simp [hmultiplicity]
  · simp

/-- Multiplying the induced character of an invariant normal character by
its degree replaces restriction multiplicities by ambient character
degrees and removes all irreducibles outside the lying-over fibre. -/
theorem degree_smul_inducedCharacter_eq_sum_charactersOver
    (N : Subgroup A) [N.Normal]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ a : A, a • θ = θ) :
    (θ.degree : ℂ) •
        FDRep.characterClassFunction
          (FDRep.ind N.subtype θ.realization) =
      ∑ χ : IrreducibleCharactersOverAlong N.subtype θ,
        (χ.1.degree : ℂ) • χ.1.toClassFunction := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype (IrreducibleCharacter A) :=
    Fintype.ofFinite _
  rw [inducedCharacter_eq_restrictionMultiplicity_sum]
  rw [Finset.smul_sum]
  calc
    (∑ χ : IrreducibleCharacter A,
        (θ.degree : ℂ) •
          ((restrictionMultiplicity N.subtype θ χ : ℂ) •
            χ.toClassFunction)) =
        ∑ χ : IrreducibleCharacter A,
          if LiesOverAlong N.subtype θ χ then
            (χ.degree : ℂ) • χ.toClassFunction
          else 0 := by
      apply Finset.sum_congr rfl
      intro χ _
      by_cases hχ : LiesOverAlong N.subtype θ χ
      · simp only [hχ, ↓reduceIte]
        rw [smul_smul]
        have hdegree :=
          restrictionMultiplicity_mul_degree_eq_degree_of_invariant
            N θ χ hinvariant hχ
        have hdegreeComplex :
            (θ.degree : ℂ) *
                (restrictionMultiplicity N.subtype θ χ : ℂ) =
              (χ.degree : ℂ) := by
          exact_mod_cast
            (show
              θ.degree *
                  restrictionMultiplicity N.subtype θ χ =
                χ.degree by
              rw [mul_comm]
              exact hdegree)
        rw [hdegreeComplex]
      · simp only [hχ, ↓reduceIte]
        have hmultiplicity :
            restrictionMultiplicity N.subtype θ χ = 0 := by
          apply Nat.eq_zero_of_not_pos
          exact hχ
        simp [hmultiplicity]
    _ =
        ∑ χ : IrreducibleCharactersOverAlong N.subtype θ,
          (χ.1.degree : ℂ) • χ.1.toClassFunction := by
      change
        (∑ χ : IrreducibleCharacter A,
            if LiesOverAlong N.subtype θ χ then
              (χ.degree : ℂ) • χ.toClassFunction
            else 0) =
          ∑ χ :
              {χ : IrreducibleCharacter A //
                LiesOverAlong N.subtype θ χ},
            (χ.1.degree : ℂ) • χ.1.toClassFunction
      rw [← Finset.sum_filter]
      exact
        Finset.sum_subtype
          (Finset.univ.filter
            (fun χ : IrreducibleCharacter A =>
              LiesOverAlong N.subtype θ χ))
          (by simp)
          (fun χ : IrreducibleCharacter A =>
            (χ.degree : ℂ) • χ.toClassFunction)

end CliffordCorrespondence

namespace IrreducibleCharacter

variable {A : Type} [Group A] [Finite A]

noncomputable local instance finiteGroupFintype
    (G : Type) [Group G] [Finite G] : Fintype G :=
  Fintype.ofFinite G

/-- The fixed-left-variable identity underlying Gallagher's commutator
sum. -/
theorem degree_mul_sum_gallagherCommutator_fixed_left
    (χ : IrreducibleCharacter A) (x : A) :
    (χ.degree : ℂ) *
        ∑ y : A, χ.values (x⁻¹ * y⁻¹ * x * y) =
      (Nat.card A : ℂ) * χ.values x * χ.values x⁻¹ := by
  classical
  let ρ : Representation ℂ A χ.realization :=
    χ.realization.ρ
  letI : Representation.IsIrreducible ρ :=
    CliffordRestriction.isIrreducible_of_simple
      χ.realization
  let T : Module.End ℂ χ.realization :=
    ∑ y : A, ρ (y⁻¹ * x * y)
  have hTcomm (a : A) :
      ρ a * T = T * ρ a := by
    change
      ρ a * (∑ y : A, ρ (y⁻¹ * x * y)) =
        (∑ y : A, ρ (y⁻¹ * x * y)) * ρ a
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Fintype.sum_equiv (Equiv.mulRight a⁻¹)
    intro y
    simp only [Equiv.coe_mulRight]
    rw [← map_mul, ← map_mul]
    congr 1
    group
  obtain ⟨c, hc⟩ :=
    McKayConjecture.RepresentationTheory.exists_smul_id_of_forall_mul_comm
      ρ T hTcomm
  have htraceρ (g : A) :
      LinearMap.trace ℂ χ.realization (ρ g) =
        χ.values g := by
    change χ.realization.character g = χ.values g
    exact congrFun χ.realization_character g
  have htraceT :
      LinearMap.trace ℂ χ.realization T =
        (Nat.card A : ℂ) * χ.values x := by
    calc
      LinearMap.trace ℂ χ.realization T =
          ∑ y : A,
            LinearMap.trace ℂ χ.realization
              (ρ (y⁻¹ * x * y)) := by
            simp only [T, map_sum]
      _ = ∑ _y : A, χ.values x := by
        apply Finset.sum_congr rfl
        intro y _
        rw [htraceρ]
        change
          χ.toClassFunction (y⁻¹ * x * y) =
            χ.toClassFunction x
        simpa using
          ClassFunction.conj_apply
            χ.toClassFunction x y⁻¹
      _ = (Nat.card A : ℂ) * χ.values x := by
        simp [Finset.card_univ, ← Nat.card_eq_fintype_card,
          nsmul_eq_mul]
  have hcDegree :
      c * (χ.degree : ℂ) =
        (Nat.card A : ℂ) * χ.values x := by
    calc
      c * (χ.degree : ℂ) =
          LinearMap.trace ℂ χ.realization
            (c • (LinearMap.id :
              Module.End ℂ χ.realization)) := by
            simp [χ.realization_finrank]
      _ = LinearMap.trace ℂ χ.realization T := by
        rw [← hc]
      _ = (Nat.card A : ℂ) * χ.values x :=
        htraceT
  have htraceProduct :
      LinearMap.trace ℂ χ.realization (ρ x⁻¹ * T) =
        ∑ y : A,
          χ.values (x⁻¹ * y⁻¹ * x * y) := by
    calc
      LinearMap.trace ℂ χ.realization (ρ x⁻¹ * T) =
          ∑ y : A,
            LinearMap.trace ℂ χ.realization
              (ρ x⁻¹ * ρ (y⁻¹ * x * y)) := by
            simp only [T, Finset.mul_sum, map_sum]
      _ = ∑ y : A,
          χ.values (x⁻¹ * y⁻¹ * x * y) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [← map_mul]
        simpa only [mul_assoc] using
          htraceρ (x⁻¹ * (y⁻¹ * x * y))
  have htraceProductScalar :
      LinearMap.trace ℂ χ.realization (ρ x⁻¹ * T) =
        c * χ.values x⁻¹ := by
    rw [hc]
    change
      LinearMap.trace ℂ χ.realization
          (ρ x⁻¹ *
            (c • (LinearMap.id :
              Module.End ℂ χ.realization))) =
        c * χ.values x⁻¹
    have hmul :
        ρ x⁻¹ *
            (LinearMap.id :
              Module.End ℂ χ.realization) =
          ρ x⁻¹ := by
      ext v
      rfl
    rw [mul_smul_comm, hmul, map_smul, htraceρ]
    rfl
  rw [← htraceProduct, htraceProductScalar]
  calc
    (χ.degree : ℂ) * (c * χ.values x⁻¹) =
        (c * (χ.degree : ℂ)) * χ.values x⁻¹ := by
          ring
    _ = (Nat.card A : ℂ) * χ.values x *
        χ.values x⁻¹ := by
      rw [hcDegree]

/-- Gallagher's global commutator-sum identity for an irreducible
character. -/
theorem degree_mul_sum_gallagherCommutator
    (χ : IrreducibleCharacter A) :
    (χ.degree : ℂ) *
        ∑ x : A, ∑ y : A,
          χ.values (x⁻¹ * y⁻¹ * x * y) =
      (Nat.card A : ℂ) ^ 2 := by
  classical
  have hself :
      ∑ x : A, χ.values x * χ.values x⁻¹ =
        (Nat.card A : ℂ) := by
    have hpair :=
      ClassFunction.normalizedPairing_irreducible_self χ
    change
      (Nat.card A : ℂ)⁻¹ *
          ∑ x : A, χ.values x * χ.values x⁻¹ =
        1 at hpair
    have hcardne : (Nat.card A : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card A).ne'
    field_simp [hcardne] at hpair
    exact hpair
  calc
    (χ.degree : ℂ) *
          ∑ x : A, ∑ y : A,
            χ.values (x⁻¹ * y⁻¹ * x * y) =
        ∑ x : A,
          (χ.degree : ℂ) *
            ∑ y : A,
              χ.values (x⁻¹ * y⁻¹ * x * y) := by
          rw [Finset.mul_sum]
    _ =
        ∑ x : A,
          (Nat.card A : ℂ) * χ.values x *
            χ.values x⁻¹ := by
      apply Finset.sum_congr rfl
      intro x _
      exact degree_mul_sum_gallagherCommutator_fixed_left χ x
    _ =
        (Nat.card A : ℂ) *
          ∑ x : A, χ.values x * χ.values x⁻¹ := by
      rw [Finset.mul_sum]
      simp only [mul_assoc]
    _ = (Nat.card A : ℂ) ^ 2 := by
      rw [hself]
      ring

end IrreducibleCharacter
end McKayConjecture
