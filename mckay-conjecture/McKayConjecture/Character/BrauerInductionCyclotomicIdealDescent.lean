/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionCyclotomicIdeal
import McKayConjecture.Character.BrauerInductionGlobalCyclotomicExpansion

/-!
# Extracting elementary expansions from the cyclotomic ideal

Because `J_n(G)` was defined as an additive closure, membership yields an
explicit finitely supported family of cyclotomic coefficients on genuine
elementary induced irreducible characters.  This file carries out that
extraction and then converts equality of evaluated class functions into
equality of irreducible coefficient vectors.  The additive cyclotomic
retraction can consequently descend the result to integral Brauer
induction.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture

namespace CyclotomicElementaryInductionDatum

variable {G : Type} [Group G] [Finite G]
variable {n : ℕ} {hn : 0 < n}

/-- A chosen irreducible coefficient family for the local cyclotomic
generalized character. -/
def localCyclotomicCoefficients
    (d : CyclotomicElementaryInductionDatum G n hn) :
    IrreducibleCharacter d.subgroup →
      ClassFunction.CyclotomicCoefficientRing n :=
  Classical.choose d.localCharacter.property.1

/-- The chosen coefficients reconstruct the local class function. -/
theorem local_eq_cyclotomicCharacterCombination
    (d : CyclotomicElementaryInductionDatum G n hn) :
    (d.localCharacter : ClassFunction d.subgroup) =
      ClassFunction.cyclotomicCharacterCombination
        n hn d.localCyclotomicCoefficients :=
  Classical.choose_spec d.localCharacter.property.1

/-- Turn a local irreducible character into the corresponding ambient
elementary induction term. -/
def elementaryTerm
    (d : CyclotomicElementaryInductionDatum G n hn)
    (χ : IrreducibleCharacter d.subgroup) :
    ElementaryInductionTerm G where
  prime := d.prime
  prime_isPrime := d.prime_isPrime
  subgroup := d.subgroup
  decomposition := d.decomposition
  character := χ

/-- Expand a local element of `Q_n(E)` in irreducibles and retain its
coefficients on the resulting ambient elementary induction terms. -/
def elementaryCyclotomicCoefficients
    (d : CyclotomicElementaryInductionDatum G n hn) :
    ElementaryInductionTerm G →₀
      ClassFunction.CyclotomicCoefficientRing n := by
  classical
  letI : Fintype (IrreducibleCharacter d.subgroup) :=
    Fintype.ofFinite _
  exact
    ∑ χ : IrreducibleCharacter d.subgroup,
      Finsupp.single (d.elementaryTerm χ)
        (d.localCyclotomicCoefficients χ)

/-- The explicit elementary coefficients of a generator evaluate to that
generator's induced class function. -/
theorem evaluate_elementaryCyclotomicCoefficients
    (d : CyclotomicElementaryInductionDatum G n hn) :
    ClassFunction.evaluateElementaryInductionCombinationOver
        n hn d.elementaryCyclotomicCoefficients =
      d.induced := by
  classical
  letI : Fintype G := Fintype.ofFinite _
  letI : Fintype (IrreducibleCharacter d.subgroup) :=
    Fintype.ofFinite _
  rw [elementaryCyclotomicCoefficients,
    ClassFunction.evaluateElementaryInductionCombinationOver_finsetSum]
  simp only [
    ClassFunction.evaluateElementaryInductionCombinationOver_single]
  have h :=
    congrArg
      (ClassFunction.induceLinearMap d.subgroup)
      d.local_eq_cyclotomicCharacterCombination
  rw [ClassFunction.cyclotomicCharacterCombination,
    map_sum] at h
  simp only [map_smul,
    ClassFunction.induceLinearMap_apply] at h
  exact h.symm

end CyclotomicElementaryInductionDatum

namespace ClassFunction

variable {G : Type} [Group G] [Finite G]
variable {n : ℕ} {hn : 0 < n}

/-- Evaluation of elementary cyclotomic combinations as an additive
homomorphism. -/
def evaluateElementaryInductionCombinationOverAddHom :
    (ElementaryInductionTerm G →₀
        CyclotomicCoefficientRing n) →+
      ClassFunction G where
  toFun :=
    evaluateElementaryInductionCombinationOver n hn
  map_zero' :=
    evaluateElementaryInductionCombinationOver_zero n hn
  map_add' :=
    evaluateElementaryInductionCombinationOver_add n hn

@[simp]
theorem evaluateElementaryInductionCombinationOverAddHom_apply
    (c : ElementaryInductionTerm G →₀
      CyclotomicCoefficientRing n) :
    evaluateElementaryInductionCombinationOverAddHom
        (G := G) (n := n) (hn := hn) c =
      evaluateElementaryInductionCombinationOver n hn c :=
  rfl

/-- Evaluation of elementary cyclotomic combinations respects negation. -/
theorem evaluateElementaryInductionCombinationOver_neg
    (c : ElementaryInductionTerm G →₀
      CyclotomicCoefficientRing n) :
    evaluateElementaryInductionCombinationOver n hn (-c) =
      -evaluateElementaryInductionCombinationOver n hn c := by
  exact
    map_neg
      (evaluateElementaryInductionCombinationOverAddHom
        (G := G) (n := n) (hn := hn))
      c

/-- Membership in `J_n(G)` supplies an explicit elementary cyclotomic
expansion of the underlying class function. -/
theorem exists_elementaryCyclotomicCoefficients_of_mem_ideal
    (x :
      cyclotomicIntegerCharacterSubring
        (G := G) n hn)
    (hx :
      x ∈
        cyclotomicElementaryInductionIdeal
          (G := G) (n := n) (hn := hn)) :
    ∃ c : ElementaryInductionTerm G →₀
        CyclotomicCoefficientRing n,
      (x : ClassFunction G) =
        evaluateElementaryInductionCombinationOver
          n hn c := by
  change
    x ∈
      AddSubgroup.closure
        (cyclotomicElementaryInductionGeneratorSet
          (G := G) (n := n) (hn := hn)) at hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
      obtain ⟨d, rfl⟩ := hx
      exact
        ⟨d.elementaryCyclotomicCoefficients,
          d.evaluate_elementaryCyclotomicCoefficients.symm⟩
  | zero =>
      exact
        ⟨0, by
          simp only [Subring.coe_zero,
            evaluateElementaryInductionCombinationOver_zero]⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨c, hc⟩ := ihx
      obtain ⟨d, hd⟩ := ihy
      exact
        ⟨c + d, by
          simp only [Subring.coe_add,
            evaluateElementaryInductionCombinationOver_add,
            hc, hd]⟩
  | neg x hx ihx =>
      obtain ⟨c, hc⟩ := ihx
      exact
        ⟨-c, by
          simp only [Subring.coe_neg,
            evaluateElementaryInductionCombinationOver_neg,
            hc]⟩

/-- Equality of an integral character combination with an evaluated
cyclotomic elementary combination gives the corresponding coefficient
expansion inside the integral cyclotomic ring. -/
theorem hasElementaryCoefficientExpansionOver_of_classFunction_eq
    (v : IrreducibleCharacter G → ℤ)
    (c : ElementaryInductionTerm G →₀
      CyclotomicCoefficientRing n)
    (h :
      IrreducibleCharacter.integerCharacterCombination v =
        evaluateElementaryInductionCombinationOver
          n hn c) :
    HasElementaryCoefficientExpansionOver
      (G := G)
      (1 : CyclotomicCoefficientRing n) v := by
  refine ⟨c, ?_⟩
  funext χ
  simp only [coefficientVectorOver,
    elementaryCoefficientCombinationOver,
    Finsupp.sum_apply', zsmul_one]
  apply cyclotomicCoefficientEvaluation_injective n hn
  have hpair :=
    congrArg
      (fun f : ClassFunction G =>
        normalizedPairing f χ.toClassFunction)
      h
  have hinduced :
      ∀ t : ElementaryInductionTerm G,
        normalizedPairing t.inducedClassFunction
            χ.toClassFunction =
          (elementaryInductionCoefficient t χ : ℂ) := by
    intro t
    rw [
      inducedClassFunction_eq_integerCharacterCombination_coefficient,
      IrreducibleCharacter.normalizedPairing_integerCharacterCombination_irreducible]
  simp only [
    IrreducibleCharacter.normalizedPairing_integerCharacterCombination_irreducible,
    evaluateElementaryInductionCombinationOver,
    map_finsuppSum] at hpair
  rw [Finsupp.sum_apply'' _ _ _
    (by simp)
    (by intro f k; simp)] at hpair
  simp only [map_smul, LinearMap.smul_apply,
    hinduced, smul_eq_mul] at hpair
  rw [map_finsuppSum]
  simpa only [map_mul, map_intCast, map_zsmul,
    zsmul_eq_mul, mul_comm] using hpair

/-- If an integral generalized character, bundled in `Q_n(G)`, belongs to
`J_n(G)`, its integral coefficient vector lies in the ordinary elementary
induction lattice. -/
theorem coefficient_mem_elementaryInductionLattice_of_mem_ideal
    (v : IrreducibleCharacter G → ℤ)
    (x :
      cyclotomicIntegerCharacterSubring
        (G := G) n hn)
    (hxclass :
      (x : ClassFunction G) =
        IrreducibleCharacter.integerCharacterCombination v)
    (hx :
      x ∈
        cyclotomicElementaryInductionIdeal
          (G := G) (n := n) (hn := hn)) :
    v ∈ elementaryInductionLattice (G := G) := by
  obtain ⟨c, hc⟩ :=
    exists_elementaryCyclotomicCoefficients_of_mem_ideal
      x hx
  apply
    mem_elementaryInductionLattice_of_cyclotomic_expansion
      n hn v
  exact
    hasElementaryCoefficientExpansionOver_of_classFunction_eq
      v c (hxclass.symm.trans hc)

end ClassFunction
end McKayConjecture
