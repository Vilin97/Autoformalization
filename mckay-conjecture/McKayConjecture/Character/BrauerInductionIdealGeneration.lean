/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionCyclotomicIdealDescent
import McKayConjecture.Character.ClassFunctionProjectionFormula

/-!
# Generating all characters from the elementary formula for one

The first step of Bernstein's proof observes that elementary inductions
form an ideal in the ordinary character ring.  Consequently an elementary
formula for the trivial character already implies Brauer induction for
every irreducible character.

This file proves that assertion constructively.  Multiplication of one
elementary induced irreducible by an ambient irreducible is moved inside
induction by the projection formula; the resulting local generalized
character is then expanded in the local irreducible basis.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture

namespace ClassFunction

variable {G : Type} [Group G] [Finite G]

noncomputable local instance brauerIdealGenerationFintypeG :
    Fintype G :=
  Fintype.ofFinite _

/-- The elementary-induction combination, bundled additively. -/
def elementaryInductionCombinationAddHom :
    (ElementaryInductionTerm G →₀ ℤ) →+
      ClassFunction G where
  toFun := elementaryInductionCombination
  map_zero' := by
    classical
    simp [elementaryInductionCombination]
  map_add' c d := by
    classical
    change
      (c + d).sum
          (fun t z => (z : ℂ) • t.inducedClassFunction) =
        c.sum
            (fun t z => (z : ℂ) • t.inducedClassFunction) +
          d.sum
            (fun t z => (z : ℂ) • t.inducedClassFunction)
    rw [Finsupp.sum_add_index']
    · intro t
      simp
    · intro t a b
      simp only [Int.cast_add, add_smul]

@[simp]
theorem elementaryInductionCombinationAddHom_apply
    (c : ElementaryInductionTerm G →₀ ℤ) :
    elementaryInductionCombinationAddHom c =
      elementaryInductionCombination c :=
  rfl

@[simp]
theorem elementaryInductionCombination_zero :
    elementaryInductionCombination
        (0 : ElementaryInductionTerm G →₀ ℤ) =
      0 :=
  map_zero (elementaryInductionCombinationAddHom
    (G := G))

@[simp]
theorem elementaryInductionCombination_add
    (c d : ElementaryInductionTerm G →₀ ℤ) :
    elementaryInductionCombination (c + d) =
      elementaryInductionCombination c +
        elementaryInductionCombination d :=
  map_add (elementaryInductionCombinationAddHom
    (G := G)) c d

@[simp]
theorem elementaryInductionCombination_neg
    (c : ElementaryInductionTerm G →₀ ℤ) :
    elementaryInductionCombination (-c) =
      -elementaryInductionCombination c :=
  map_neg (elementaryInductionCombinationAddHom
    (G := G)) c

@[simp]
theorem elementaryInductionCombination_zsmul
    (z : ℤ)
    (c : ElementaryInductionTerm G →₀ ℤ) :
    elementaryInductionCombination (z • c) =
      z • elementaryInductionCombination c :=
  map_zsmul (elementaryInductionCombinationAddHom
    (G := G)) z c

@[simp]
theorem elementaryInductionCombination_single
    (t : ElementaryInductionTerm G)
    (z : ℤ) :
    elementaryInductionCombination
        (Finsupp.single t z) =
      z • t.inducedClassFunction := by
  classical
  change
    (Finsupp.single t z).sum
        (fun u a => (a : ℂ) • u.inducedClassFunction) =
      z • t.inducedClassFunction
  rw [Finsupp.sum_single_index]
  · exact
      Int.cast_smul_eq_zsmul ℂ z
        t.inducedClassFunction
  · simp

end ClassFunction

namespace ElementaryInductionTerm

variable {G : Type} [Group G] [Finite G]

/-- The local product which appears after applying the projection formula
to an elementary induced character and an ambient irreducible. -/
def localProduct
    (t : ElementaryInductionTerm G)
    (χ : IrreducibleCharacter G) :
    ClassFunction t.subgroup :=
  t.character.toClassFunction *
    ClassFunction.comapLinearMap
      t.subgroup.subtype χ.toClassFunction

/-- The local product is an ordinary generalized character. -/
theorem localProduct_isGeneralizedCharacter
    (t : ElementaryInductionTerm G)
    (χ : IrreducibleCharacter G) :
    ClassFunction.IsGeneralizedCharacter
      (t.localProduct χ) :=
  (ClassFunction.isGeneralizedCharacter_irreducible
      t.character).mul
    (ClassFunction.isGeneralizedCharacter_comap_irreducible
      t.subgroup.subtype χ)

/-- A chosen integral irreducible coefficient vector for the local
product. -/
def localProductCoefficients
    (t : ElementaryInductionTerm G)
    (χ : IrreducibleCharacter G) :
    IrreducibleCharacter t.subgroup → ℤ :=
  Classical.choose
    (t.localProduct_isGeneralizedCharacter χ)

/-- The chosen local coefficients reconstruct the local product. -/
theorem localProduct_eq_integerCharacterCombination
    (t : ElementaryInductionTerm G)
    (χ : IrreducibleCharacter G) :
    t.localProduct χ =
      IrreducibleCharacter.integerCharacterCombination
        (t.localProductCoefficients χ) :=
  Classical.choose_spec
    (t.localProduct_isGeneralizedCharacter χ)

/-- Replace the local irreducible character in an elementary induction
term while retaining its subgroup and displayed decomposition. -/
def withCharacter
    (t : ElementaryInductionTerm G)
    (ψ : IrreducibleCharacter t.subgroup) :
    ElementaryInductionTerm G where
  prime := t.prime
  prime_isPrime := t.prime_isPrime
  subgroup := t.subgroup
  decomposition := t.decomposition
  character := ψ

/-- Elementary terms obtained by expanding the product of one induced
term with an ambient irreducible character. -/
def mulIrreducibleCoefficients
    (t : ElementaryInductionTerm G)
    (χ : IrreducibleCharacter G) :
    ElementaryInductionTerm G →₀ ℤ := by
  classical
  letI : Fintype (IrreducibleCharacter t.subgroup) :=
    Fintype.ofFinite _
  exact
    ∑ ψ : IrreducibleCharacter t.subgroup,
      Finsupp.single (t.withCharacter ψ)
        (t.localProductCoefficients χ ψ)

/-- The expanded elementary terms evaluate to the pointwise product of
the original induced term and the ambient irreducible character. -/
theorem elementaryInductionCombination_mulIrreducibleCoefficients
    (t : ElementaryInductionTerm G)
    (χ : IrreducibleCharacter G) :
    ClassFunction.elementaryInductionCombination
        (t.mulIrreducibleCoefficients χ) =
      t.inducedClassFunction * χ.toClassFunction := by
  classical
  letI : Fintype G := Fintype.ofFinite _
  letI : Fintype (IrreducibleCharacter t.subgroup) :=
    Fintype.ofFinite _
  rw [mulIrreducibleCoefficients]
  change
    ClassFunction.elementaryInductionCombinationAddHom
        (∑ ψ : IrreducibleCharacter t.subgroup,
          Finsupp.single (t.withCharacter ψ)
            (t.localProductCoefficients χ ψ)) =
      _
  rw [map_sum]
  simp only [
    ClassFunction.elementaryInductionCombinationAddHom_apply,
    ClassFunction.elementaryInductionCombination_single]
  have h :=
    congrArg
      (ClassFunction.induceLinearMap t.subgroup)
      (t.localProduct_eq_integerCharacterCombination χ)
  rw [IrreducibleCharacter.integerCharacterCombination,
    map_sum] at h
  simp only [map_smul,
    ClassFunction.induceLinearMap_apply] at h
  simp only [← Int.cast_smul_eq_zsmul ℂ]
  change
    (∑ ψ : IrreducibleCharacter t.subgroup,
        (t.localProductCoefficients χ ψ : ℂ) •
          ClassFunction.induce t.subgroup
            ψ.toClassFunction) =
      ClassFunction.induce t.subgroup
          t.character.toClassFunction *
        χ.toClassFunction
  rw [← ClassFunction.induce_mul_comap
    t.subgroup t.character.toClassFunction
      χ.toClassFunction]
  exact h.symm

end ElementaryInductionTerm

namespace ClassFunction

variable {G : Type} [Group G] [Finite G]

/-- Multiply every term in an elementary-induction combination by an
ambient irreducible, expanding the resulting local generalized
characters. -/
def multiplyElementaryCoefficientsByIrreducible
    (c : ElementaryInductionTerm G →₀ ℤ)
    (χ : IrreducibleCharacter G) :
    ElementaryInductionTerm G →₀ ℤ :=
  c.sum fun t z =>
    z • t.mulIrreducibleCoefficients χ

/-- The coefficient construction above evaluates to pointwise
multiplication by the ambient irreducible. -/
theorem elementaryInductionCombination_multiplyByIrreducible
    (c : ElementaryInductionTerm G →₀ ℤ)
    (χ : IrreducibleCharacter G) :
    elementaryInductionCombination
        (multiplyElementaryCoefficientsByIrreducible c χ) =
      elementaryInductionCombination c *
        χ.toClassFunction := by
  classical
  induction c using Finsupp.induction with
  | zero =>
      simp [multiplyElementaryCoefficientsByIrreducible]
  | @single_add t z c ht hz ih =>
      rw [multiplyElementaryCoefficientsByIrreducible,
        Finsupp.sum_add_index'
          (fun _ => zero_zsmul _)
          (fun _ a b => add_zsmul _ _ _)]
      simp only [Finsupp.sum_single_index,
        zero_zsmul,
        elementaryInductionCombination_add,
        elementaryInductionCombination_zsmul,
        t.elementaryInductionCombination_mulIrreducibleCoefficients,
        elementaryInductionCombination_single,
        add_mul]
      have ih' :
          elementaryInductionCombination
              (c.sum fun u a =>
                a • u.mulIrreducibleCoefficients χ) =
            elementaryInductionCombination c *
              χ.toClassFunction :=
        ih
      rw [ih']
      apply ClassFunction.ext
      intro g
      simp only [add_apply, zsmul_apply, mul_apply,
        zsmul_eq_mul]
      ring

/-- The trivial irreducible character is the constant-one class
function. -/
theorem trivial_toClassFunction_eq_one :
    (IrreducibleCharacter.trivial G).toClassFunction =
      (1 : ClassFunction G) := by
  apply ClassFunction.ext
  intro g
  exact
    IrreducibleCharacter.trivial_values
      (G := G) g

/-- Since elementary inductions form an ideal, membership of the trivial
basis vector in their coefficient lattice implies full Brauer
induction. -/
theorem hasElementaryBrauerInduction_of_trivialCoefficient_mem
    (htrivial :
      irreducibleCoefficient
          (IrreducibleCharacter.trivial G) ∈
        elementaryInductionLattice (G := G)) :
    HasElementaryBrauerInduction (G := G) := by
  obtain ⟨c, hc⟩ :=
    (mem_elementaryInductionLattice_iff
      (G := G)
      (irreducibleCoefficient
        (IrreducibleCharacter.trivial G))).mp
      htrivial
  intro χ
  refine
    ⟨multiplyElementaryCoefficientsByIrreducible
        c χ, ?_⟩
  norm_num only [Int.cast_one, one_smul]
  rw [
    elementaryInductionCombination_multiplyByIrreducible]
  have hcclass :
      elementaryInductionCombination c =
        (1 : ClassFunction G) := by
    rw [
      elementaryInductionCombination_eq_integerCharacterCombination,
      hc,
      integerCharacterCombination_irreducibleCoefficient,
      trivial_toClassFunction_eq_one]
  rw [hcclass, one_mul]

/-- A member of the cyclotomic elementary ideal whose underlying class
function is one implies ordinary denominator-one Brauer induction. -/
theorem hasElementaryBrauerInduction_of_cyclotomicIdeal_member_eq_one
    {n : ℕ} {hn : 0 < n}
    (q :
      cyclotomicIntegerCharacterSubring
        (G := G) n hn)
    (hq :
      q ∈ cyclotomicElementaryInductionIdeal
        (G := G) (n := n) (hn := hn))
    (hqone :
      (q : ClassFunction G) = 1) :
    HasElementaryBrauerInduction (G := G) := by
  apply
    hasElementaryBrauerInduction_of_trivialCoefficient_mem
  apply
    coefficient_mem_elementaryInductionLattice_of_mem_ideal
      (irreducibleCoefficient
        (IrreducibleCharacter.trivial G))
      q
  · rw [hqone,
      integerCharacterCombination_irreducibleCoefficient,
      trivial_toClassFunction_eq_one]
  · exact hq

end ClassFunction
end McKayConjecture
