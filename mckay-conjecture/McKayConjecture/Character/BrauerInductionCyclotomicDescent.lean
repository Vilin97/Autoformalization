/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import McKayConjecture.Character.BrauerInductionCoefficientLattice

/-!
# Additive cyclotomic descent in Brauer induction

Bernstein's proof first constructs elementary-induction formulas whose
coefficients lie in a cyclotomic integer ring.  It then applies an additive
map from that ring to `ℤ` which sends `1` to `1`.  Multiplicativity of this
map is neither available nor needed: elementary induction is additive and
its irreducible-character coefficient vectors are integral.

This file formalizes that descent at the coefficient-lattice level.  The
generic theorem works for any additive coefficient group equipped with a
distinguished element and an additive retraction.  We then construct the
required retraction explicitly for
`AdjoinRoot (cyclotomic n ℤ)` by taking the constant coordinate in its
power basis.
-/

noncomputable section

namespace McKayConjecture
namespace ClassFunction

open scoped BigOperators

variable {G : Type} [Group G]

/-- Extend an integral irreducible-character coefficient vector to an
additive coefficient group, using `u` as the image of `1`. -/
def coefficientVectorOver
    {R : Type*} [AddCommGroup R]
    (u : R) (v : IrreducibleCharacter G → ℤ) :
    IrreducibleCharacter G → R :=
  fun χ => v χ • u

/-- An elementary coefficient combination with coefficients in an
arbitrary additive group.  The integral entries of each generator act by
integer scalar multiplication. -/
def elementaryCoefficientCombinationOver
    {R : Type*} [AddCommGroup R]
    (c : ElementaryInductionTerm G →₀ R) :
    IrreducibleCharacter G → R :=
  c.sum fun t a χ =>
    elementaryInductionCoefficient t χ • a

@[simp]
theorem elementaryCoefficientCombinationOver_zero
    {R : Type*} [AddCommGroup R] :
    elementaryCoefficientCombinationOver
        (G := G) (0 : ElementaryInductionTerm G →₀ R) =
      0 := by
  rfl

@[simp]
theorem elementaryCoefficientCombinationOver_add
    {R : Type*} [AddCommGroup R]
    (c d : ElementaryInductionTerm G →₀ R) :
    elementaryCoefficientCombinationOver (c + d) =
      elementaryCoefficientCombinationOver c +
        elementaryCoefficientCombinationOver d := by
  classical
  unfold elementaryCoefficientCombinationOver
  rw [Finsupp.sum_add_index']
  · intro t
    ext χ
    simp
  · intro t x y
    ext χ
    simp only [Pi.add_apply, smul_add]

@[simp]
theorem elementaryCoefficientCombinationOver_single
    {R : Type*} [AddCommGroup R]
    (t : ElementaryInductionTerm G) (a : R) :
    elementaryCoefficientCombinationOver
        (Finsupp.single t a) =
      fun χ => elementaryInductionCoefficient t χ • a := by
  classical
  unfold elementaryCoefficientCombinationOver
  rw [Finsupp.sum_single_index]
  ext χ
  simp

theorem elementaryCoefficientCombinationOver_finsetSum
    {R : Type*} [AddCommGroup R]
    {ι : Type*} (s : Finset ι)
    (c : ι → ElementaryInductionTerm G →₀ R) :
    elementaryCoefficientCombinationOver
        (∑ i ∈ s, c i) =
      ∑ i ∈ s, elementaryCoefficientCombinationOver (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi,
        elementaryCoefficientCombinationOver_add, ih]

/-- An integral coefficient vector has an elementary expansion over `R`
when its extension along `1 ↦ u` is an `R`-coefficient combination of the
elementary generators. -/
def HasElementaryCoefficientExpansionOver
    {R : Type*} [AddCommGroup R]
    (u : R) (v : IrreducibleCharacter G → ℤ) : Prop :=
  ∃ c : ElementaryInductionTerm G →₀ R,
    coefficientVectorOver u v =
      elementaryCoefficientCombinationOver c

/-- Applying an additive retraction coefficientwise descends an elementary
expansion back to the integral elementary-induction lattice. -/
theorem mem_elementaryInductionLattice_of_expansionOver
    {R : Type*} [AddCommGroup R]
    (u : R) (ν : R →+ ℤ) (hν : ν u = 1)
    (v : IrreducibleCharacter G → ℤ)
    (hexp : HasElementaryCoefficientExpansionOver
      (G := G) u v) :
    v ∈ elementaryInductionLattice (G := G) := by
  obtain ⟨c, hc⟩ := hexp
  let cℤ : ElementaryInductionTerm G →₀ ℤ :=
    Finsupp.mapRange ν ν.map_zero c
  refine
    (mem_elementaryInductionLattice_iff
      (G := G) v).mpr
      ⟨cℤ, ?_⟩
  funext χ
  have hχ :=
    congrArg ν (congrFun hc χ)
  have hχ' :
      c.sum (fun t a =>
        elementaryInductionCoefficient t χ * ν a) =
        v χ := by
    simpa only [coefficientVectorOver,
      elementaryCoefficientCombinationOver,
      Finsupp.sum_apply', map_finsuppSum,
      map_zsmul, hν, smul_eq_mul, mul_one] using hχ.symm
  rw [elementaryCoefficientLinearMap,
    Finsupp.linearCombination_apply,
    Finsupp.sum_apply']
  change
    cℤ.sum (fun t a =>
      a * elementaryInductionCoefficient t χ) =
      v χ
  dsimp only [cℤ]
  rw [Finsupp.sum_mapRange_index]
  · simpa only [mul_comm] using hχ'
  · intro
    simp

/-- The standard integral model of the `n`-th cyclotomic coefficient
ring. -/
abbrev CyclotomicCoefficientRing (n : ℕ) :=
  AdjoinRoot (Polynomial.cyclotomic n ℤ)

/-- Constant-coordinate projection in the cyclotomic power basis.  This
is the additive map used for descent from cyclotomic coefficients. -/
def cyclotomicCoefficientRetraction
    (n : ℕ) (hn : 0 < n) :
    CyclotomicCoefficientRing n →+ ℤ := by
  let pb :=
    AdjoinRoot.powerBasis'
      (Polynomial.cyclotomic.monic n ℤ)
  let i0 : Fin pb.dim :=
    ⟨0, by
      change 0 < (Polynomial.cyclotomic n ℤ).natDegree
      rw [Polynomial.natDegree_cyclotomic]
      exact Nat.totient_pos.mpr hn⟩
  exact (pb.basis.coord i0).toAddMonoidHom

/-- Constant-coordinate projection sends the unit of the cyclotomic
coefficient ring to `1`. -/
theorem cyclotomicCoefficientRetraction_one
    (n : ℕ) (hn : 0 < n) :
    cyclotomicCoefficientRetraction n hn
        (1 : CyclotomicCoefficientRing n) =
      1 := by
  let pb :=
    AdjoinRoot.powerBasis'
      (Polynomial.cyclotomic.monic n ℤ)
  let i0 : Fin pb.dim :=
    ⟨0, by
      change 0 < (Polynomial.cyclotomic n ℤ).natDegree
      rw [Polynomial.natDegree_cyclotomic]
      exact Nat.totient_pos.mpr hn⟩
  change pb.basis.coord i0 1 = 1
  have hbasis : pb.basis i0 = 1 := by
    rw [pb.basis_eq_pow]
    simp [i0]
  rw [← hbasis]
  change pb.basis.repr (pb.basis i0) i0 = 1
  rw [pb.basis.repr_self, Finsupp.single_eq_same]

/-- A cyclotomic-coefficient elementary expansion of an integral vector
already places that vector in the integral elementary-induction lattice. -/
theorem mem_elementaryInductionLattice_of_cyclotomic_expansion
    (n : ℕ) (hn : 0 < n)
    (v : IrreducibleCharacter G → ℤ)
    (hexp :
      HasElementaryCoefficientExpansionOver
        (G := G)
        (1 : CyclotomicCoefficientRing n) v) :
    v ∈ elementaryInductionLattice (G := G) :=
  mem_elementaryInductionLattice_of_expansionOver
    (1 : CyclotomicCoefficientRing n)
    (cyclotomicCoefficientRetraction n hn)
    (cyclotomicCoefficientRetraction_one n hn)
    v hexp

variable [Finite G]

/-- It is enough to construct cyclotomic elementary expansions for the
irreducible basis vectors.  Additive descent then gives denominator-one
Brauer induction. -/
theorem
    hasElementaryBrauerInduction_of_cyclotomic_basis_expansions
    (n : ℕ) (hn : 0 < n)
    (hexp :
      ∀ χ : IrreducibleCharacter G,
        HasElementaryCoefficientExpansionOver
          (G := G)
          (1 : CyclotomicCoefficientRing n)
          (irreducibleCoefficient χ)) :
    HasElementaryBrauerInduction (G := G) := by
  rw [hasElementaryBrauerInduction_iff_irreducibleCoefficient_mem]
  intro χ
  exact
    mem_elementaryInductionLattice_of_cyclotomic_expansion
      n hn (irreducibleCoefficient χ) (hexp χ)

end ClassFunction
end McKayConjecture
