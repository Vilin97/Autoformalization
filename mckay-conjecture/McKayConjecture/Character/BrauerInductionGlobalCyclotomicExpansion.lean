/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionElementaryTransport
import McKayConjecture.Character.BrauerInductionGlobalClassFibers

/-!
# Common-cyclotomic expansions of the global class fibres

Every global Bernstein fibre is a finite linear combination of genuine
elementary induced irreducible characters of the ambient group.  All
coefficients are placed in the single integral cyclotomic ring
`CyclotomicCoefficientRing (Nat.card G)`.

The construction first transports the local elementary induction terms
from the centralizer into `G`, then uses induction transitivity.  Evaluating
the cyclotomic coefficients in `ℂ` recovers the global class fibre
exactly.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {G : Type} [Group G] [Finite G]

/-- Evaluate a finitely supported cyclotomic combination of elementary
induced characters as a complex class function. -/
def evaluateElementaryInductionCombinationOver
    (n : ℕ) (hn : 0 < n)
    (c : ElementaryInductionTerm G →₀
      CyclotomicCoefficientRing n) :
    ClassFunction G :=
  c.sum fun t a =>
    cyclotomicCoefficientEvaluation n hn a •
      t.inducedClassFunction

@[simp]
theorem evaluateElementaryInductionCombinationOver_zero
    (n : ℕ) (hn : 0 < n) :
    evaluateElementaryInductionCombinationOver
        (G := G) n hn 0 =
      0 := by
  rfl

@[simp]
theorem evaluateElementaryInductionCombinationOver_add
    (n : ℕ) (hn : 0 < n)
    (c d : ElementaryInductionTerm G →₀
      CyclotomicCoefficientRing n) :
    evaluateElementaryInductionCombinationOver n hn (c + d) =
      evaluateElementaryInductionCombinationOver n hn c +
        evaluateElementaryInductionCombinationOver n hn d := by
  classical
  unfold evaluateElementaryInductionCombinationOver
  rw [Finsupp.sum_add_index']
  · intro t
    simp
  · intro t x y
    simp only [map_add, add_smul]

@[simp]
theorem evaluateElementaryInductionCombinationOver_single
    (n : ℕ) (hn : 0 < n)
    (t : ElementaryInductionTerm G)
    (a : CyclotomicCoefficientRing n) :
    evaluateElementaryInductionCombinationOver
        n hn (Finsupp.single t a) =
      cyclotomicCoefficientEvaluation n hn a •
        t.inducedClassFunction := by
  classical
  unfold evaluateElementaryInductionCombinationOver
  rw [Finsupp.sum_single_index]
  simp

theorem evaluateElementaryInductionCombinationOver_finsetSum
    (n : ℕ) (hn : 0 < n)
    {ι : Type} (s : Finset ι)
    (c : ι → ElementaryInductionTerm G →₀
      CyclotomicCoefficientRing n) :
    evaluateElementaryInductionCombinationOver
        n hn (∑ i ∈ s, c i) =
      ∑ i ∈ s,
        evaluateElementaryInductionCombinationOver
          n hn (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi,
        evaluateElementaryInductionCombinationOver_add,
        ih]

variable {p : ℕ} [Fact p.Prime]

/-- Common-cyclotomic coefficients of the global fibre indexed by `q`.
The local elementary terms are transported from `C_G(q.representative)`
to the ambient group. -/
def pRegularClassCyclotomicCoefficients
    (q : PRegularConjClasses p G) :
    ElementaryInductionTerm G →₀
      CyclotomicCoefficientRing (Nat.card G) := by
  let a := q.representative
  let C := PRegularCentralizer.group a
  let aC : C := PRegularCentralizer.element a
  let haC : IsPRegular p aC :=
    PRegularCentralizer.element_isPRegular
      p q.representative_isPRegular
  let P : Sylow p C :=
    PRegularCentralizer.sylow p a
  let D :=
    centralPRegularElementaryDecomposition
      aC
      (PRegularCentralizer.element_mem_center a)
      haC P
  let aD :=
    centralPRegularCyclicCoordinate
      aC
      (PRegularCentralizer.element_mem_center a)
      haC P
  let hdiv :
      Nat.card D.cyclicPart ∣ Nat.card G :=
    PRegularCentralizer.cyclicPart_card_dvd_ambient
      p q.representative_isPRegular
  exact
    ∑ lam ∈ cyclicFactorDual D,
      Finsupp.single
        ((centralPRegularLinearInductionTerm
          aC
          (PRegularCentralizer.element_mem_center a)
          haC P lam).mapSubtype C)
        (liftedRegularFiberWeightAt
          (Nat.card G) Nat.card_pos D aD lam hdiv)

/-- Induction transitivity turns the local Fourier formula into an
elementary-character expansion of the ambient class fibre. -/
theorem pRegularClassFiber_fourierExpansion
    (q : PRegularConjClasses p G) :
    let a := q.representative
    let C := PRegularCentralizer.group a
    let aC : C := PRegularCentralizer.element a
    let haC : IsPRegular p aC :=
      PRegularCentralizer.element_isPRegular
        p q.representative_isPRegular
    let P : Sylow p C :=
      PRegularCentralizer.sylow p a
    let D :=
      centralPRegularElementaryDecomposition
        aC
        (PRegularCentralizer.element_mem_center a)
        haC P
    let aD :=
      centralPRegularCyclicCoordinate
        aC
        (PRegularCentralizer.element_mem_center a)
        haC P
    pRegularClassFiber q =
      ∑ lam ∈ cyclicFactorDual D,
        (lam aD⁻¹ : ℂ) •
          ((centralPRegularLinearInductionTerm
            aC
            (PRegularCentralizer.element_mem_center a)
            haC P lam).mapSubtype C).inducedClassFunction := by
  classical
  dsimp only
  let a := q.representative
  let C := PRegularCentralizer.group a
  let aC : C := PRegularCentralizer.element a
  let haC : IsPRegular p aC :=
    PRegularCentralizer.element_isPRegular
      p q.representative_isPRegular
  let P : Sylow p C :=
    PRegularCentralizer.sylow p a
  have hlocal :=
    induce_centralPRegularFiber_eq_sum_inducedLinearCharacters
      aC
      (PRegularCentralizer.element_mem_center a)
      haC P
  have hamb :=
    congrArg
      (induceLinearMap C)
      hlocal
  simp only [map_sum, map_smul,
    induceLinearMap_apply] at hamb
  simp_rw [
    ← ElementaryInductionTerm.mapSubtype_inducedClassFunction
      C] at hamb
  simpa only [pRegularClassFiber,
    centralizerGlobalFiber,
    centralizerLocalFiber,
    induceLinearMap_apply, a, C, aC, haC, P]
    using hamb

/-- Evaluating the ambient cyclotomic coefficient family recovers the
global class fibre exactly. -/
theorem evaluate_pRegularClassCyclotomicCoefficients
    (q : PRegularConjClasses p G) :
    evaluateElementaryInductionCombinationOver
        (Nat.card G) Nat.card_pos
        (pRegularClassCyclotomicCoefficients q) =
      pRegularClassFiber q := by
  classical
  rw [pRegularClassCyclotomicCoefficients,
    evaluateElementaryInductionCombinationOver_finsetSum]
  simp only [
    evaluateElementaryInductionCombinationOver_single,
    evaluate_liftedRegularFiberWeightAt]
  exact (pRegularClassFiber_fourierExpansion q).symm

end ClassFunction
end McKayConjecture
