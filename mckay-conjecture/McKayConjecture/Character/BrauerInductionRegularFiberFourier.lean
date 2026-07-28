/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionRegularFiber
import McKayConjecture.Character.ClassFunctionInductionPairing
import McKayConjecture.Character.ElementaryBrauerInductionReduction
import McKayConjecture.GroupTheory.FiniteDualOrthogonality

/-!
# Fourier expansion of the regular-fibre function

On an elementary product `D × P`, multiplying the indicator of one
`D`-coordinate by `|D|` gives the sum of all complex linear characters of
`D`, weighted by their value at the inverse of that coordinate.  Transporting
those characters across the elementary decomposition gives an explicit
Fourier expansion of Bernstein's regular-fibre class function.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {p : ℕ}
variable {E : Type} [Group E]

/-- A concrete finite enumeration of the complex dual of the cyclic factor.
It is defined explicitly so statements using the sum do not carry a
redundant `Fintype` hypothesis. -/
noncomputable def cyclicFactorDual
    [Finite E] (D : PElementaryDecomposition p E) :
    Finset (D.cyclicPart →* ℂˣ) := by
  letI : IsCyclic D.cyclicPart := D.cyclic
  letI : CommGroup D.cyclicPart :=
    IsCyclic.commGroup
  letI : Fintype (D.cyclicPart →* ℂˣ) :=
    Fintype.ofFinite _
  exact Finset.univ

/-- Inflate a complex linear character of the cyclic factor across the
elementary direct product and transport it to the elementary group. -/
def regularFiberLinearCharacter
    (D : PElementaryDecomposition p E)
    (lam : D.cyclicPart →* ℂˣ) :
    IrreducibleCharacter E :=
  IrreducibleCharacter.linear
    (lam.comp
      ((MonoidHom.fst D.cyclicPart D.pPart).comp
        D.multiplicationEquiv.symm.toMonoidHom))

@[simp]
theorem regularFiberLinearCharacter_values
    (D : PElementaryDecomposition p E)
    (lam : D.cyclicPart →* ℂˣ) (x : E) :
    (regularFiberLinearCharacter D lam).values x =
      (lam (D.multiplicationEquiv.symm x).1 : ℂ) := by
  simp [regularFiberLinearCharacter]

/-- The finite Fourier expansion of the regular-fibre class function.
The scalar coefficients are roots of unity; placing them in a common
cyclotomic coefficient ring is the remaining arithmetic bookkeeping in
the cyclotomic-descent route. -/
theorem regularFiber_card_eq_sum_linearCharacters
    [Finite E]
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart) :
    regularFiber D a (Nat.card D.cyclicPart) =
      ∑ lam ∈ cyclicFactorDual D,
        (lam a⁻¹ : ℂ) •
          (regularFiberLinearCharacter D lam).toClassFunction := by
  classical
  letI : IsCyclic D.cyclicPart := D.cyclic
  letI : CommGroup D.cyclicPart :=
    IsCyclic.commGroup
  letI : Fintype (D.cyclicPart →* ℂˣ) :=
    Fintype.ofFinite _
  apply ClassFunction.ext
  intro x
  let d : D.cyclicPart :=
    (D.multiplicationEquiv.symm x).1
  have hweighted :
      (∑ lam : D.cyclicPart →* ℂˣ,
          (lam a⁻¹ : ℂ) * (lam d : ℂ)) =
        if d = a
        then (Nat.card D.cyclicPart : ℂ)
        else 0 := by
    have hreindex :
        (∑ lam : D.cyclicPart →* ℂˣ,
            (lam a⁻¹ : ℂ) * (lam d : ℂ)) =
          ∑ lam : D.cyclicPart →* ℂˣ,
            (lam (a⁻¹ * d) : ℂ) := by
      apply Finset.sum_congr rfl
      intro lam _hlam
      rw [map_mul, Units.val_mul]
    rw [hreindex]
    by_cases hd : d = a
    · simpa only [hd, inv_mul_cancel, if_pos] using
        sum_complexUnitCharacters_apply_one
          (A := D.cyclicPart)
    · rw [if_neg hd]
      apply sum_complexUnitCharacters_apply_eq_zero
      intro hone
      apply hd
      exact (inv_mul_eq_one.mp hone).symm
  simp only [AddSubmonoidClass.coe_finsetSum,
    Finset.sum_apply, SetLike.val_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [show
      (∑ lam ∈ cyclicFactorDual D,
          (lam a⁻¹ : ℂ) *
            (regularFiberLinearCharacter D lam).toClassFunction x) =
        ∑ lam : D.cyclicPart →* ℂˣ,
          (lam a⁻¹ : ℂ) * (lam d : ℂ) by
      unfold cyclicFactorDual
      apply Finset.sum_congr rfl
      intro lam _hlam
      rw [IrreducibleCharacter.toClassFunction_apply,
        regularFiberLinearCharacter_values]]
  rw [hweighted]
  by_cases hd : d = a
  · rw [if_pos hd]
    apply
      regularFiber_apply_of_cyclicCoordinate_eq
        D a (Nat.card D.cyclicPart) x
    exact hd
  · rw [if_neg hd]
    apply
      regularFiber_apply_of_cyclicCoordinate_ne
        D a (Nat.card D.cyclicPart) x
    exact hd

end ClassFunction

variable {C : Type} [Group C] [Finite C]
variable {p : ℕ} [Fact p.Prime]

/-- Each inflated cyclic-factor character in the Fourier expansion defines
an elementary induction term in the ambient centralizer. -/
def centralPRegularLinearInductionTerm
    (a : C)
    (haCentral : a ∈ Subgroup.center C)
    (haRegular : IsPRegular p a)
    (P : Sylow p C)
    (lam :
      (centralPRegularElementaryDecomposition
        a haCentral haRegular P).cyclicPart →* ℂˣ) :
    ElementaryInductionTerm C where
  prime := p
  prime_isPrime := Fact.out
  subgroup :=
    centralPRegularElementarySubgroup a P
  decomposition :=
    centralPRegularElementaryDecomposition
      a haCentral haRegular P
  character :=
    ClassFunction.regularFiberLinearCharacter
      (centralPRegularElementaryDecomposition
        a haCentral haRegular P)
      lam

namespace ClassFunction

/-- Fourier expansion of the canonical regular-fibre function attached to
a central `p`-regular element. -/
theorem centralPRegularFiber_fourierExpansion
    (a : C)
    (haCentral : a ∈ Subgroup.center C)
    (haRegular : IsPRegular p a)
    (P : Sylow p C) :
    let D :=
      centralPRegularElementaryDecomposition
        a haCentral haRegular P
    let aD :=
      centralPRegularCyclicCoordinate
        a haCentral haRegular P
    centralPRegularFiber a haCentral haRegular P =
      ∑ lam ∈ cyclicFactorDual D,
        (lam aD⁻¹ : ℂ) •
          (regularFiberLinearCharacter D lam).toClassFunction := by
  dsimp only
  exact
    regularFiber_card_eq_sum_linearCharacters
      (centralPRegularElementaryDecomposition
        a haCentral haRegular P)
      (centralPRegularCyclicCoordinate
        a haCentral haRegular P)

/-- Inducing the canonical regular-fibre function gives an explicit
complex linear combination of elementary induced irreducible characters.
The coefficients are precisely the cyclic roots of unity appearing in the
finite Fourier expansion. -/
theorem induce_centralPRegularFiber_eq_sum_inducedLinearCharacters
    (a : C)
    (haCentral : a ∈ Subgroup.center C)
    (haRegular : IsPRegular p a)
    (P : Sylow p C) :
    let S :=
      centralPRegularElementarySubgroup a P
    let D :=
      centralPRegularElementaryDecomposition
        a haCentral haRegular P
    let aD :=
      centralPRegularCyclicCoordinate
        a haCentral haRegular P
    induceLinearMap S
        (centralPRegularFiber
          a haCentral haRegular P) =
      ∑ lam ∈ cyclicFactorDual D,
        (lam aD⁻¹ : ℂ) •
          (centralPRegularLinearInductionTerm
            a haCentral haRegular P lam).inducedClassFunction := by
  dsimp only
  rw [centralPRegularFiber_fourierExpansion]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro lam _hlam
  rw [map_smul]
  rfl

end ClassFunction
end McKayConjecture
