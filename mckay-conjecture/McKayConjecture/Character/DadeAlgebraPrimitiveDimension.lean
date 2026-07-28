/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraBrauerDimensionCriterion

/-!
# Dimensions of Brauer-primitive Dade algebras

The stable basis of a Dade algebra is a finite `P`-set.  If the algebra is
Brauer-primitive, its distinguished unit is the unique globally fixed basis
index.  The fixed-point congruence for a finite `p`-group therefore makes the
cardinality of the basis, and hence the dimension of the algebra, prime to
`p`.

For an endomorphism algebra this implies that the dimension of the underlying
module is prime to `p`.  This is the elementary rank consequence used for
strongly capped endopermutation modules.
-/

noncomputable section

namespace Representation
namespace DadeAlgebra

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [CharP k p]
variable [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

omit [CharP k p] [Fintype P] [SMulCommClass P k A] in
/-- A Brauer-primitive Dade algebra has dimension prime to the defining
characteristic. -/
theorem not_dvd_finrank_of_isBrauerPrimitive
    (S : DadeAlgebra p k P A)
    (hprimitive : S.IsBrauerPrimitive) :
    ¬p ∣ Module.finrank k A := by
  letI : FiniteDimensional k A :=
    S.finiteDimensional
  letI : Finite S.permutationBasis.index :=
    Module.Finite.finite_basis S.permutationBasis.basis
  letI : Fintype S.permutationBasis.index :=
    Fintype.ofFinite S.permutationBasis.index
  letI : MulAction P S.permutationBasis.index :=
    PointedPermutationAlgebraBasis.indexMulAction
      (B := S.permutationBasis)
  have hfixed :
      Nat.card
          (MulAction.fixedPoints P S.permutationBasis.index) =
        1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact
      ⟨(S.isBrauerPrimitive_iff_subsingleton_fixedIndex).1
          hprimitive,
        ⟨S.permutationBasis.oneFixedIndex⟩⟩
  have hmod :
      Nat.card S.permutationBasis.index ≡ 1 [MOD p] := by
    calc
      Nat.card S.permutationBasis.index ≡
          Nat.card
            (MulAction.fixedPoints P S.permutationBasis.index) [MOD p] :=
        S.isPGroup.card_modEq_card_fixedPoints
          S.permutationBasis.index
      _ = 1 := hfixed
  rw [Module.finrank_eq_card_basis S.permutationBasis.basis]
  rw [← Nat.card_eq_fintype_card]
  intro hdvd
  have hpOne : p ∣ 1 :=
    Nat.modEq_zero_iff_dvd.mp
      (hmod.symm.trans
        (Nat.modEq_zero_iff_dvd.mpr hdvd))
  exact (Fact.out : p.Prime).not_dvd_one hpOne

variable {V : Type}
variable [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V] [Nontrivial V]

omit [CharP k p] [Fintype P] [Nontrivial V] in
/-- If the conjugation Dade algebra on `End(V)` is Brauer-primitive, then
the dimension of `V` is prime to `p`. -/
theorem not_dvd_finrank_of_endomorphism_isBrauerPrimitive
    [MulSemiringAction P (Module.End k V)]
    [SMulCommClass P k (Module.End k V)]
    (S : DadeAlgebra p k P (Module.End k V))
    (hprimitive : S.IsBrauerPrimitive) :
    ¬p ∣ Module.finrank k V := by
  intro hdiv
  apply S.not_dvd_finrank_of_isBrauerPrimitive hprimitive
  rw [Module.finrank_linearMap]
  exact dvd_mul_of_dvd_left hdiv _

end DadeAlgebra
end Representation
