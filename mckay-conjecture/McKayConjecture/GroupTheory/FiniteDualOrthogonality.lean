/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Linear
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Orthogonality for the complex dual of a finite abelian group

The sum of all complex linear characters vanishes at every nonidentity
element.  At the identity it is the order of the group.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture

/-- The sum of all complex unit-valued characters of a finite abelian
group vanishes away from the identity. -/
theorem sum_complexUnitCharacters_apply_eq_zero
    {A : Type} [CommGroup A] [Finite A]
    [Fintype (A →* ℂˣ)]
    {a : A}
    (ha : a ≠ 1) :
    ∑ lam : A →* ℂˣ, (lam a : ℂ) = 0 := by
  classical
  obtain ⟨mu, hmu⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
      A ℂ ha
  let S : ℂ :=
    ∑ lam : A →* ℂˣ, (lam a : ℂ)
  have hshift :
      S =
        ∑ lam : A →* ℂˣ,
          ((mu * lam) a : ℂ) := by
    exact
      (Function.Bijective.sum_comp
        (Equiv.mulLeft mu).bijective
        (fun lam : A →* ℂˣ ↦
          (lam a : ℂ))).symm
  have heq : S = (mu a : ℂ) * S := by
    calc
      S =
          ∑ lam : A →* ℂˣ,
            ((mu * lam) a : ℂ) :=
        hshift
      _ =
          ∑ lam : A →* ℂˣ,
            (mu a : ℂ) * (lam a : ℂ) := by
              simp only [MonoidHom.mul_apply,
                Units.val_mul]
      _ = (mu a : ℂ) * S := by
        exact
          (Finset.mul_sum Finset.univ
            (fun lam : A →* ℂˣ ↦
              (lam a : ℂ))
            (mu a : ℂ)).symm
  have hval : (mu a : ℂ) ≠ 1 := by
    intro h
    apply hmu
    exact Units.ext h
  have hzero :
      (1 - (mu a : ℂ)) * S = 0 := by
    calc
      (1 - (mu a : ℂ)) * S =
          S - (mu a : ℂ) * S := by
            ring
      _ = 0 := sub_eq_zero.mpr heq
  exact
    (mul_eq_zero.mp hzero).resolve_left
      (sub_ne_zero.mpr hval.symm)

/-- At the identity, the sum of all complex unit-valued characters is
the order of the finite abelian group. -/
theorem sum_complexUnitCharacters_apply_one
    {A : Type} [CommGroup A] [Finite A]
    [Fintype (A →* ℂˣ)] :
    ∑ lam : A →* ℂˣ, (lam 1 : ℂ) =
      (Nat.card A : ℂ) := by
  simp only [map_one, Units.val_one,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_univ,
    Fintype.card_eq_nat_card]
  exact_mod_cast
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
      A ℂ

end McKayConjecture
