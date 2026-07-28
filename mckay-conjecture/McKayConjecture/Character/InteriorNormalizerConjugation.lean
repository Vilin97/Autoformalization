/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InteriorAlgebra
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# Conjugation by an interior normalizer

An element normalizing the implementing units of an interior action sends
the fixed algebra to itself by conjugation.  This is the first elementary
step toward the induced normalizer action on the Brauer quotient.
-/

noncomputable section

namespace Representation

variable {k P A : Type}
variable [CommRing k] [Group P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- Conjugation by a unit, oriented as `a ↦ s⁻¹ a s`. -/
def unitConjugationAlgEquiv
    (s : Aˣ) :
    A ≃ₐ[k] A :=
  MulSemiringAction.toAlgEquiv k A
    (ConjAct.toConjAct s⁻¹)

@[simp]
theorem unitConjugationAlgEquiv_apply
    (s : Aˣ) (a : A) :
    unitConjugationAlgEquiv (k := k) s a =
      (↑(s⁻¹) : A) * a * (s : A) :=
  rfl

@[simp]
theorem unitConjugationAlgEquiv_symm :
    (unitConjugationAlgEquiv (k := k) (A := A) s).symm =
      unitConjugationAlgEquiv (k := k) s⁻¹ := by
  apply AlgEquiv.ext
  intro a
  simp [unitConjugationAlgEquiv, ConjAct.units_smul_def,
    mul_assoc]

namespace InteriorAction

variable (I : InteriorAction (P := P) (A := A))

/-- Conjugation by a unit in the interior normalizer preserves the fixed
algebra. -/
theorem unitConjugation_mem_fixedSubalgebra
    (s : I.unitNormalizer)
    (c : fixedSubalgebra (k := k) (P := P) (A := A)) :
    unitConjugationAlgEquiv (k := k) (s : Aˣ) (c : A) ∈
      fixedSubalgebra (k := k) (P := P) (A := A) := by
  intro g
  have hsRange :
      (s : Aˣ) * I.unit g * (s : Aˣ)⁻¹ ∈ I.unitRange :=
    ((Subgroup.mem_normalizer_iff).mp s.property
      (I.unit g)).mp ⟨g, rfl⟩
  obtain ⟨h, hh⟩ := hsRange
  have hhA :
      (I.unit h : A) =
        (s : Aˣ) * I.unit g * (s : Aˣ)⁻¹ := by
    exact congrArg Units.val hh
  have hhInvA :
      (↑((I.unit h)⁻¹) : A) =
        (↑(s : Aˣ) : A) *
          ((↑((I.unit g)⁻¹) : A) *
            (↑((s : Aˣ)⁻¹) : A)) := by
    have hinv := congrArg Inv.inv hh
    simpa only [mul_inv_rev, inv_inv, Units.val_mul] using
      congrArg Units.val hinv
  rw [I.smul_eq]
  change
    (I.unit g : A) *
          ((↑((s : Aˣ)⁻¹) : A) * (c : A) * (s : Aˣ)) *
        (↑((I.unit g)⁻¹) : A) =
      (↑((s : Aˣ)⁻¹) : A) * (c : A) * (s : Aˣ)
  calc
    (I.unit g : A) *
          ((↑((s : Aˣ)⁻¹) : A) * (c : A) * (s : Aˣ)) *
        (↑((I.unit g)⁻¹) : A) =
      (↑((s : Aˣ)⁻¹) : A) *
          (((↑(s : Aˣ) : A) * (I.unit g : A) *
              (↑((s : Aˣ)⁻¹) : A)) *
            (c : A) *
            ((↑(s : Aˣ) : A) *
              ((↑((I.unit g)⁻¹) : A) *
                (↑((s : Aˣ)⁻¹) : A)))) *
        (s : Aˣ) := by
          simp [mul_assoc]
    _ =
      (↑((s : Aˣ)⁻¹) : A) *
          ((I.unit h : A) * (c : A) *
            (↑((I.unit h)⁻¹) : A)) *
        (s : Aˣ) := by
          rw [← hhA, ← hhInvA]
    _ =
      (↑((s : Aˣ)⁻¹) : A) * (c : A) * (s : Aˣ) := by
          rw [← I.smul_eq, c.property h]

/-- Algebra automorphism of the fixed algebra induced by an element of
the interior normalizer. -/
def normalizerConjFixedAlgEquiv
    (s : I.unitNormalizer) :
    fixedSubalgebra (k := k) (P := P) (A := A) ≃ₐ[k]
      fixedSubalgebra (k := k) (P := P) (A := A) where
  toFun c :=
    ⟨unitConjugationAlgEquiv (k := k) (s : Aˣ) c,
      I.unitConjugation_mem_fixedSubalgebra s c⟩
  invFun c :=
    ⟨unitConjugationAlgEquiv (k := k) ((s : Aˣ)⁻¹) c,
      I.unitConjugation_mem_fixedSubalgebra s⁻¹ c⟩
  left_inv c := by
    apply Subtype.ext
    exact
      (unitConjugationAlgEquiv
        (k := k) (s : Aˣ)).left_inv c
  right_inv c := by
    apply Subtype.ext
    exact
      (unitConjugationAlgEquiv
        (k := k) (s : Aˣ)).right_inv c
  map_mul' _ _ := by
    apply Subtype.ext
    exact map_mul _ _ _
  map_add' _ _ := by
    apply Subtype.ext
    exact map_add _ _ _
  commutes' r := by
    apply Subtype.ext
    exact (unitConjugationAlgEquiv
      (k := k) (s : Aˣ)).commutes r

@[simp]
theorem normalizerConjFixedAlgEquiv_apply_coe
    (s : I.unitNormalizer)
    (c : fixedSubalgebra (k := k) (P := P) (A := A)) :
    ((I.normalizerConjFixedAlgEquiv (k := k) s c :
        fixedSubalgebra (k := k) (P := P) (A := A)) : A) =
      (↑(((s : Aˣ)⁻¹)) : A) * (c : A) * (s : Aˣ) :=
  rfl

end InteriorAction
end Representation
