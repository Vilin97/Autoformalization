/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EquivalenceRestrictionMultiplicity
import McKayConjecture.Character.GlaubermanActionStrong

/-!
# Strong Glauberman correspondence for a trivial action

When the action is trivial, the fixed-point subgroup is canonically the
whole group.  Transport along that equivalence gives the strong
Glauberman correspondence, including uniqueness among all irreducible
target characters.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable (P A : Type) [Group P] [Group A]
variable [MulDistribMulAction P A]
variable [Finite P] [Finite A]
variable {p : ℕ} [Fact p.Prime]

/-- The fixed-point subgroup of a trivial action is canonically the whole
acted-on group. -/
def actionFixedPointsEquivOfTrivial
    (htrivial : ∀ g : P, ∀ a : A, g • a = a) :
    FixedPoints.subgroup P A ≃* A where
  toFun x := x.1
  invFun a := ⟨a, fun g ↦ htrivial g a⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem actionFixedPointsEquivOfTrivial_apply_coe
    (htrivial : ∀ g : P, ∀ a : A, g • a = a)
    (x : FixedPoints.subgroup P A) :
    actionFixedPointsEquivOfTrivial P A htrivial x =
      (x : A) :=
  rfl

/-- The character equivalence for a trivial action. -/
def trivialActionStrongGlaubermanCharacterEquiv
    (htrivial : ∀ g : P, ∀ a : A, g • a = a) :
    ActionInvariantPPrimeIrreducibleCharacter P A p ≃
      PPrimeIrreducibleCharacter
        (FixedPoints.subgroup P A) p where
  toFun θ :=
    IrreducibleCharacter.pPrimeComapEquiv p
      (actionFixedPointsEquivOfTrivial
        P A htrivial) θ.1
  invFun φ :=
    let θ :=
      IrreducibleCharacter.pPrimeComapEquiv p
        (actionFixedPointsEquivOfTrivial
          P A htrivial).symm φ
    ⟨θ, by
      intro g a
      rw [htrivial g a]⟩
  left_inv θ := by
    apply Subtype.ext
    exact
      (IrreducibleCharacter.pPrimeComapEquiv p
        (actionFixedPointsEquivOfTrivial
          P A htrivial)).symm_apply_apply θ.1
  right_inv φ :=
    (IrreducibleCharacter.pPrimeComapEquiv p
      (actionFixedPointsEquivOfTrivial
        P A htrivial)).apply_symm_apply φ

@[simp]
theorem trivialActionStrongGlaubermanCharacterEquiv_apply_coe
    (htrivial : ∀ g : P, ∀ a : A, g • a = a)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p) :
    (trivialActionStrongGlaubermanCharacterEquiv
      P A htrivial θ).1 =
      θ.1.1.comap
        (actionFixedPointsEquivOfTrivial
          P A htrivial) :=
  rfl

/-- The strong action-level Glauberman correspondence for a trivial
action. -/
def strongActionGlaubermanCorrespondenceOfTrivial
    (htrivial : ∀ g : P, ∀ a : A, g • a = a) :
    StrongActionGlaubermanCorrespondence P A p where
  characterEquiv :=
    trivialActionStrongGlaubermanCharacterEquiv
      P A htrivial
  multiplicity_isPPrime := by
    intro θ
    have hinclusion :
        actionFixedPointsInclusion P A =
          (actionFixedPointsEquivOfTrivial
            P A htrivial).toMonoidHom := by
      ext x
      rfl
    rw [hinclusion,
      trivialActionStrongGlaubermanCharacterEquiv_apply_coe,
      restrictionMultiplicity_comap_mulEquiv_eq_one]
    exact (Fact.out : p.Prime).not_dvd_one
  eq_correspondent_of_multiplicity_isPPrime := by
    intro θ φ hφ
    have hinclusion :
        actionFixedPointsInclusion P A =
          (actionFixedPointsEquivOfTrivial
            P A htrivial).toMonoidHom := by
      ext x
      rfl
    by_contra hne
    have hzero :
        restrictionMultiplicity
            (actionFixedPointsInclusion P A)
            φ θ.1.1 =
          0 := by
      rw [hinclusion]
      apply
        restrictionMultiplicity_mulEquiv_eq_zero_of_ne
      intro heq
      apply hne
      simpa only [
        trivialActionStrongGlaubermanCharacterEquiv_apply_coe]
        using heq
    exact hφ (hzero ▸ dvd_zero p)

/-- A subsingleton acting group acts trivially, hence has the strong
Glauberman correspondence. -/
def strongActionGlaubermanCorrespondenceOfSubsingleton
    [Subsingleton P] :
    StrongActionGlaubermanCorrespondence P A p :=
  strongActionGlaubermanCorrespondenceOfTrivial
    P A (fun g a ↦ by
      rw [Subsingleton.elim g 1, one_smul])

end McKayConjecture
