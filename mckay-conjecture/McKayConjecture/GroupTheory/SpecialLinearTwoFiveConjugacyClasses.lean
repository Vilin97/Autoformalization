/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SpecialLinearTwoFivePresentation

/-!
# Conjugacy classes of `SL(2, 𝔽₅)`

This file records an executable nine-row conjugacy-class table for the
concrete group `SL(2, ZMod 5)`.  Representatives are short words in the
balanced binary-icosahedral generators.  The exhaustive classification and
the class sizes are kernel-checked finite computations.
-/

namespace McKayConjecture
namespace GroupTheory

/-- A nine-element index for the conjugacy classes of the binary
icosahedral group.  In order, the rows have element orders
`1, 2, 4, 6, 3, 10, 10, 5, 5`. -/
abbrev SpecialLinearTwoFiveConjugacyClass :=
  Fin 9

/-- Short-word representatives of all conjugacy classes. -/
def specialLinearTwoFiveConjugacyRepresentative :
    SpecialLinearTwoFiveConjugacyClass →
      SpecialLinearTwoFive
  | 0 => 1
  | 1 => -1
  | 2 => specialLinearTwoFivePresentationX
  | 3 => specialLinearTwoFivePresentationY
  | 4 => specialLinearTwoFivePresentationY ^ 2
  | 5 => specialLinearTwoFivePresentationZ
  | 6 => specialLinearTwoFivePresentationZ ^ 3
  | 7 => specialLinearTwoFivePresentationZ ^ 2
  | 8 => specialLinearTwoFivePresentationZ ^ 4

/-- The expected sizes of the nine conjugacy classes. -/
def specialLinearTwoFiveConjugacyClassSize :
    SpecialLinearTwoFiveConjugacyClass → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 30
  | 3 => 20
  | 4 => 20
  | 5 => 12
  | 6 => 12
  | 7 => 12
  | 8 => 12

/-- Executable conjugacy test for the concrete finite matrix group. -/
def specialLinearTwoFiveAreConjugate
    (g h : SpecialLinearTwoFive) : Bool :=
  decide (∃ x : SpecialLinearTwoFive,
    x * g * x⁻¹ = h)

theorem specialLinearTwoFiveAreConjugate_iff_isConj
    (g h : SpecialLinearTwoFive) :
    specialLinearTwoFiveAreConjugate g h = true ↔
      IsConj g h := by
  simp [specialLinearTwoFiveAreConjugate, isConj_iff]

/-- Every concrete matrix lies in exactly one of the nine displayed
conjugacy classes. -/
theorem specialLinearTwoFive_existsUnique_conjugacyClass
    (g : SpecialLinearTwoFive) :
    ∃! c : SpecialLinearTwoFiveConjugacyClass,
      IsConj g
        (specialLinearTwoFiveConjugacyRepresentative c) := by
  simp only [←
    specialLinearTwoFiveAreConjugate_iff_isConj]
  obtain ⟨c, hc⟩ :
      ∃ c : SpecialLinearTwoFiveConjugacyClass,
        specialLinearTwoFiveAreConjugate g
          (specialLinearTwoFiveConjugacyRepresentative c) =
            true := by
    revert g
    native_decide
  refine ⟨c, hc, ?_⟩
  intro d hd
  revert g c d
  native_decide

/-- The executable cardinality of each displayed conjugacy class. -/
theorem specialLinearTwoFive_card_conjugacyClass
    (c : SpecialLinearTwoFiveConjugacyClass) :
    (Finset.univ.filter fun g : SpecialLinearTwoFive =>
      specialLinearTwoFiveAreConjugate g
        (specialLinearTwoFiveConjugacyRepresentative c) = true).card =
      specialLinearTwoFiveConjugacyClassSize c := by
  fin_cases c <;> native_decide

/-- Every displayed class is closed under inversion. -/
theorem specialLinearTwoFiveConjugacyRepresentative_isConj_inv
    (c : SpecialLinearTwoFiveConjugacyClass) :
    IsConj
      (specialLinearTwoFiveConjugacyRepresentative c)
      (specialLinearTwoFiveConjugacyRepresentative c)⁻¹ := by
  apply
    (specialLinearTwoFiveAreConjugate_iff_isConj _ _).1
  fin_cases c <;> native_decide

/-- Any conjugacy-invariant finite sum over `SL(2, 𝔽₅)` reduces to the
nine representative values with the displayed class multiplicities. -/
theorem specialLinearTwoFive_sum_by_conjugacyClasses
    {R : Type*} [AddCommMonoid R]
    (f : SpecialLinearTwoFive → R)
    (hf :
      ∀ {g h : SpecialLinearTwoFive},
        IsConj g h → f g = f h) :
    (∑ g : SpecialLinearTwoFive, f g) =
      ∑ c : SpecialLinearTwoFiveConjugacyClass,
        specialLinearTwoFiveConjugacyClassSize c •
          f (specialLinearTwoFiveConjugacyRepresentative c) := by
  have hpointwise (g : SpecialLinearTwoFive) :
      f g =
        ∑ c : SpecialLinearTwoFiveConjugacyClass,
          if specialLinearTwoFiveAreConjugate g
              (specialLinearTwoFiveConjugacyRepresentative c) = true then
            f (specialLinearTwoFiveConjugacyRepresentative c)
          else 0 := by
    obtain ⟨c, hc, hunique⟩ :=
      specialLinearTwoFive_existsUnique_conjugacyClass g
    have hcBool :
        specialLinearTwoFiveAreConjugate g
            (specialLinearTwoFiveConjugacyRepresentative c) =
          true :=
      (specialLinearTwoFiveAreConjugate_iff_isConj _ _).2 hc
    rw [Finset.sum_eq_single c]
    · rw [if_pos hcBool]
      exact hf hc
    · intro d _ hdc
      have hd :
          ¬IsConj g
            (specialLinearTwoFiveConjugacyRepresentative d) := by
        intro hd
        exact hdc (hunique d hd)
      rw [if_neg]
      exact fun hdBool =>
        hd
          ((specialLinearTwoFiveAreConjugate_iff_isConj _ _).1
            hdBool)
    · simp
  calc
    (∑ g : SpecialLinearTwoFive, f g) =
        ∑ g : SpecialLinearTwoFive,
          ∑ c : SpecialLinearTwoFiveConjugacyClass,
            if specialLinearTwoFiveAreConjugate g
                (specialLinearTwoFiveConjugacyRepresentative c) = true then
              f (specialLinearTwoFiveConjugacyRepresentative c)
            else 0 := by
          apply Finset.sum_congr rfl
          intro g _
          exact hpointwise g
    _ =
        ∑ c : SpecialLinearTwoFiveConjugacyClass,
          ∑ g : SpecialLinearTwoFive,
            if specialLinearTwoFiveAreConjugate g
                (specialLinearTwoFiveConjugacyRepresentative c) = true then
              f (specialLinearTwoFiveConjugacyRepresentative c)
            else 0 := by
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.sum_filter]
      rw [Finset.sum_const]
      rw [specialLinearTwoFive_card_conjugacyClass]

end GroupTheory
end McKayConjecture
