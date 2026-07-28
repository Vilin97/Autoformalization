/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralIndexInduction
import McKayConjecture.InductiveMcKay.CentralScalarLocalCorrespondence

/-!
# Central-scalar numerical induction

This file gives the well-founded induction framework tailored to the
numerical McKay theorem.  Its local datum remembers exactly the central
value identity needed by projective factor extensions and forgets the
stronger automorphism and external character-triple clauses.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open McKayConjecture.GroupTheory

/-- The central-scalar numerical local condition at `p`. -/
def CentralScalarNumericalInductiveMcKay
    (p : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (P : Sylow p G),
    Nonempty (CentralScalarLocalCorrespondence P)

namespace CentralScalarNumericalInductiveMcKay

/-- Forget the central-value identity and retain the numerical local
condition. -/
theorem toNumerical
    (h : CentralScalarNumericalInductiveMcKay.{u} p) :
    NumericalInductiveMcKay.{u} p := by
  intro G _ _ P
  obtain ⟨d⟩ := h G P
  exact ⟨d.toLocal⟩

/-- The central-scalar numerical condition implies the McKay statement. -/
theorem statement
    [Fact p.Prime]
    (h : CentralScalarNumericalInductiveMcKay.{u} p)
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  h.toNumerical.statement G P

end CentralScalarNumericalInductiveMcKay

/-- One central-index induction step for the central-scalar numerical
condition. -/
def CentralScalarCentralIndexInductionStep
    (p : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (P : Sylow p G),
    (∀ (H : Type u) [Group H] [Finite H],
      centralIndex H < centralIndex G →
        ∀ Q : Sylow p H,
          Nonempty (CentralScalarLocalCorrespondence Q)) →
      Nonempty (CentralScalarLocalCorrespondence P)

/-- A valid central-index step establishes the central-scalar numerical
condition for all finite groups. -/
theorem centralScalarNumericalInductiveMcKay_of_centralIndexStep
    {p : ℕ}
    (step :
      CentralScalarCentralIndexInductionStep.{u} p) :
    CentralScalarNumericalInductiveMcKay.{u} p := by
  intro G _ _ P
  have all :
      ∀ n : ℕ,
        (∀ m < n,
          ∀ (H : Type u) [Group H] [Finite H],
            centralIndex H = m →
              ∀ Q : Sylow p H,
                Nonempty
                  (CentralScalarLocalCorrespondence Q)) →
          ∀ (H : Type u) [Group H] [Finite H],
            centralIndex H = n →
              ∀ Q : Sylow p H,
                Nonempty
                  (CentralScalarLocalCorrespondence Q) := by
    intro n ih H _ _ hmeasure Q
    apply step H Q
    intro K _ _ hsmall R
    exact
      ih (centralIndex K)
        (by simpa only [hmeasure] using hsmall)
        K rfl R
  exact
    Nat.strong_induction_on
      (centralIndex G)
      (p := fun n =>
        ∀ (H : Type u) [Group H] [Finite H],
          centralIndex H = n →
            ∀ Q : Sylow p H,
              Nonempty
                (CentralScalarLocalCorrespondence Q))
      all G rfl P

/-- The noncommutative part of the scalar numerical central-index step. -/
def NoncommutativeCentralScalarCentralIndexInductionStep
    (p : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (P : Sylow p G),
    ¬IsMulCommutative G →
      (∀ (H : Type u) [Group H] [Finite H],
        centralIndex H < centralIndex G →
          ∀ Q : Sylow p H,
            Nonempty
              (CentralScalarLocalCorrespondence Q)) →
        Nonempty (CentralScalarLocalCorrespondence P)

/-- It suffices to construct the scalar numerical local datum for
noncommutative groups.  The commutative case is the full-group identity
datum, forgotten to the central-scalar condition. -/
theorem centralScalarNumericalInductiveMcKay_of_noncommutativeCentralIndexStep
    {p : ℕ}
    (step :
      NoncommutativeCentralScalarCentralIndexInductionStep.{u} p) :
    CentralScalarNumericalInductiveMcKay.{u} p := by
  apply
    centralScalarNumericalInductiveMcKay_of_centralIndexStep
  intro G _ _ P ih
  by_cases hG : IsMulCommutative G
  · exact
      ⟨(LocalInductiveMcKayData.of_isMulCommutative
        hG P).toCentralScalarLocal⟩
  · exact step G P hG ih

end InductiveMcKay
end McKayConjecture
