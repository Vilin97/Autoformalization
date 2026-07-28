/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralIndex
import McKayConjecture.InductiveMcKay.AbelianLocal
import McKayConjecture.InductiveMcKay.Condition
import McKayConjecture.InductiveMcKay.TrivialLocal

/-!
# Induction on the central index

Rossi's reduction chooses a counterexample minimal with respect to
`|G : Z(G)|`.  This file isolates that well-founded induction.  Its
step hypothesis receives the full inductive-McKay data for every finite
group of smaller central index and must construct the datum for the
current group.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open McKayConjecture.GroupTheory

/-- One induction step for constructing full inductive-McKay data,
using central index as the measure. -/
def CentralIndexInductionStep (p : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (P : Sylow p G),
    (∀ (H : Type u) [Group H] [Finite H],
      centralIndex H < centralIndex G →
        ∀ Q : Sylow p H,
          Nonempty (LocalInductiveMcKayData Q)) →
      Nonempty (LocalInductiveMcKayData P)

/-- A valid central-index induction step constructs full local
inductive-McKay data for every finite group. -/
theorem inductiveMcKayCondition_of_centralIndexInductionStep
    {p : ℕ}
    (step : CentralIndexInductionStep.{u} p) :
    InductiveMcKayCondition.{u} p := by
  intro G _ _ P
  have all :
      ∀ n : ℕ,
        (∀ m < n,
          ∀ (H : Type u) [Group H] [Finite H],
            centralIndex H = m →
              ∀ Q : Sylow p H,
                Nonempty (LocalInductiveMcKayData Q)) →
          ∀ (H : Type u) [Group H] [Finite H],
            centralIndex H = n →
              ∀ Q : Sylow p H,
                Nonempty (LocalInductiveMcKayData Q) := by
    intro n ih H _ _ hmeasure Q
    apply step H Q
    intro K _ _ hsmall R
    exact
      ih (centralIndex K) (by simpa only [hmeasure] using hsmall)
        K rfl R
  exact
    Nat.strong_induction_on
      (centralIndex G)
      (p := fun n =>
        ∀ (H : Type u) [Group H] [Finite H],
          centralIndex H = n →
            ∀ Q : Sylow p H,
              Nonempty (LocalInductiveMcKayData Q))
      all G rfl P

/-- The noncommutative part of the full central-index induction step.
The normal-Sylow identity construction handles the commutative case. -/
def NoncommutativeCentralIndexInductionStep
    (p : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (P : Sylow p G),
    ¬IsMulCommutative G →
      (∀ (H : Type u) [Group H] [Finite H],
        centralIndex H < centralIndex G →
          ∀ Q : Sylow p H,
            Nonempty (LocalInductiveMcKayData Q)) →
        Nonempty (LocalInductiveMcKayData P)

/-- To establish the full inductive McKay condition by central-index
induction, it suffices to construct the local datum for noncommutative
groups. -/
theorem inductiveMcKayCondition_of_noncommutativeCentralIndexStep
    {p : ℕ}
    (step : NoncommutativeCentralIndexInductionStep.{u} p) :
    InductiveMcKayCondition.{u} p := by
  apply inductiveMcKayCondition_of_centralIndexInductionStep
  intro G _ _ P ih
  by_cases hG : IsMulCommutative G
  · exact
      ⟨LocalInductiveMcKayData.of_isMulCommutative
        hG P⟩
  · exact step G P hG ih

/-- Numerical version of one central-index induction step. -/
def NumericalCentralIndexInductionStep (p : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (P : Sylow p G),
    (∀ (H : Type u) [Group H] [Finite H],
      centralIndex H < centralIndex G →
        ∀ Q : Sylow p H,
          Nonempty (LocalCorrespondence Q)) →
      Nonempty (LocalCorrespondence P)

/-- A valid numerical central-index induction step gives the numerical
inductive McKay condition. -/
theorem numericalInductiveMcKay_of_centralIndexInductionStep
    {p : ℕ}
    (step : NumericalCentralIndexInductionStep.{u} p) :
    NumericalInductiveMcKay.{u} p := by
  intro G _ _ P
  have all :
      ∀ n : ℕ,
        (∀ m < n,
          ∀ (H : Type u) [Group H] [Finite H],
            centralIndex H = m →
              ∀ Q : Sylow p H,
                Nonempty (LocalCorrespondence Q)) →
          ∀ (H : Type u) [Group H] [Finite H],
            centralIndex H = n →
              ∀ Q : Sylow p H,
                Nonempty (LocalCorrespondence Q) := by
    intro n ih H _ _ hmeasure Q
    apply step H Q
    intro K _ _ hsmall R
    exact
      ih (centralIndex K) (by simpa only [hmeasure] using hsmall)
        K rfl R
  exact
    Nat.strong_induction_on
      (centralIndex G)
      (p := fun n =>
        ∀ (H : Type u) [Group H] [Finite H],
          centralIndex H = n →
            ∀ Q : Sylow p H,
              Nonempty (LocalCorrespondence Q))
      all G rfl P

/-- The noncommutative part of a numerical central-index induction step.
The commutative base case is elementary and is discharged separately. -/
def NoncommutativeNumericalCentralIndexInductionStep
    (p : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (P : Sylow p G),
    ¬IsMulCommutative G →
      (∀ (H : Type u) [Group H] [Finite H],
        centralIndex H < centralIndex G →
          ∀ Q : Sylow p H,
            Nonempty (LocalCorrespondence Q)) →
        Nonempty (LocalCorrespondence P)

/-- It suffices to construct the numerical local correspondence in the
noncommutative induction case.  For a commutative group the Sylow
normalizer is the whole group. -/
theorem numericalInductiveMcKay_of_noncommutativeCentralIndexStep
    {p : ℕ}
    (step :
      NoncommutativeNumericalCentralIndexInductionStep.{u} p) :
    NumericalInductiveMcKay.{u} p := by
  apply numericalInductiveMcKay_of_centralIndexInductionStep
  intro G _ _ P ih
  by_cases hG : IsMulCommutative G
  · exact ⟨LocalCorrespondence.of_isMulCommutative hG P⟩
  · exact step G P hG ih

end InductiveMcKay
end McKayConjecture
