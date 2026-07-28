/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionStrongTransitivity
import McKayConjecture.Character.GlaubermanActionTrivial
import McKayConjecture.GroupTheory.PGroupMaximalCyclicQuotient
import McKayConjecture.GroupTheory.PPrimeCore

/-!
# Glauberman correspondence by induction on the acting `p`-group

Every nontrivial finite `p`-group has a proper normal subgroup with cyclic
`p`-group quotient.  Strong cyclic correspondences therefore compose,
through the transitivity theorem, to a strong correspondence for every
finite `p`-group action on a finite `p'`-group.
-/

noncomputable section

namespace McKayConjecture

variable {p : ℕ} [Fact p.Prime]

/-- The cyclic action theorem needed in each chief step of a finite
`p`-group. -/
def CyclicStrongActionGlaubermanHypothesis (p : ℕ) : Prop :=
  ∀ (P A : Type) [Group P] [Group A]
    [MulDistribMulAction P A]
    [Finite P] [Finite A] [IsCyclic P],
    IsPGroup p P →
      GroupTheory.IsPPrimeGroup p A →
        Nonempty
          (StrongActionGlaubermanCorrespondence P A p)

private theorem strongActionGlaubermanCorrespondenceOfPGroup_aux
    (cyclic : CyclicStrongActionGlaubermanHypothesis p)
    (P A : Type) [Group P] [Group A]
    [MulDistribMulAction P A]
    [Finite P] [Finite A]
    (hP : IsPGroup p P)
    (hA : GroupTheory.IsPPrimeGroup p A) :
    Nonempty
      (StrongActionGlaubermanCorrespondence P A p) := by
  classical
  by_cases hnontrivial : Nontrivial P
  · letI : Nontrivial P := hnontrivial
    obtain ⟨Q, hQcard, hQp, hQuotientP,
        hQuotientCyclic⟩ :=
      GroupTheory.IsPGroup.exists_normal_card_lt_cyclic_quotient
        hP
    obtain ⟨dQ⟩ :=
      strongActionGlaubermanCorrespondenceOfPGroup_aux
        cyclic Q.toSubgroup A hQp hA
    letI : IsCyclic (P ⧸ Q.toSubgroup) :=
      hQuotientCyclic
    have hfixedPPrime :
        GroupTheory.IsPPrimeGroup p
          (FixedPoints.subgroup Q.toSubgroup A) :=
      hA.to_subgroup
        (FixedPoints.subgroup Q.toSubgroup A)
    obtain ⟨dQuot⟩ :=
      cyclic
        (P ⧸ Q.toSubgroup)
        (FixedPoints.subgroup Q.toSubgroup A)
        hQuotientP hfixedPPrime
    exact
      ⟨StrongActionGlaubermanCorrespondence.transitive
        P A Q.toSubgroup dQ dQuot⟩
  · letI : Subsingleton P :=
      not_nontrivial_iff_subsingleton.mp hnontrivial
    exact
      ⟨strongActionGlaubermanCorrespondenceOfSubsingleton
        P A⟩
termination_by Nat.card P

/-- Strong cyclic Glauberman correspondences imply the strong
correspondence for every finite `p`-group action on a finite `p'`-group. -/
theorem strongActionGlaubermanCorrespondenceOfPGroup
    (cyclic : CyclicStrongActionGlaubermanHypothesis p)
    (P A : Type) [Group P] [Group A]
    [MulDistribMulAction P A]
    [Finite P] [Finite A]
    (hP : IsPGroup p P)
    (hA : GroupTheory.IsPPrimeGroup p A) :
    Nonempty
      (StrongActionGlaubermanCorrespondence P A p) :=
  strongActionGlaubermanCorrespondenceOfPGroup_aux
    cyclic P A hP hA

/-- Ordinary action-level form of the preceding induction theorem. -/
theorem actionGlaubermanCorrespondenceOfPGroup
    (cyclic : CyclicStrongActionGlaubermanHypothesis p)
    (P A : Type) [Group P] [Group A]
    [MulDistribMulAction P A]
    [Finite P] [Finite A]
    (hP : IsPGroup p P)
    (hA : GroupTheory.IsPPrimeGroup p A) :
    Nonempty
      (ActionGlaubermanCorrespondence P A p) := by
  obtain ⟨d⟩ :=
    strongActionGlaubermanCorrespondenceOfPGroup
      cyclic P A hP hA
  exact ⟨d.toAction⟩

end McKayConjecture
