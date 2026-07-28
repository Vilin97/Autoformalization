/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionPGroupInduction
import McKayConjecture.Character.GlaubermanActionTransport
import McKayConjecture.Character.GlaubermanCyclicConjugationAction
import McKayConjecture.GroupTheory.CoprimeActionSemidirect

/-!
# Strong Glauberman correspondence for cyclic actions

An abstract action is realized by its canonical semidirect product.  The
kernel and acting factor are isomorphic to the original groups, and
conjugation in the semidirect product is equivariant with the original
action.  Transporting the cyclic trace correspondence through these
coordinates proves the cyclic strong action hypothesis used by the
induction on the acting `p`-group.
-/

noncomputable section

namespace McKayConjecture

variable (P A : Type) [Group P] [Group A]
variable [MulDistribMulAction P A]
variable [Finite P] [Finite A]
variable {p : ℕ} [Fact p.Prime]

local instance actionSemidirectConjugationMulDistribMulAction :
    MulDistribMulAction
      (GroupTheory.actionActingSubgroup P A)
      (GroupTheory.actionKernel P A) :=
  subgroupConjugationMulDistribMulAction
    (GroupTheory.actionKernel P A)
    (GroupTheory.actionActingSubgroup P A)

/-- Conjugation of the canonical kernel by the canonical acting subgroup
is the original action in semidirect-product coordinates. -/
theorem actionSemidirect_conjugation_equivariant
    (q : GroupTheory.actionActingSubgroup P A)
    (a : GroupTheory.actionKernel P A) :
    GroupTheory.actionKernelEquiv P A (q • a) =
      GroupTheory.actionActingSubgroupEquiv P A q •
        GroupTheory.actionKernelEquiv P A a := by
  change
    (q.1 * a.1 * q.1⁻¹).left =
      q.1.right • a.1.left
  obtain ⟨g, hg⟩ := q.2
  obtain ⟨b, hb⟩ := a.2
  rw [← hg, ← hb]
  simp

/-- The fully constructed strong Glauberman correspondence for an
arbitrary cyclic `p`-group action on a finite `p'`-group. -/
def strongCyclicActionGlaubermanCorrespondence
    [IsCyclic P]
    (hP : IsPGroup p P)
    (hA : GroupTheory.IsPPrimeGroup p A) :
    StrongActionGlaubermanCorrespondence P A p := by
  let G := GroupTheory.actionSemidirectProduct P A
  let K : Subgroup G :=
    GroupTheory.actionKernel P A
  let Q : Subgroup G :=
    GroupTheory.actionActingSubgroup P A
  let eP : Q ≃* P :=
    GroupTheory.actionActingSubgroupEquiv P A
  let eA : K ≃* A :=
    GroupTheory.actionKernelEquiv P A
  letI : IsCyclic Q :=
    eP.isCyclic.mpr (inferInstance : IsCyclic P)
  have hQ : IsPGroup p Q :=
    GroupTheory.actionActingSubgroup_isPGroup
      P A hP
  have hK : GroupTheory.IsPPrimeGroup p K :=
    GroupTheory.actionKernel_isPPrimeGroup
      P A hA
  let d : StrongActionGlaubermanCorrespondence Q K p :=
    strongCyclicConjugationActionGlaubermanCorrespondence
      K Q hK hQ
      (GroupTheory.actionKernel_sup_actionActingSubgroup
        P A)
  exact
    StrongActionGlaubermanCorrespondence.transport
      P Q A K eP eA
      (actionSemidirect_conjugation_equivariant P A)
      d

/-- The cyclic strong-action hypothesis required by the induction on
finite `p`-groups is unconditional. -/
theorem cyclicStrongActionGlaubermanHypothesis :
    CyclicStrongActionGlaubermanHypothesis p := by
  intro P A _instP _instA _instAction
    _instFiniteP _instFiniteA _instCyclic hP hA
  exact
    ⟨strongCyclicActionGlaubermanCorrespondence
      P A hP hA⟩

end McKayConjecture
