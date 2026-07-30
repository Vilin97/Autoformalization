/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentrallyClosedFreePresentation
import McKayConjecture.InductiveMcKay.ProjectiveSpecialLinearTwoExceptionalCoverSplit

/-!
# Generic PSL₂ central closedness as a Hopf-kernel computation

The generic `SL(2,q)` branch needs central closedness outside `q = 4,9`.
For a perfect group, the free-presentation Hopf kernel is its Schur
multiplier.  Cardinality one therefore gives exactly the required
central-closedness input.

This file does not assert the multiplier computation.  It replaces the
abstract splitting condition by a single explicit family of finite
cardinality equalities, which is the natural endpoint for a future
rank-one Steinberg-presentation argument.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The remaining generic Schur-multiplier computation for the
special-linear covers. -/
def ProjectiveSpecialLinearTwoGenericHopfKernelTrivialResidual : Prop :=
  ∀ a : ProjectiveSpecialLinearTwoGenericParameter,
    Nat.card
        (FreePresentation.HopfKernel
          (projectiveSpecialLinearTwoSpecialLinearCover a.1)) =
      1

/-- Triviality of every generic special-linear Hopf kernel implies the
existing generic central-closedness residual. -/
theorem
    projectiveSpecialLinearTwoGenericCentrallyClosedResidual_of_hopfKernelTrivial
    (h : ProjectiveSpecialLinearTwoGenericHopfKernelTrivialResidual) :
    ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual := by
  intro a
  exact
    isCentrallyClosed_of_hopfKernel_card_one
      (projectiveSpecialLinearTwoSpecialLinearCover_isPerfect a.1)
      (h a)

namespace ProjectiveSpecialLinearTwoGenericHopfKernelTrivialResidual

/-- The Hopf-kernel residual directly supplies the universal
special-linear cover used by the generic verification reduction. -/
def universalCentralExtension
    (h : ProjectiveSpecialLinearTwoGenericHopfKernelTrivialResidual)
    (a : ProjectiveSpecialLinearTwoGenericParameter) :
    UniversalCentralExtension
      (projectiveSpecialLinearTwoSpecialLinearCover a.1)
      (projectiveSpecialLinearTwoRepresentative a.1) :=
  ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual.universalCentralExtension
    (projectiveSpecialLinearTwoGenericCentrallyClosedResidual_of_hopfKernelTrivial
      h)
    a

/-- The same residual identifies the free-presentation universal cover of
`PSL(2,q)` with `SL(2,q)` on every generic parameter. -/
def universalCoverEquivSpecialLinear
    (h : ProjectiveSpecialLinearTwoGenericHopfKernelTrivialResidual)
    (a : ProjectiveSpecialLinearTwoGenericParameter) :
    projectiveSpecialLinearTwoUniversalCover a.1 ≃*
      projectiveSpecialLinearTwoSpecialLinearCover a.1 :=
  ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual.universalCoverEquivSpecialLinear
    (projectiveSpecialLinearTwoGenericCentrallyClosedResidual_of_hopfKernelTrivial
      h)
    a

end ProjectiveSpecialLinearTwoGenericHopfKernelTrivialResidual

end InductiveMcKay
end McKayConjecture
