/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import McKayConjecture.GroupTheory.FreePresentationCentralExtension

/-!
# The Hopf kernel of the free-presentation cover

For the canonical free presentation `F → S`, with relation subgroup `R`
and derived subgroup `D = [F,F]`, the kernel of

`D / [F,R] → S`

is the Hopf-formula quotient

`(R ∩ D) / [F,R]`.

This file defines that quotient and gives an explicit multiplicative
equivalence to the kernel of `coverProjection`.  It is deliberately stated
for an arbitrary group: perfectness is only needed to make the projection
surjective, not to identify its kernel.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory
namespace FreePresentation

variable (S : Type u) [Group S]

/-- The relation subgroup inside the derived subgroup.  As a subgroup of
the ambient free group, this is `R ∩ [F,F]`. -/
def hopfNumerator :
    Subgroup (derived S) :=
  (relations S).subgroupOf (derived S)

instance hopfNumerator_normal :
    (hopfNumerator S).Normal := by
  unfold hopfNumerator
  infer_instance

/-- The kernel of evaluation restricted to the derived subgroup is exactly
the Hopf numerator `R ∩ [F,F]`. -/
@[simp]
theorem derivedEvaluation_ker_eq_hopfNumerator :
    (derivedEvaluation S).ker = hopfNumerator S :=
  rfl

/-- The commutator relators `[F,R]` lie in the Hopf numerator. -/
theorem centralRelatorsInDerived_le_hopfNumerator :
    centralRelatorsInDerived S ≤ hopfNumerator S := by
  rw [← derivedEvaluation_ker_eq_hopfNumerator]
  exact centralRelatorsInDerived_le_ker S

/-- The quotient `(R ∩ [F,F]) / [F,R]` occurring in the Hopf formula. -/
abbrev HopfKernel :=
  hopfNumerator S ⧸
    (centralRelatorsInDerived S).subgroupOf
      (hopfNumerator S)

/-- The projection kernel, viewed in `D / [F,R]`, is the image of the
Hopf numerator. -/
theorem coverProjection_ker_eq_map_hopfNumerator :
    (coverProjection S).ker =
      (hopfNumerator S).map
        (QuotientGroup.mk'
          (centralRelatorsInDerived S)) := by
  rw [coverProjection, QuotientGroup.ker_lift,
    derivedEvaluation_ker_eq_hopfNumerator]

/-- The Hopf-formula quotient is canonically equivalent to the checked
kernel of the free-presentation cover. -/
def hopfKernelEquivCoverProjectionKer :
    HopfKernel S ≃*
      (coverProjection S).ker := by
  let q :=
    (QuotientGroup.mk'
      (centralRelatorsInDerived S)).subgroupMap
        (hopfNumerator S)
  have hqSurjective :
      Function.Surjective q :=
    MonoidHom.subgroupMap_surjective _ _
  have hqKer :
      q.ker =
        (centralRelatorsInDerived S).subgroupOf
          (hopfNumerator S) := by
    change
      ((QuotientGroup.mk'
        (centralRelatorsInDerived S)).subgroupMap
          (hopfNumerator S)).ker =
        (centralRelatorsInDerived S).subgroupOf
          (hopfNumerator S)
    rw [Subgroup.ker_subgroupMap,
      QuotientGroup.ker_mk']
  exact
    (QuotientGroup.quotientMulEquivOfEq hqKer.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective
          q hqSurjective).trans
        (MulEquiv.subgroupCongr
          (coverProjection_ker_eq_map_hopfNumerator S).symm))

/-- Cardinality form of the Hopf formula for the free-presentation cover
kernel. -/
theorem natCard_hopfKernel_eq_natCard_coverProjection_ker :
    Nat.card (HopfKernel S) =
      Nat.card (coverProjection S).ker :=
  Nat.card_congr
    (hopfKernelEquivCoverProjectionKer S).toEquiv

end FreePresentation
end GroupTheory
end McKayConjecture
