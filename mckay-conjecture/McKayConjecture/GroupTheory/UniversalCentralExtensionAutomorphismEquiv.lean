/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.UniversalCentralExtensionAutomorphismInjection

/-!
# Automorphism groups of universal central extensions

For a universal central extension of a nonabelian simple group, lifting
target automorphisms and descending source automorphisms are inverse group
homomorphisms.  The injective direction was isolated previously; this file
records the two-sided multiplicative equivalence.
-/

noncomputable section

open scoped IsMulCommutative

universe u

namespace McKayConjecture
namespace GroupTheory
namespace UniversalCentralExtension

variable {U S : Type u}
variable [Group U] [Group S]

/-- Descending the canonical lift of a target automorphism recovers that
target automorphism. -/
theorem inducedTargetAutomorphism_targetAutomorphismLift
    (E : UniversalCentralExtension U S)
    (hsimple : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (β : MulAut S) :
    E.toCentralExtension.inducedTargetAutomorphism
        hsimple hnoncomm
        (E.targetAutomorphismLift β) =
      β := by
  ext s
  obtain ⟨u, rfl⟩ :=
    E.toCentralExtension.surjective s
  rw [
    E.toCentralExtension.inducedTargetAutomorphism_projection,
    E.projection_targetAutomorphismLift
  ]

/-- The automorphism group of a universal central extension of a
nonabelian simple group is canonically equivalent to the automorphism group
of its target. -/
def sourceAutomorphismMulEquivTarget
    (E : UniversalCentralExtension U S)
    (hsimple : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S) :
    MulAut U ≃* MulAut S :=
  MonoidHom.toMulEquiv
    (E.toCentralExtension.inducedTargetAutomorphismMonoidHom
      hsimple hnoncomm)
    E.targetAutomorphismLiftMonoidHom
    (by
      apply MonoidHom.ext
      intro α
      exact
        E.targetAutomorphismLift_inducedTargetAutomorphism
          hsimple hnoncomm α)
    (by
      apply MonoidHom.ext
      intro β
      exact
        E.inducedTargetAutomorphism_targetAutomorphismLift
          hsimple hnoncomm β)

@[simp]
theorem sourceAutomorphismMulEquivTarget_apply
    (E : UniversalCentralExtension U S)
    (hsimple : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (α : MulAut U) :
    E.sourceAutomorphismMulEquivTarget hsimple hnoncomm α =
      E.toCentralExtension.inducedTargetAutomorphism
        hsimple hnoncomm α :=
  rfl

@[simp]
theorem sourceAutomorphismMulEquivTarget_symm_apply
    (E : UniversalCentralExtension U S)
    (hsimple : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (β : MulAut S) :
    (E.sourceAutomorphismMulEquivTarget
        hsimple hnoncomm).symm β =
      E.targetAutomorphismLift β :=
  rfl

end UniversalCentralExtension
end GroupTheory
end McKayConjecture
