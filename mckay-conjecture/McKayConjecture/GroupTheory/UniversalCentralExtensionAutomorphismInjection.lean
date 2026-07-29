/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.UniversalCentralExtensionAutomorphism
import McKayConjecture.GroupTheory.UniversalCentralExtensionSourceEquiv

/-!
# Automorphisms of a universal central extension inject into target automorphisms

For a universal central extension of a nonabelian simple group, an
automorphism of the source induces an automorphism of the target.  Lifting
that induced target automorphism recovers the original source automorphism,
so the induction map is injective.
-/

noncomputable section

open scoped IsMulCommutative

universe u

namespace McKayConjecture
namespace GroupTheory
namespace UniversalCentralExtension

variable {U S : Type u}
variable [Group U] [Group S]

/-- Lifting the target automorphism induced by a source automorphism recovers
that source automorphism. -/
theorem targetAutomorphismLift_inducedTargetAutomorphism
    (E : UniversalCentralExtension U S)
    (hsimple : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (α : MulAut U) :
    E.targetAutomorphismLift
        (E.toCentralExtension.inducedTargetAutomorphism
          hsimple hnoncomm α) =
      α := by
  apply MulEquiv.toMonoidHom_injective
  simpa [E.mapToSelf_eq_id] using
    E.targetAutomorphismLift_intertwines_mapToCentralExtension
      E.toCentralExtension hsimple hnoncomm α

/-- Source automorphisms act faithfully on the simple target of a universal
central extension. -/
theorem inducedTargetAutomorphismMonoidHom_injective
    (E : UniversalCentralExtension U S)
    (hsimple : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S) :
    Function.Injective
      (E.toCentralExtension.inducedTargetAutomorphismMonoidHom
        hsimple hnoncomm) :=
  Function.LeftInverse.injective
    (fun α =>
      E.targetAutomorphismLift_inducedTargetAutomorphism
        hsimple hnoncomm α)

end UniversalCentralExtension
end GroupTheory
end McKayConjecture
