/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.UniversalCentralExtension

/-!
# Transporting universal central extensions across the target

Composing the projection of a central extension with a target-group
isomorphism preserves centrality and universality.  This lets a
classification theorem use one representative of each isomorphism class
of nonabelian finite simple groups.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {U S T : Type u}
variable [Group U] [Group S] [Group T]

namespace CentralExtension

/-- Transport a central extension across an isomorphism of its target. -/
def targetEquiv
    (E : CentralExtension U S)
    (e : S ≃* T) :
    CentralExtension U T where
  projection :=
    e.toMonoidHom.comp E.projection
  surjective :=
    e.surjective.comp E.surjective
  ker_le_center := by
    intro u hu
    apply E.ker_le_center
    apply MonoidHom.mem_ker.mpr
    apply e.injective
    have hu' :=
      MonoidHom.mem_ker.mp hu
    simpa using hu'

@[simp]
theorem targetEquiv_projection
    (E : CentralExtension U S)
    (e : S ≃* T) :
    (E.targetEquiv e).projection =
      e.toMonoidHom.comp E.projection :=
  rfl

end CentralExtension

namespace UniversalCentralExtension

/-- Transport a universal central extension across an isomorphism of its
target. -/
def targetEquiv
    (E : UniversalCentralExtension U S)
    (e : S ≃* T) :
    UniversalCentralExtension U T where
  toCentralExtension :=
    E.toCentralExtension.targetEquiv e
  sourcePerfect :=
    E.sourcePerfect
  lift := by
    intro V groupV F
    let F' : CentralExtension V S :=
      F.targetEquiv e.symm
    obtain ⟨f, hf, hfunique⟩ :=
      E.lift V F'
    refine ⟨f, ?_, ?_⟩
    · ext v
      have hv :=
        DFunLike.congr_fun hf v
      have hev :=
        congrArg e hv
      simpa [F'] using hev
    · intro g hg
      apply hfunique
      ext v
      have hv :=
        DFunLike.congr_fun hg v
      have hev :=
        congrArg e.symm hv
      simpa [F'] using hev

@[simp]
theorem targetEquiv_projection
    (E : UniversalCentralExtension U S)
    (e : S ≃* T) :
    (E.targetEquiv e).toCentralExtension.projection =
      e.toMonoidHom.comp E.toCentralExtension.projection :=
  rfl

end UniversalCentralExtension
end GroupTheory
end McKayConjecture
