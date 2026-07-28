/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.FreePresentationUniversalCentralExtension
import McKayConjecture.GroupTheory.PerfectCentralExtensionFinite
import McKayConjecture.GroupTheory.SimpleQuasisimple

/-!
# Finite universal central extensions

The free-presentation universal central extension of a finite perfect group
is finite.  In particular, every finite nonabelian simple group has a
finite universal central extension.
-/

noncomputable section

open scoped IsMulCommutative

universe u

namespace McKayConjecture
namespace GroupTheory

variable {S : Type u} [Group S]

/-- Every finite perfect group has a finite universal central
extension. -/
theorem finite_universalCentralExtension_exists
    [Finite S]
    (hperfect : Group.IsPerfect S) :
    ∃ (U : Type u) (_ : Group U) (_ : Finite U),
      Nonempty (UniversalCentralExtension U S) := by
  let E :
      UniversalCentralExtension
        (FreePresentation.Cover S) S :=
    FreePresentation.universalCentralExtension
      hperfect
  let finiteCover :
      Finite (FreePresentation.Cover S) :=
    E.toCentralExtension.finite_source
      E.sourcePerfect
  exact
    ⟨FreePresentation.Cover S,
      inferInstance, finiteCover, ⟨E⟩⟩

/-- Every finite nonabelian simple group has a finite universal central
extension. -/
theorem finite_universalCentralExtension_exists_of_isSimpleGroup
    [Finite S]
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S) :
    ∃ (U : Type u) (_ : Group U) (_ : Finite U),
      Nonempty (UniversalCentralExtension U S) :=
  finite_universalCentralExtension_exists
    (isPerfect_of_isSimpleGroup hs hnoncomm)

end GroupTheory
end McKayConjecture
