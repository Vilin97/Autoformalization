/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GallagherCorrespondence
import McKayConjecture.Character.InertiaTopFibre
import McKayConjecture.CharacterTriple.Inertia

/-!
# Honest extensions on a full inertia group

When a normal-subgroup character has full inertia, an honest extension to
the ambient group pulls back along the canonical equivalence from the inertia
group to the ambient group.  The resulting character extends the canonical
internal copy used by `CharacterTriple.ofInertia`.

This small transport lemma lets factor-one extension constructions be used
directly with the canonical inertia-triple API.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple

open CliffordCorrespondence
open CliffordEquivalence

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal]
variable (theta : IrreducibleCharacter N)

noncomputable local instance inertiaTopExtensionFintypeG :
    Fintype G :=
  Fintype.ofFinite G

/-- Any honest extension of the canonical internal copy determines exactly
the canonical inertia character triple. -/
theorem extensionCharacterTriple_eq_ofInertia
    (psi :
      IrreducibleCharacter
        (IrreducibleCharacter.inertia N theta))
    (hpsi :
      IrreducibleCharacter.IsExtensionAlong
        (inertiaNormalCopy N theta).subtype
        (inertiaCopyCharacter N theta)
        psi) :
    IrreducibleCharacter.extensionCharacterTriple hpsi =
      ofInertia N theta := by
  unfold
    IrreducibleCharacter.extensionCharacterTriple
    ofInertia
  congr

/-- Pull an ambient extension back to a full inertia group. -/
def inertiaTopExtensionCharacter
    (hinertia :
      IrreducibleCharacter.inertia N theta = ⊤)
    (psi : IrreducibleCharacter G) :
    IrreducibleCharacter
      (IrreducibleCharacter.inertia N theta) :=
  psi.comap (inertiaTopEquiv N theta hinertia)

/-- The pulled-back ambient character extends the canonical internal copy
of the normal character in its inertia group. -/
theorem inertiaTopExtensionCharacter_isExtension
    (hinertia :
      IrreducibleCharacter.inertia N theta = ⊤)
    (psi : IrreducibleCharacter G)
    (hpsi :
      IrreducibleCharacter.IsExtensionAlong
        N.subtype theta psi) :
    IrreducibleCharacter.IsExtensionAlong
      (inertiaNormalCopy N theta).subtype
      (inertiaCopyCharacter N theta)
      (inertiaTopExtensionCharacter
        N theta hinertia psi) := by
  intro n
  change
    (psi.comap
      (inertiaTopEquiv N theta hinertia)).values
        ((inertiaNormalCopy N theta).subtype n) =
      (theta.comap
        (inertiaNormalCopyEquiv N theta)).values n
  rw [
    IrreducibleCharacter.comap_values,
    IrreducibleCharacter.comap_values
  ]
  change
    psi.values (n : G) =
      theta.values (inertiaNormalCopyEquiv N theta n)
  convert
    hpsi (inertiaNormalCopyEquiv N theta n)
    using 1
  rfl

/-- The extension character triple obtained from the full-inertia pullback
is the canonical inertia triple. -/
theorem extensionCharacterTriple_inertiaTopExtension_eq_ofInertia
    (hinertia :
      IrreducibleCharacter.inertia N theta = ⊤)
    (psi : IrreducibleCharacter G)
    (hpsi :
      IrreducibleCharacter.IsExtensionAlong
        N.subtype theta psi) :
    IrreducibleCharacter.extensionCharacterTriple
        (inertiaTopExtensionCharacter_isExtension
          N theta hinertia psi hpsi) =
      ofInertia N theta := by
  exact
    extensionCharacterTriple_eq_ofInertia
      N theta
      (inertiaTopExtensionCharacter
        N theta hinertia psi)
      (inertiaTopExtensionCharacter_isExtension
        N theta hinertia psi hpsi)

end CharacterTriple
end McKayConjecture
