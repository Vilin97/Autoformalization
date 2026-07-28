/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Extension

/-!
# Stable extendible character transversals

The local and global `A`-conditions used in inductive McKay arguments ask
for more than an orbit transversal: the representative set is stable under
an outer action, and every chosen representative extends to its inertia
group in a specified overgroup.

This file adds precisely that extension datum to
`StableOrbitTransversal`.  It is deliberately independent of finite
reductive groups and of type `D`.  The two actions are abstract because, in
applications, the orbit action and the outer stability action come from
different overgroups.
-/

noncomputable section

universe u v w

namespace McKayConjecture.InductiveMcKay

open McKayConjecture

variable {K : Type u} [Group K]
variable (N : Subgroup K) [N.Normal]
variable (M : Type v) (A : Type w)
variable [Group M] [Group A]
variable [MulAction M (IrreducibleCharacter N)]
variable [MulAction A (IrreducibleCharacter N)]

/-- A stable orbit transversal whose selected irreducible characters each
come with a chosen extension to their inertia group in `K`.

The extension is indexed by the subtype of representatives.  Thus the
structure does not make, or require, extension choices for characters
outside the transversal. -/
structure ExtendibleStableCharacterTransversal
    extends StableOrbitTransversal M A (IrreducibleCharacter N) where
  /-- The chosen inertia-group extension of a representative. -/
  extension :
    ∀ χ : {χ : IrreducibleCharacter N // χ ∈ representatives},
      IrreducibleCharacter (IrreducibleCharacter.inertia N χ.1)
  /-- Each chosen character really restricts to its representative. -/
  isExtension :
    ∀ χ : {χ : IrreducibleCharacter N // χ ∈ representatives},
      IrreducibleCharacter.IsInertiaExtension N χ.1 (extension χ)

namespace ExtendibleStableCharacterTransversal

variable {N M A}

/-- The subtype of characters selected by a stable transversal. -/
abbrev Representatives
    (T : ExtendibleStableCharacterTransversal N M A) :=
  {χ : IrreducibleCharacter N // χ ∈ T.representatives}

/-- Regard outer stability as an action on the representative subtype. -/
@[instance_reducible]
def representativeAction
    (T : ExtendibleStableCharacterTransversal N M A) :
    MulAction A T.Representatives where
  smul a χ := ⟨a • χ.1, T.stable a χ.2⟩
  one_smul χ := by
    apply Subtype.ext
    exact one_smul A χ.1
  mul_smul a b χ := by
    apply Subtype.ext
    exact mul_smul a b χ.1

/-- The extension chosen at a character together with a proof that it is a
representative. -/
def extensionAt
    (T : ExtendibleStableCharacterTransversal N M A)
    (χ : IrreducibleCharacter N) (hχ : χ ∈ T.representatives) :
    IrreducibleCharacter (IrreducibleCharacter.inertia N χ) :=
  T.extension ⟨χ, hχ⟩

/-- The character returned by `extensionAt` is an inertia extension. -/
theorem extensionAt_isExtension
    (T : ExtendibleStableCharacterTransversal N M A)
    (χ : IrreducibleCharacter N) (hχ : χ ∈ T.representatives) :
    IrreducibleCharacter.IsInertiaExtension N χ
      (T.extensionAt χ hχ) :=
  T.isExtension ⟨χ, hχ⟩

/-- Every orbit contains a representative equipped with an inertia-group
extension. -/
theorem exists_smul_extension
    (T : ExtendibleStableCharacterTransversal N M A)
    (χ : IrreducibleCharacter N) :
    ∃ m : M,
      ∃ ψ : IrreducibleCharacter
          (IrreducibleCharacter.inertia N (m • χ)),
        m • χ ∈ T.representatives ∧
          IrreducibleCharacter.IsInertiaExtension N (m • χ) ψ := by
  obtain ⟨m, hm⟩ := T.exists_smul_mem χ
  exact ⟨m, T.extensionAt (m • χ) hm, hm,
    T.extensionAt_isExtension (m • χ) hm⟩

/-- Forget the chosen extensions and retain only the stable transversal. -/
def forgetExtensions
    (T : ExtendibleStableCharacterTransversal N M A) :
    StableOrbitTransversal M A (IrreducibleCharacter N) :=
  T.toStableOrbitTransversal

end ExtendibleStableCharacterTransversal

end McKayConjecture.InductiveMcKay
