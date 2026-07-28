/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AutomorphismInertia
import McKayConjecture.Character.ExtensionLinearTwist

/-!
# Equivariant extension maps compatible with twists

Condition `B(d)` uses an extension map with two independent compatibility
requirements.  It is equivariant for an outer normalizer action, and it
also commutes with an action by linear-character twists.

The character-theoretic carrier is necessarily dependent:

`Σ χ : Irr(N), Irr(I_K(χ))`.

The existing `EquivariantExtensionMap` handles the first action.  This file
adds a second, explicitly named twist action and requires the same graph
equivariance for it.  The actions themselves remain parameters: concrete
finite-reductive applications must construct the linear-character group,
its actions on source and inertia characters, and the proof that the latter
lies over the former.
-/

noncomputable section

universe u v w

namespace McKayConjecture.InductiveMcKay

open McKayConjecture
open McKayConjecture.IrreducibleCharacter

variable {K : Type u} [Group K]
variable (N : Subgroup K) [N.Normal]
variable {A : Type v} {T : Type w}
variable [Group A] [Group T]
variable [MulAction A (IrreducibleCharacter N)]
variable [MulAction A (InertiaCharacter N)]
variable [MulAction T (IrreducibleCharacter N)]
variable [MulAction T (InertiaCharacter N)]

/-- An outer-equivariant extension map which also commutes with a specified
group of twists.

`outerLiesOver` and `twistLiesOver` assert that both actions on the dependent
family have the expected source character.  In applications `T` is a group
of linear characters (often inflated from a quotient), and its two actions
must be supplied explicitly. -/
structure TwistCompatibleEquivariantExtensionMap
    (outerLiesOver : InertiaActionLiesOver N (A := A))
    (twistLiesOver : InertiaActionLiesOver N (A := T))
    extends EquivariantExtensionMap N outerLiesOver where
  /-- Twisting a chosen extension gives the chosen extension of the twisted
  source character. -/
  map_twist' :
    ∀ (t : T) (χ : IrreducibleCharacter N),
      t • (⟨χ, extension χ⟩ : InertiaCharacter N) =
        ⟨t • χ, extension (t • χ)⟩

namespace TwistCompatibleEquivariantExtensionMap

variable {N}
variable {outerLiesOver : InertiaActionLiesOver N (A := A)}
variable {twistLiesOver : InertiaActionLiesOver N (A := T)}

/-- Forget twist compatibility and retain outer equivariance. -/
def forgetTwists
    (E : TwistCompatibleEquivariantExtensionMap N
      outerLiesOver twistLiesOver) :
    EquivariantExtensionMap N outerLiesOver :=
  E.toEquivariantExtensionMap

/-- The same extension map, viewed as equivariant for the twist action. -/
def toTwistEquivariantExtensionMap
    (E : TwistCompatibleEquivariantExtensionMap N
      outerLiesOver twistLiesOver) :
    EquivariantExtensionMap N twistLiesOver where
  toExtensionMap := E.toExtensionMap
  map_smul' := E.map_twist'

@[simp]
theorem map_outer
    (E : TwistCompatibleEquivariantExtensionMap N
      outerLiesOver twistLiesOver)
    (a : A) (χ : IrreducibleCharacter N) :
    a • (⟨χ, E.extension χ⟩ : InertiaCharacter N) =
      ⟨a • χ, E.extension (a • χ)⟩ :=
  E.map_smul' a χ

@[simp]
theorem map_twist
    (E : TwistCompatibleEquivariantExtensionMap N
      outerLiesOver twistLiesOver)
    (t : T) (χ : IrreducibleCharacter N) :
    t • (⟨χ, E.extension χ⟩ : InertiaCharacter N) =
      ⟨t • χ, E.extension (t • χ)⟩ :=
  E.map_twist' t χ

/-- The graph of the extension map is stable under the outer action. -/
theorem graph_outer_stable
    (E : TwistCompatibleEquivariantExtensionMap N
      outerLiesOver twistLiesOver)
    (a : A) (x : InertiaCharacter N)
    (hx : x ∈ Set.range
      (fun χ : IrreducibleCharacter N ↦
        (⟨χ, E.extension χ⟩ : InertiaCharacter N))) :
    a • x ∈ Set.range
      (fun χ : IrreducibleCharacter N ↦
        (⟨χ, E.extension χ⟩ : InertiaCharacter N)) :=
  E.toEquivariantExtensionMap.graph_stable a x hx

/-- The graph of the extension map is stable under the twist action. -/
theorem graph_twist_stable
    (E : TwistCompatibleEquivariantExtensionMap N
      outerLiesOver twistLiesOver)
    (t : T) (x : InertiaCharacter N)
    (hx : x ∈ Set.range
      (fun χ : IrreducibleCharacter N ↦
        (⟨χ, E.extension χ⟩ : InertiaCharacter N))) :
    t • x ∈ Set.range
      (fun χ : IrreducibleCharacter N ↦
        (⟨χ, E.extension χ⟩ : InertiaCharacter N)) :=
  E.toTwistEquivariantExtensionMap.graph_stable t x hx

/-- Forgetting both equivariance laws leaves maximal extendibility. -/
theorem maximallyExtendible
    (E : TwistCompatibleEquivariantExtensionMap N
      outerLiesOver twistLiesOver) :
    IsMaximallyExtendible N :=
  E.toExtensionMap.maximallyExtendible

end TwistCompatibleEquivariantExtensionMap

end McKayConjecture.InductiveMcKay
