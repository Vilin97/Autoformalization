/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Extension

/-!
# Equivariant extension maps

The inertia group varies with the source character, so the natural carrier
for equivariance is the dependent sum

`Σ χ : Irr(N), Irr(I_G(χ))`.

This file packages the abstract equivariance interface independently of a
particular automorphism group.  Later finite-reductive constructions only
need to install the action induced by their automorphisms and prove that it
preserves the extension relation.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type u} [Group G]
variable (N : Subgroup G) [N.Normal]

/-- A character of an inertia group, indexed by the character of `N` whose
inertia group it is. -/
abbrev InertiaCharacter :=
  Σ χ : IrreducibleCharacter N,
    IrreducibleCharacter (inertia N χ)

namespace InertiaCharacter

/-- The source character indexing an inertia character. -/
abbrev source (x : InertiaCharacter N) : IrreducibleCharacter N :=
  x.1

/-- The character on the corresponding inertia group. -/
abbrev extension (x : InertiaCharacter N) :
    IrreducibleCharacter (inertia N x.source) :=
  x.2

/-- The dependent pair is an actual inertia extension. -/
def IsExtension (x : InertiaCharacter N) : Prop :=
  IsInertiaExtension N x.source x.extension

@[simp]
theorem isExtension_mk (χ : IrreducibleCharacter N)
    (ψ : IrreducibleCharacter (inertia N χ)) :
    IsExtension N ⟨χ, ψ⟩ ↔ IsInertiaExtension N χ ψ :=
  Iff.rfl

end InertiaCharacter

variable {A : Type v} [Group A]
variable [MulAction A (IrreducibleCharacter N)]
variable [MulAction A (InertiaCharacter N)]

/-- An action on the dependent family of inertia characters lies over the
given action on source characters. -/
def InertiaActionLiesOver : Prop :=
  ∀ (a : A) (x : InertiaCharacter N),
    (a • x).source = a • x.source

/-- An action on inertia characters preserves the assertion that the second
component extends the first. -/
def InertiaActionPreservesExtensions : Prop :=
  ∀ (a : A) (x : InertiaCharacter N),
    x.IsExtension → (a • x).IsExtension

/-- An extension map is equivariant when its graph in the dependent sum of
inertia characters is stable under the acting group. -/
structure EquivariantExtensionMap
    (hOver : InertiaActionLiesOver N (A := A))
    extends ExtensionMap N where
  /-- Acting on a chosen extension gives the chosen extension of the acted-on
  source character. -/
  map_smul' :
    ∀ (a : A) (χ : IrreducibleCharacter N),
      a • (⟨χ, extension χ⟩ : InertiaCharacter N) =
        ⟨a • χ, extension (a • χ)⟩

namespace EquivariantExtensionMap

variable {N} {hOver : InertiaActionLiesOver N (A := A)}

@[simp]
theorem map_smul (E : EquivariantExtensionMap N hOver)
    (a : A) (χ : IrreducibleCharacter N) :
    a • (⟨χ, E.extension χ⟩ : InertiaCharacter N) =
      ⟨a • χ, E.extension (a • χ)⟩ :=
  E.map_smul' a χ

/-- The chosen graph is a stable subset of the dependent family. -/
theorem graph_stable (E : EquivariantExtensionMap N hOver)
    (a : A) (x : InertiaCharacter N)
    (hx : x ∈ Set.range
      (fun χ : IrreducibleCharacter N ↦
        (⟨χ, E.extension χ⟩ : InertiaCharacter N))) :
    a • x ∈ Set.range
      (fun χ : IrreducibleCharacter N ↦
        (⟨χ, E.extension χ⟩ : InertiaCharacter N)) := by
  obtain ⟨χ, rfl⟩ := hx
  exact ⟨a • χ, (E.map_smul a χ).symm⟩

/-- Forgetting equivariance leaves maximal extendibility. -/
theorem maximallyExtendible (E : EquivariantExtensionMap N hOver) :
    IsMaximallyExtendible N :=
  E.toExtensionMap.maximallyExtendible

end EquivariantExtensionMap

end IrreducibleCharacter
end McKayConjecture
