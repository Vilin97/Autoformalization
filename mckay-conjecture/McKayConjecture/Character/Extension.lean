/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Inertia
import McKayConjecture.Character.Realization
import McKayConjecture.Character.Restriction

/-!
# Extensions of irreducible characters

An irreducible character of `H` extends along a homomorphism `f : H →* G`
when it is the pullback of an irreducible character of `G`.  The generic
definition is useful for chains of subgroups; the specialization to a normal
subgroup and its inertia group gives the usual notion of maximal
extendibility.

This file deliberately treats extension as equality of character values, not
as equality of chosen representation carriers.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type u} {H : Type v} {K : Type w}
variable [Group G] [Group H] [Group K]

/-- `ψ` extends `χ` along `f` if restriction of the values of `ψ` along
`f : H →* G` is exactly `χ`. -/
def IsExtensionAlong (f : H →* G)
    (χ : IrreducibleCharacter H) (ψ : IrreducibleCharacter G) : Prop :=
  ∀ h : H, ψ.values (f h) = χ.values h

namespace IsExtensionAlong

variable {f : H →* G} {χ : IrreducibleCharacter H}
  {ψ : IrreducibleCharacter G}

@[simp]
theorem value (hψ : IsExtensionAlong f χ ψ) (h : H) :
    ψ.values (f h) = χ.values h :=
  hψ h

/-- Extension preserves character degree. -/
theorem degree_eq (hψ : IsExtensionAlong f χ ψ) :
    ψ.degree = χ.degree := by
  apply Nat.cast_injective (R := ℂ)
  rw [← ψ.value_one, ← χ.value_one]
  simpa using hψ 1

/-- Consequently, extension preserves the `p'`-degree predicate. -/
theorem isPPrimeDegree_iff (hψ : IsExtensionAlong f χ ψ) (p : ℕ) :
    ψ.IsPPrimeDegree p ↔ χ.IsPPrimeDegree p := by
  simp only [IrreducibleCharacter.IsPPrimeDegree, hψ.degree_eq]

/-- The character of the chosen realization of an extension restricts to
the values of the character being extended. -/
theorem realization_character (hψ : IsExtensionAlong f χ ψ) :
    (FDRep.res f ψ.realization).character = χ.values := by
  funext h
  rw [FDRep.res_character_apply, ψ.realization_character]
  exact hψ h

/-- Every character is an extension of itself along the identity. -/
@[simp]
theorem refl (χ : IrreducibleCharacter G) :
    IsExtensionAlong (MonoidHom.id G) χ χ := by
  intro g
  rfl

/-- Extensions compose along a chain of homomorphisms. -/
theorem trans {g : K →* H} {θ : IrreducibleCharacter K}
    (hψ : IsExtensionAlong f χ ψ)
    (hχ : IsExtensionAlong g θ χ) :
    IsExtensionAlong (f.comp g) θ ψ := by
  intro k
  exact (hψ (g k)).trans (hχ k)

/-- Pullback along a group isomorphism is an extension along that
isomorphism. -/
theorem comap (e : H ≃* G) (ψ : IrreducibleCharacter G) :
    IsExtensionAlong (e : H →* G) (ψ.comap e) ψ := by
  intro h
  rfl

end IsExtensionAlong

section Subgroup

variable {G : Type u} [Group G]

/-- The usual subgroup specialization of character extension. -/
abbrev IsExtension
    (N : Subgroup G) (χ : IrreducibleCharacter N)
    (ψ : IrreducibleCharacter G) : Prop :=
  IsExtensionAlong N.subtype χ ψ

namespace IsExtension

variable {N : Subgroup G} {χ : IrreducibleCharacter N}
  {ψ : IrreducibleCharacter G}

@[simp]
theorem value (hψ : IsExtension N χ ψ) (n : N) :
    ψ.values n.1 = χ.values n :=
  hψ n

theorem degree_eq (hψ : IsExtension N χ ψ) :
    ψ.degree = χ.degree :=
  IsExtensionAlong.degree_eq hψ

theorem isPPrimeDegree_iff (hψ : IsExtension N χ ψ) (p : ℕ) :
    ψ.IsPPrimeDegree p ↔ χ.IsPPrimeDegree p :=
  IsExtensionAlong.isPPrimeDegree_iff hψ p

end IsExtension

end Subgroup

section Inertia

variable {G : Type u} [Group G]
variable (N : Subgroup G) [N.Normal]

/-- The canonical inclusion of a normal subgroup in the inertia group of one
of its irreducible characters. -/
def inertiaInclusion (χ : IrreducibleCharacter N) :
    N →* inertia N χ :=
  Subgroup.inclusion (subgroup_le_inertia N χ)

@[simp]
theorem inertiaInclusion_apply (χ : IrreducibleCharacter N) (n : N) :
    (inertiaInclusion N χ n : G) = n :=
  rfl

/-- An extension of `χ` to its inertia group. -/
def IsInertiaExtension (χ : IrreducibleCharacter N)
    (ψ : IrreducibleCharacter (inertia N χ)) : Prop :=
  IsExtensionAlong (inertiaInclusion N χ) χ ψ

/-- A normal subgroup is maximally extendible in `G` if every irreducible
character of the subgroup extends to its inertia group. -/
def IsMaximallyExtendible : Prop :=
  ∀ χ : IrreducibleCharacter N,
    ∃ ψ : IrreducibleCharacter (inertia N χ),
      IsInertiaExtension N χ ψ

/-- A simultaneous choice of inertia-group extensions.  No equivariance is
asserted at this layer; that extra structure belongs in an equivariant
extension map. -/
structure ExtensionMap where
  /-- The chosen extension of each irreducible character. -/
  extension :
    ∀ χ : IrreducibleCharacter N,
      IrreducibleCharacter (inertia N χ)
  /-- Each chosen character really restricts to its source. -/
  isExtension :
    ∀ χ : IrreducibleCharacter N,
      IsInertiaExtension N χ (extension χ)

namespace ExtensionMap

variable {N}

/-- An extension map witnesses maximal extendibility. -/
theorem maximallyExtendible (E : ExtensionMap N) :
    IsMaximallyExtendible N := by
  intro χ
  exact ⟨E.extension χ, E.isExtension χ⟩

/-- Maximal extendibility supplies an extension map by simultaneous
classical choice. -/
def ofMaximallyExtendible (h : IsMaximallyExtendible N) :
    ExtensionMap N where
  extension χ := Classical.choose (h χ)
  isExtension χ := Classical.choose_spec (h χ)

/-- Maximal extendibility is equivalent to the existence of an extension
map. -/
theorem nonempty_iff_maximallyExtendible :
    Nonempty (ExtensionMap N) ↔ IsMaximallyExtendible N := by
  constructor
  · rintro ⟨E⟩
    exact E.maximallyExtendible
  · intro h
    exact ⟨ofMaximallyExtendible h⟩

@[simp]
theorem degree_eq (E : ExtensionMap N)
    (χ : IrreducibleCharacter N) :
    (E.extension χ).degree = χ.degree :=
  (E.isExtension χ).degree_eq

@[simp]
theorem isPPrimeDegree_iff (E : ExtensionMap N)
    (χ : IrreducibleCharacter N) (p : ℕ) :
    (E.extension χ).IsPPrimeDegree p ↔ χ.IsPPrimeDegree p :=
  (E.isExtension χ).isPPrimeDegree_iff p

end ExtensionMap

end Inertia

end IrreducibleCharacter

/-! ## Stable orbit transversals -/

/-- A subset meeting every `M`-orbit in exactly one point. -/
structure OrbitTransversal
    (M : Type u) (X : Type v) [Group M] [MulAction M X] where
  /-- The chosen set of representatives. -/
  representatives : Set X
  /-- Every orbit has a representative. -/
  exists_smul_mem : ∀ x : X, ∃ m : M, m • x ∈ representatives
  /-- Two representatives in the same orbit coincide. -/
  eq_of_mem_orbit :
    ∀ {x y : X}, x ∈ representatives → y ∈ representatives →
      y ∈ MulAction.orbit M x → x = y

/-- An orbit transversal stable under a second action.  In applications the
second group is an outer automorphism group normalizing the first action. -/
structure StableOrbitTransversal
    (M : Type u) (A : Type v) (X : Type w)
    [Group M] [Group A] [MulAction M X] [MulAction A X]
    extends OrbitTransversal M X where
  /-- The set of representatives is stable under the outer action. -/
  stable : ∀ a : A, ∀ {x : X},
    x ∈ representatives → a • x ∈ representatives

end McKayConjecture
