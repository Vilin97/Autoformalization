/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import McKayConjecture.Character.EquivariantExtension

/-!
# Automorphisms and inertia-group extensions

An ambient automorphism stabilizing a normal subgroup transports a character
of that subgroup, its inertia group, and every extension to that inertia
group.  This file constructs the resulting group equivalence between the two
inertia groups and proves the exact restriction formula for transported
extensions.
-/

noncomputable section

open scoped Pointwise

universe u

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type u} [Group G]
variable (N : Subgroup G) [N.Normal]

/-- The ambient automorphisms preserving `N`. -/
abbrev NormalSubgroupAutStabilizer : Subgroup (MulAut G) :=
  MulAction.stabilizer (MulAut G) N

namespace NormalSubgroupAutStabilizer

variable {N}

omit [N.Normal] in
@[simp]
theorem mem_iff (a : MulAut G) :
    a ∈ NormalSubgroupAutStabilizer N ↔ a • N = N :=
  MulAction.mem_stabilizer_iff

omit [N.Normal] in
/-- An automorphism stabilizing `N` maps `N` to itself. -/
theorem map_subgroup_eq (a : NormalSubgroupAutStabilizer N) :
    N.map (a.1 : G →* G) = N := by
  have h := MulAction.mem_stabilizer_iff.mp a.2
  rw [Subgroup.pointwise_smul_def] at h
  calc
    N.map (a.1 : G →* G) =
        N.map (MulDistribMulAction.toMonoidEnd (MulAut G) G a.1) := by
      congr 1
    _ = N := h

/-- Restrict an ambient automorphism stabilizing `N` to `N`. -/
def restrict (a : NormalSubgroupAutStabilizer N) : MulAut N where
  toFun x :=
    ⟨a.1 x.1, by
      have hx : a.1 x.1 ∈ N.map (a.1 : G →* G) :=
        Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩
      exact (congrArg (fun K : Subgroup G ↦ a.1 x.1 ∈ K)
        (map_subgroup_eq a)).mp hx⟩
  invFun x :=
    ⟨a.1.symm x.1, by
      change (a⁻¹).1 x.1 ∈ N
      have hx : (a⁻¹).1 x.1 ∈ N.map ((a⁻¹).1 : G →* G) :=
        Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩
      exact (congrArg (fun K : Subgroup G ↦ (a⁻¹).1 x.1 ∈ K)
        (map_subgroup_eq a⁻¹)).mp hx⟩
  left_inv x := by
    apply Subtype.ext
    exact a.1.symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact a.1.apply_symm_apply x.1
  map_mul' x y := by
    apply Subtype.ext
    exact a.1.map_mul x.1 y.1

omit [N.Normal] in
@[simp]
theorem restrict_apply_coe
    (a : NormalSubgroupAutStabilizer N) (n : N) :
    ((restrict a n : N) : G) = a.1 n.1 :=
  rfl

omit [N.Normal] in
@[simp]
theorem restrict_symm_apply_coe
    (a : NormalSubgroupAutStabilizer N) (n : N) :
    (((restrict a).symm n : N) : G) = a.1.symm n.1 :=
  rfl

/-- Restriction is a homomorphism on automorphism groups. -/
def restrictionHom :
    NormalSubgroupAutStabilizer N →* MulAut N where
  toFun := restrict
  map_one' := by
    ext n
    rfl
  map_mul' a b := by
    ext n
    rfl

omit [N.Normal] in
@[simp]
theorem restrictionHom_apply_coe
    (a : NormalSubgroupAutStabilizer N) (n : N) :
    ((restrictionHom (N := N) a n : N) : G) = a.1 n.1 :=
  rfl

end NormalSubgroupAutStabilizer

/-- The induced action on irreducible characters of `N`. -/
instance normalSubgroupAutStabilizerCharacterAction :
    MulAction (NormalSubgroupAutStabilizer N)
      (IrreducibleCharacter N) :=
  MulAction.compHom _
    (NormalSubgroupAutStabilizer.restrictionHom (N := N))

omit [N.Normal] in
@[simp]
theorem normalSubgroupAutStabilizer_smul_values
    (a : NormalSubgroupAutStabilizer N)
    (χ : IrreducibleCharacter N) (n : N) :
    (a • χ).values n =
      χ.values ((NormalSubgroupAutStabilizer.restrict a).symm n) :=
  rfl

/-- Conjugating a character and transporting it by an ambient automorphism
commute. -/
theorem conjBy_smul
    (a : NormalSubgroupAutStabilizer N) (g : G)
    (χ : IrreducibleCharacter N) :
    conjBy N (a.1 g) (a • χ) = a • conjBy N g χ := by
  apply IrreducibleCharacter.ext
  funext n
  simp only [conjBy_values, normalSubgroupAutStabilizer_smul_values]
  congr 1
  apply Subtype.ext
  simp only [MulAut.conjNormal_symm_apply,
    NormalSubgroupAutStabilizer.restrict_symm_apply_coe]
  exact a.1.symm.map_mul _ _ |>.trans (by
    rw [a.1.symm.map_mul, a.1.symm_apply_apply,
      a.1.symm.map_inv, a.1.symm_apply_apply])

/-- An ambient automorphism sends the inertia group of `χ` onto the inertia
group of the transported character. -/
theorem map_inertia_eq
    (a : NormalSubgroupAutStabilizer N)
    (χ : IrreducibleCharacter N) :
    (inertia N χ).map (a.1 : G →* G) = inertia N (a • χ) := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    rw [mem_inertia_iff] at hx ⊢
    calc
      conjBy N (a.1 x) (a • χ) =
          a • conjBy N x χ :=
        conjBy_smul N a x χ
      _ = a • χ := congrArg (a • ·) hx
  · intro hg
    rw [mem_inertia_iff] at hg
    refine Subgroup.mem_map.mpr
      ⟨a.1.symm g, ?_, a.1.apply_symm_apply g⟩
    rw [mem_inertia_iff]
    calc
      conjBy N (a.1.symm g) χ =
          a⁻¹ • conjBy N g (a • χ) := by
        simpa using conjBy_smul N a⁻¹ g (a • χ)
      _ = a⁻¹ • (a • χ) := congrArg (a⁻¹ • ·) hg
      _ = χ := inv_smul_smul a χ

/-- The canonical equivalence from `I_G(χ)` to `I_G(a • χ)`. -/
def inertiaEquiv
    (a : NormalSubgroupAutStabilizer N)
    (χ : IrreducibleCharacter N) :
    inertia N χ ≃* inertia N (a • χ) :=
  (a.1.subgroupMap (inertia N χ)).trans
    (MulEquiv.subgroupCongr (map_inertia_eq N a χ))

@[simp]
theorem inertiaEquiv_apply_coe
    (a : NormalSubgroupAutStabilizer N)
    (χ : IrreducibleCharacter N) (x : inertia N χ) :
    ((inertiaEquiv N a χ x : inertia N (a • χ)) : G) =
      a.1 x.1 :=
  rfl

@[simp]
theorem inertiaEquiv_symm_apply_coe
    (a : NormalSubgroupAutStabilizer N)
    (χ : IrreducibleCharacter N)
    (x : inertia N (a • χ)) :
    (((inertiaEquiv N a χ).symm x : inertia N χ) : G) =
      a.1.symm x.1 := by
  apply a.1.injective
  rw [a.1.apply_symm_apply]
  simpa using (inertiaEquiv_apply_coe N a χ
    ((inertiaEquiv N a χ).symm x)).symm

/-- Transport a character of an inertia group by an ambient automorphism. -/
def transportInertiaCharacter
    (a : NormalSubgroupAutStabilizer N)
    (x : InertiaCharacter N) :
    InertiaCharacter N :=
  ⟨a • x.source, x.extension.comap (inertiaEquiv N a x.source).symm⟩

@[simp]
theorem transportInertiaCharacter_source
    (a : NormalSubgroupAutStabilizer N)
    (x : InertiaCharacter N) :
    (transportInertiaCharacter N a x).source = a • x.source :=
  rfl

@[simp]
theorem transportInertiaCharacter_values
    (a : NormalSubgroupAutStabilizer N)
    (x : InertiaCharacter N)
    (g : inertia N (a • x.source)) :
    (transportInertiaCharacter N a x).extension.values g =
      x.extension.values ((inertiaEquiv N a x.source).symm g) :=
  rfl

/-- Transport by an ambient automorphism preserves the property of extending
the source character. -/
theorem transportInertiaCharacter_isExtension
    (a : NormalSubgroupAutStabilizer N)
    (x : InertiaCharacter N)
    (hx : x.IsExtension) :
    (transportInertiaCharacter N a x).IsExtension := by
  intro n
  change
    x.extension.values
        ((inertiaEquiv N a x.source).symm
          (inertiaInclusion N (a • x.source) n)) =
      (a • x.source).values n
  rw [normalSubgroupAutStabilizer_smul_values]
  convert hx ((NormalSubgroupAutStabilizer.restrict a).symm n) using 1
  apply congrArg x.extension.values
  apply Subtype.ext
  exact inertiaEquiv_symm_apply_coe N a x.source
    (inertiaInclusion N (a • x.source) n)

/-- Transport by the identity automorphism is the identity on the dependent
family of inertia characters. -/
theorem transportInertiaCharacter_one
    (x : InertiaCharacter N) :
    transportInertiaCharacter N
      (1 : NormalSubgroupAutStabilizer N) x = x := by
  rcases x with ⟨χ, ψ⟩
  apply Sigma.ext (one_smul _ χ)
  apply heq_of_eq
  apply IrreducibleCharacter.ext
  funext g
  change ψ.values ((inertiaEquiv N 1 χ).symm g) = ψ.values g
  congr 1

/-- Successive transports agree with transport by the product
automorphism. -/
theorem transportInertiaCharacter_mul
    (a b : NormalSubgroupAutStabilizer N)
    (x : InertiaCharacter N) :
    transportInertiaCharacter N (a * b) x =
      transportInertiaCharacter N a
        (transportInertiaCharacter N b x) := by
  rcases x with ⟨χ, ψ⟩
  apply Sigma.ext (mul_smul a b χ)
  apply heq_of_eq
  apply IrreducibleCharacter.ext
  funext g
  change
    ψ.values ((inertiaEquiv N (a * b) χ).symm g) =
      ψ.values
        ((inertiaEquiv N b χ).symm
          ((inertiaEquiv N a (b • χ)).symm g))
  congr 1

/-- The natural action of ambient automorphisms stabilizing `N` on the
dependent family `Σ χ, Irr(I_G(χ))`. -/
instance normalSubgroupAutStabilizerInertiaCharacterAction :
    MulAction (NormalSubgroupAutStabilizer N)
      (InertiaCharacter N) where
  smul := transportInertiaCharacter N
  one_smul := transportInertiaCharacter_one N
  mul_smul := transportInertiaCharacter_mul N

@[simp]
theorem inertiaCharacter_smul_source
    (a : NormalSubgroupAutStabilizer N)
    (x : InertiaCharacter N) :
    (a • x).source = a • x.source :=
  rfl

@[simp]
theorem inertiaCharacter_smul_values
    (a : NormalSubgroupAutStabilizer N)
    (x : InertiaCharacter N)
    (g : inertia N (a • x.source)) :
    (a • x).extension.values g =
      x.extension.values ((inertiaEquiv N a x.source).symm g) :=
  rfl

/-- The canonical inertia-character action lies over the character action. -/
theorem inertiaCharacterAction_liesOver :
    InertiaActionLiesOver N
      (A := NormalSubgroupAutStabilizer N) :=
  inertiaCharacter_smul_source N

/-- The canonical inertia-character action preserves extension. -/
theorem inertiaCharacterAction_preservesExtensions :
    InertiaActionPreservesExtensions N
      (A := NormalSubgroupAutStabilizer N) := by
  intro a x hx
  exact transportInertiaCharacter_isExtension N a x hx

/-- An extension map equivariant under every ambient automorphism preserving
the normal subgroup. -/
abbrev AutomorphismEquivariantExtensionMap :=
  EquivariantExtensionMap N
    (inertiaCharacterAction_liesOver N)

/-- Existence of a fully automorphism-equivariant extension map. -/
def HasAutomorphismEquivariantExtensionMap : Prop :=
  Nonempty (AutomorphismEquivariantExtensionMap N)

namespace AutomorphismEquivariantExtensionMap

@[simp]
theorem map_smul
    (E : AutomorphismEquivariantExtensionMap N)
    (a : NormalSubgroupAutStabilizer N)
    (χ : IrreducibleCharacter N) :
    a • (⟨χ, E.extension χ⟩ : InertiaCharacter N) =
      ⟨a • χ, E.extension (a • χ)⟩ :=
  E.map_smul' a χ

/-- Automorphism-equivariant maximal extendibility implies ordinary maximal
extendibility. -/
theorem maximallyExtendible
    (E : AutomorphismEquivariantExtensionMap N) :
    IsMaximallyExtendible N :=
  E.toExtensionMap.maximallyExtendible

end AutomorphismEquivariantExtensionMap

end IrreducibleCharacter
end McKayConjecture
