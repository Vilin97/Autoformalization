/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationModuleBasis
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Decomposing a permutation module into orbit modules

A permutation basis splits canonically according to the orbits of its
indexing `P`-set.  This file constructs the corresponding invariant
submodules, gives each one its transitive orbit basis, and proves that
the family is an internal direct sum with supremum the whole module.
-/

noncomputable section

namespace Representation
namespace PermutationModuleBasis

variable {k P V ι : Type}
variable [Field k] [Group P]
variable [AddCommGroup V] [Module k V]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [MulAction P ι]

variable (B : PermutationModuleBasis
  (k := k) (P := P) (V := V) (ι := ι))

local notation "ρ" => B.representation
local notation "Ω" => MulAction.orbitRel.Quotient P ι

noncomputable local instance orbitDecompositionQuotientDecidableEq :
    DecidableEq Ω :=
  Classical.decEq Ω

/-- The span of the permutation-basis vectors belonging to one
`P`-orbit. -/
def orbitSubmodule (ω : Ω) : Submodule k V :=
  Submodule.span k
    (Set.range fun i : ω.orbit => B.basis (i : ι))

omit [SMulCommClass P k V] in
/-- The orbit submodule described as the span of the image of the
corresponding subset of basis indices. -/
theorem orbitSubmodule_eq_span_image (ω : Ω) :
    B.orbitSubmodule ω =
      Submodule.span k (B.basis '' ω.orbit) := by
  apply congrArg (Submodule.span k)
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.property, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

/-- An orbit span is invariant under the group action. -/
def orbitSubrepresentation (ω : Ω) :
    Subrepresentation ρ where
  toSubmodule := B.orbitSubmodule ω
  apply_mem_toSubmodule := by
    intro g v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨i, rfl⟩ := hv
        apply Submodule.subset_span
        refine ⟨g • i, ?_⟩
        change B.basis ((g • i : ω.orbit) : ι) =
          g • B.basis (i : ι)
        rw [B.smul_basis]
        exact congrArg B.basis
          MulAction.orbitRel.Quotient.orbit.coe_smul
    | zero =>
        simp
    | add x y _ _ hx hy =>
        simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul c x _ hx =>
        simpa only [map_smul] using Submodule.smul_mem _ c hx

/-- The basis of an orbit submodule indexed by the orbit itself. -/
def orbitBasis (ω : Ω) :
    Module.Basis ω.orbit k (B.orbitSubmodule ω) :=
  Module.Basis.span (B.basis.linearIndependent.comp
    (fun i : ω.orbit => (i : ι)) Subtype.val_injective)

omit [SMulCommClass P k V] in
@[simp]
theorem orbitBasis_coe (ω : Ω) (i : ω.orbit) :
    (B.orbitBasis ω i : V) = B.basis (i : ι) := by
  exact Module.Basis.coe_span_apply _ i

/-- The orbit basis is permuted transitively by the restricted
representation. -/
theorem orbitBasis_action (ω : Ω) (g : P) (i : ω.orbit) :
    (B.orbitSubrepresentation ω).toRepresentation g
        (B.orbitBasis ω i) =
      B.orbitBasis ω (g • i) := by
  dsimp only [orbitSubrepresentation,
    Subrepresentation.toRepresentation]
  apply Subtype.ext
  change g • (B.orbitBasis ω i : V) =
    (B.orbitBasis ω (g • i) : V)
  rw [B.orbitBasis_coe, B.orbitBasis_coe, B.smul_basis]
  exact congrArg B.basis
    MulAction.orbitRel.Quotient.orbit.coe_smul

/-- The restricted group action on an orbit submodule.  This is
provided as a definition, rather than a global instance, because it
depends on the chosen permutation basis. -/
@[instance_reducible]
def orbitDistribMulAction (ω : Ω) :
    DistribMulAction P (B.orbitSubmodule ω) where
  smul g x :=
    (B.orbitSubrepresentation ω).toRepresentation g x
  one_smul x := by
    apply Subtype.ext
    change ρ 1 (x : V) = (x : V)
    simp
  mul_smul g h x := by
    apply Subtype.ext
    change ρ (g * h) (x : V) =
      ρ g (ρ h (x : V))
    simp only [map_mul, Module.End.mul_apply]
  smul_zero g := by
    apply Subtype.ext
    change ρ g (0 : V) = 0
    exact map_zero (ρ g)
  smul_add g x y := by
    apply Subtype.ext
    change ρ g ((x : V) + (y : V)) =
      ρ g (x : V) + ρ g (y : V)
    exact map_add (ρ g) (x : V) (y : V)

/-- Scalar multiplication by the group and by the coefficient field
commute on an orbit submodule. -/
theorem orbitSMulCommClass (ω : Ω) :
    letI := B.orbitDistribMulAction ω
    SMulCommClass P k (B.orbitSubmodule ω) := by
  letI := B.orbitDistribMulAction ω
  constructor
  intro g c x
  apply Subtype.ext
  change ρ g (c • (x : V)) = c • ρ g (x : V)
  exact map_smul (ρ g) c (x : V)

/-- Each orbit submodule carries a permutation basis indexed by that
single, transitive orbit. -/
def orbitPermutationModuleBasis (ω : Ω) :
    letI := B.orbitDistribMulAction ω
    letI := B.orbitSMulCommClass ω
    PermutationModuleBasis
      (k := k) (P := P) (V := B.orbitSubmodule ω)
      (ι := ω.orbit) := by
  letI := B.orbitDistribMulAction ω
  letI := B.orbitSMulCommClass ω
  exact
    { basis := B.orbitBasis ω
      smul_basis := B.orbitBasis_action ω }

omit [SMulCommClass P k V] in
/-- The orbit submodules are independent. -/
theorem orbitSubmodules_iSupIndep :
    iSupIndep B.orbitSubmodule := by
  intro ω
  rw [B.orbitSubmodule_eq_span_image]
  have hother :
      (⨆ τ : Ω, ⨆ (_ : τ ≠ ω), B.orbitSubmodule τ) =
        Submodule.span k (B.basis '' ω.orbitᶜ) := by
    apply le_antisymm
    · refine iSup_le fun τ => iSup_le fun hτω => ?_
      rw [B.orbitSubmodule_eq_span_image]
      apply Submodule.span_mono
      rintro _ ⟨i, hi, rfl⟩
      refine ⟨i, ?_, rfl⟩
      intro hiω
      apply hτω
      exact
        ((MulAction.orbitRel.Quotient.mem_orbit).mp hi).symm.trans
          ((MulAction.orbitRel.Quotient.mem_orbit).mp hiω)
    · rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      have hq : (Quotient.mk'' i : Ω) ≠ ω := by
        intro h
        exact hi ((MulAction.orbitRel.Quotient.mem_orbit).mpr h)
      refine (le_iSup (fun τ : Ω =>
        ⨆ (_ : τ ≠ ω), B.orbitSubmodule τ)
          (Quotient.mk'' i)) ?_
      refine (le_iSup (fun _ : (Quotient.mk'' i : Ω) ≠ ω =>
        B.orbitSubmodule (Quotient.mk'' i)) hq) ?_
      rw [B.orbitSubmodule_eq_span_image]
      exact Submodule.subset_span
        ⟨i, (MulAction.orbitRel.Quotient.mem_orbit).mpr rfl, rfl⟩
  rw [hother]
  exact B.basis.linearIndependent.disjoint_span_image
    disjoint_compl_right

omit [SMulCommClass P k V] in
/-- The orbit submodules span the whole permutation module. -/
theorem iSup_orbitSubmodule_eq_top :
    ⨆ ω : Ω, B.orbitSubmodule ω = ⊤ := by
  simp_rw [B.orbitSubmodule_eq_span_image]
  rw [← Submodule.span_iUnion]
  have horbits : ⋃ ω : Ω, ω.orbit = (Set.univ : Set ι) := by
    ext i
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨Quotient.mk'' i,
      (MulAction.orbitRel.Quotient.mem_orbit).mpr rfl⟩
  rw [← Set.image_iUnion, horbits, Set.image_univ]
  exact B.basis.span_eq

omit [SMulCommClass P k V] in
/-- The permutation module is the internal direct sum of its orbit
submodules. -/
theorem orbitSubmodules_isInternal :
    DirectSum.IsInternal B.orbitSubmodule := by
  classical
  exact
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (orbitSubmodules_iSupIndep B) (iSup_orbitSubmodule_eq_top B)

/-- The canonical linear projection from the permutation module onto
one orbit factor, obtained from the internal direct sum
decomposition. -/
def orbitComponent (ω : Ω) :
    V →ₗ[k] B.orbitSubmodule ω :=
  (DirectSum.component k Ω
    (fun τ : Ω => (B.orbitSubmodule τ : Type)) ω).comp
    (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap B.orbitSubmodule)
      B.orbitSubmodules_isInternal).symm.toLinearMap

omit [SMulCommClass P k V] in
/-- On its own orbit factor, the canonical component projection is
the identity. -/
@[simp]
theorem orbitComponent_of_mem
    {ω : Ω} {v : V} (hv : v ∈ B.orbitSubmodule ω) :
    B.orbitComponent ω v = ⟨v, hv⟩ := by
  unfold orbitComponent
  simp only [LinearMap.comp_apply]
  rw [← DirectSum.apply_eq_component]
  exact B.orbitSubmodules_isInternal.ofBijective_coeLinearMap_of_mem hv

omit [SMulCommClass P k V] in
/-- A vector in a different orbit factor has zero canonical
component. -/
theorem orbitComponent_of_mem_ne
    {τ ω : Ω} (hτω : τ ≠ ω)
    {v : V} (hv : v ∈ B.orbitSubmodule τ) :
    B.orbitComponent ω v = 0 := by
  unfold orbitComponent
  simp only [LinearMap.comp_apply]
  rw [← DirectSum.apply_eq_component]
  exact
    B.orbitSubmodules_isInternal.ofBijective_coeLinearMap_of_mem_ne
      hτω hv

/-- The `(ω, τ)` block of a linear endomorphism with respect to the
orbit decomposition. -/
def orbitBlock (e : Module.End k V) (ω τ : Ω) :
    B.orbitSubmodule τ →ₗ[k] B.orbitSubmodule ω :=
  (B.orbitComponent ω).comp
    (e.comp (B.orbitSubmodule τ).subtype)

omit [SMulCommClass P k V] in
@[simp]
theorem orbitBlock_apply
    (e : Module.End k V) (ω τ : Ω)
    (v : B.orbitSubmodule τ) :
    B.orbitBlock e ω τ v = B.orbitComponent ω (e v) :=
  rfl

omit [SMulCommClass P k V] in
/-- A diagonal block of the identity endomorphism is the identity. -/
@[simp]
theorem orbitBlock_id_self (ω : Ω) :
    B.orbitBlock LinearMap.id ω ω = LinearMap.id := by
  ext v
  change ((B.orbitComponent ω) (v : V) : V) = (v : V)
  exact congrArg Subtype.val
    (B.orbitComponent_of_mem v.property)

omit [SMulCommClass P k V] in
/-- An off-diagonal block of the identity endomorphism is zero. -/
theorem orbitBlock_id_eq_zero_of_ne
    {ω τ : Ω} (hτω : τ ≠ ω) :
    B.orbitBlock LinearMap.id ω τ = 0 := by
  ext v
  change ((B.orbitComponent ω) (v : V) : V) = 0
  exact congrArg Subtype.val
    (B.orbitComponent_of_mem_ne hτω v.property)

end PermutationModuleBasis
end Representation
