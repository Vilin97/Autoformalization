/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Extending an open-submanifold diffeomorphism by the identity

A diffeomorphism of an open submanifold can be extended by the identity when it is already the
identity off a closed subset contained in that open set.  The closed support condition is exactly
what makes the piecewise formula smooth across the frontier of the open set.

This is the patching operation needed for coordinate-ball implantations and radial changes inside
the explicit unlink tubes.  The proof is local: points in the open set use the given
diffeomorphism, while points outside its closed support have a neighborhood on which the extension
is literally the identity.
-/

@[expose] public section

open Function Set Topology
open TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω}

/-- The raw piecewise extension of an open-submanifold self-map by the ambient identity. -/
def extendOpenMapByIdentity (U : Opens M) (f : U → U) (x : M) : M :=
  by
    classical
    exact if hx : x ∈ U then (f ⟨x, hx⟩ : M) else x

@[simp]
theorem extendOpenMapByIdentity_of_mem (U : Opens M) (f : U → U)
    {x : M} (hx : x ∈ U) :
    extendOpenMapByIdentity U f x = (f ⟨x, hx⟩ : M) := by
  simp [extendOpenMapByIdentity, hx]

@[simp]
theorem extendOpenMapByIdentity_of_not_mem (U : Opens M) (f : U → U)
    {x : M} (hx : x ∉ U) :
    extendOpenMapByIdentity U f x = x := by
  simp [extendOpenMapByIdentity, hx]

/-- The extension agrees with the given map after restriction to its open domain. -/
theorem extendOpenMapByIdentity_coe (U : Opens M) (f : U → U) (x : U) :
    extendOpenMapByIdentity U f x.1 = (f x : M) := by
  simp [extendOpenMapByIdentity, x.2]

/-- If `f` is the identity off `K` inside `U`, its ambient extension fixes the complement of
`K` pointwise. -/
theorem extendOpenMapByIdentity_eq_self_of_not_mem
    (U : Opens M) (K : Set M) (f : U → U)
    (hfix : ∀ z : U, z.1 ∉ K → f z = z) {x : M} (hx : x ∉ K) :
    extendOpenMapByIdentity U f x = x := by
  by_cases hxU : x ∈ U
  · rw [extendOpenMapByIdentity_of_mem U f hxU]
    exact congrArg Subtype.val (hfix ⟨x, hxU⟩ hx)
  · exact extendOpenMapByIdentity_of_not_mem U f hxU

/-- Fixing the complement of `K` is inherited by the inverse diffeomorphism. -/
theorem Diffeomorph.symm_eq_self_of_eq_self_off
    (U : Opens M) (K : Set M) (e : U ≃ₘ^n⟮I, I⟯ U)
    (hfix : ∀ z : U, z.1 ∉ K → e z = z) (z : U) (hz : z.1 ∉ K) :
    e.symm z = z := by
  apply e.injective
  exact (e.apply_symm_apply z).trans (hfix z hz).symm

/-- Smoothness of the identity extension.  The hypotheses say that `K` is a closed support
contained in the open coordinate domain `U`. -/
theorem contMDiff_extendOpenMapByIdentity
    (U : Opens M) (K : Set M) (f : U → U)
    (hf : ContMDiff I I n f) (hKclosed : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ z : U, z.1 ∉ K → f z = z) :
    ContMDiff I I n (extendOpenMapByIdentity U f) := by
  intro x
  by_cases hxU : x ∈ U
  · apply (contMDiffAt_subtype_iff (I := I) (I' := I)
      (U := U) (f := extendOpenMapByIdentity U f) (x := ⟨x, hxU⟩)).mp
    have hopen : ContMDiff I I n (fun z : U ↦ (f z : M)) :=
      contMDiff_subtype_val.comp hf
    apply hopen.contMDiffAt.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun z ↦ by
      exact extendOpenMapByIdentity_coe U f z
  · have hxK : x ∉ K := fun hx ↦ hxU (hKU hx)
    apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [hKclosed.isOpen_compl.mem_nhds hxK] with y hy
    exact extendOpenMapByIdentity_eq_self_of_not_mem U K f hfix hy

/-- Extend a diffeomorphism of an open submanifold by the identity outside the open set.  Closed
support strictly inside the open set supplies smoothness across its frontier. -/
def extendOpenDiffeomorphByIdentity
    (U : Opens M) (K : Set M) (e : U ≃ₘ^n⟮I, I⟯ U)
    (hKclosed : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ z : U, z.1 ∉ K → e z = z) : M ≃ₘ^n⟮I, I⟯ M where
  toFun := extendOpenMapByIdentity U e
  invFun := extendOpenMapByIdentity U e.symm
  left_inv x := by
    by_cases hxU : x ∈ U
    · rw [extendOpenMapByIdentity_of_mem U e hxU]
      rw [extendOpenMapByIdentity_of_mem U e.symm (e ⟨x, hxU⟩).2]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hxU⟩)
    · rw [extendOpenMapByIdentity_of_not_mem U e hxU,
        extendOpenMapByIdentity_of_not_mem U e.symm hxU]
  right_inv x := by
    by_cases hxU : x ∈ U
    · rw [extendOpenMapByIdentity_of_mem U e.symm hxU]
      rw [extendOpenMapByIdentity_of_mem U e (e.symm ⟨x, hxU⟩).2]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hxU⟩)
    · rw [extendOpenMapByIdentity_of_not_mem U e.symm hxU,
        extendOpenMapByIdentity_of_not_mem U e hxU]
  contMDiff_toFun :=
    contMDiff_extendOpenMapByIdentity U K e e.contMDiff hKclosed hKU hfix
  contMDiff_invFun :=
    contMDiff_extendOpenMapByIdentity U K e.symm e.symm.contMDiff hKclosed hKU
      (Diffeomorph.symm_eq_self_of_eq_self_off U K e hfix)

@[simp]
theorem extendOpenDiffeomorphByIdentity_apply_of_mem
    (U : Opens M) (K : Set M) (e : U ≃ₘ^n⟮I, I⟯ U)
    (hKclosed : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ z : U, z.1 ∉ K → e z = z) {x : M} (hx : x ∈ U) :
    extendOpenDiffeomorphByIdentity U K e hKclosed hKU hfix x = (e ⟨x, hx⟩ : M) :=
  extendOpenMapByIdentity_of_mem U e hx

@[simp]
theorem extendOpenDiffeomorphByIdentity_apply_of_not_mem
    (U : Opens M) (K : Set M) (e : U ≃ₘ^n⟮I, I⟯ U)
    (hKclosed : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ z : U, z.1 ∉ K → e z = z) {x : M} (hx : x ∉ K) :
    extendOpenDiffeomorphByIdentity U K e hKclosed hKU hfix x = x :=
  extendOpenMapByIdentity_eq_self_of_not_mem U K e hfix hx

/-- The extension is supported in the declared closed set. -/
theorem extendOpenDiffeomorphByIdentity_supported
    (U : Opens M) (K : Set M) (e : U ≃ₘ^n⟮I, I⟯ U)
    (hKclosed : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ z : U, z.1 ∉ K → e z = z) :
    ∀ ⦃x : M⦄, x ∉ K →
      extendOpenDiffeomorphByIdentity U K e hKclosed hKU hfix x = x :=
  fun _ hx ↦ extendOpenDiffeomorphByIdentity_apply_of_not_mem
    U K e hKclosed hKU hfix hx

end SplittingSpheres
