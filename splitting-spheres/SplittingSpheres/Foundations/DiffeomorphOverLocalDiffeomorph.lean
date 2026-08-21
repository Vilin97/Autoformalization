/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothLocalDiffeomorphLift
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Diffeomorphisms detected through local diffeomorphisms

A homeomorphism between the total spaces of two local diffeomorphisms is a diffeomorphism if it
covers a diffeomorphism of their bases.  Smoothness in both directions is detected after composing
with the corresponding local diffeomorphism.

This is particularly useful for homeomorphisms between covering spaces equipped with the smooth
atlases pulled back from their bases: no formula for a local sheet or gauge needs to be
differentiated directly.
-/

@[expose] public section

open Function Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

universe uM uN uE uE' uX uX' uH uH' uK

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
variable {K : Type uH} [TopologicalSpace K]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace K M]

/-- Inclusion of an inherited open submanifold is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_opensSubtypeVal
    (I : ModelWithCorners ℝ C K) (U : TopologicalSpace.Opens M) :
    IsLocalDiffeomorph I I ∞ (Subtype.val : U → M) := by
  intro x
  let _ : Nonempty U := ⟨x⟩
  let hOpen : IsOpenEmbedding (Subtype.val : U → M) :=
    U.2.isOpenEmbedding_subtypeVal
  let oph : OpenPartialHomeomorph U M :=
    hOpen.toOpenPartialHomeomorph Subtype.val
  let phi : PartialDiffeomorph I I U M ∞ := {
    toPartialEquiv := oph.toPartialEquiv
    open_source := oph.open_source
    open_target := oph.open_target
    contMDiffOn_toFun := by
      simpa [oph] using
        (contMDiff_subtype_val : ContMDiff I I ∞
          (Subtype.val : U → M)).contMDiffOn
    contMDiffOn_invFun := by
      intro y hy
      apply (ContMDiffWithinAt.subtypeVal_comp_iff U oph.symm oph.target y).mp
      apply contMDiffWithinAt_id.congr
      · intro z hz
        exact oph.right_inv hz
      · exact oph.right_inv hy
  }
  have hx : x ∈ phi.source := by
    change x ∈ oph.source
    simp [oph]
  simpa [phi, oph] using (phi.isLocalDiffeomorphAt I I ∞ hx)

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {K' : Type uK} [TopologicalSpace K']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace K' N]

/-- Restrict a map to an open subset of its source and an open subset of its target. -/
def restrictToOpens (f : M → N) (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens N) (h : ∀ x : U, f x.1 ∈ V) : U → V :=
  fun x ↦ ⟨f x.1, h x⟩

@[simp]
theorem restrictToOpens_coe (f : M → N) (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens N) (h : ∀ x : U, f x.1 ∈ V) (x : U) :
    (restrictToOpens f U V h x : N) = f x.1 :=
  rfl

/-- Restricting a local diffeomorphism to open subsets of its source and target again gives a
local diffeomorphism. -/
theorem isLocalDiffeomorph_restrictToOpens
    (I : ModelWithCorners ℝ C K) (J : ModelWithCorners ℝ D K')
    (f : M → N) (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens N) (h : ∀ x : U, f x.1 ∈ V)
    (hf : IsLocalDiffeomorph I J ∞ f) :
    IsLocalDiffeomorph I J ∞ (restrictToOpens f U V h) := by
  intro x
  let hU := isLocalDiffeomorph_opensSubtypeVal I U x
  let hcomp : IsLocalDiffeomorphAt I J ∞ (f ∘ Subtype.val) x :=
    hU.comp J N (hf x.1)
  let v : V := restrictToOpens f U V h x
  let hV := isLocalDiffeomorph_opensSubtypeVal J V v
  let phiOne := Classical.choose hcomp
  let phi : PartialDiffeomorph I J U V ∞ := phiOne.trans hV.localInverse
  refine ⟨phi, ?_, ?_⟩
  · change x ∈ phiOne.source ∩ phiOne ⁻¹' hV.localInverse.source
    refine ⟨hcomp.choose_spec.1, ?_⟩
    change phiOne x ∈ hV.localInverse.source
    rw [← hcomp.choose_spec.2 hcomp.choose_spec.1]
    exact hV.localInverse_mem_source
  · intro y hy
    change restrictToOpens f U V h y = hV.localInverse (phiOne y)
    have hfy : phiOne y = f y.1 :=
      (hcomp.choose_spec.2 hy.1).symm
    have hy2 : phiOne y ∈ hV.localInverse.source := hy.2
    rw [hfy]
    apply Subtype.ext
    exact (hV.localInverse_right_inv (y := f y.1) (by rwa [← hfy])).symm

variable {A B : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  (I : ModelWithCorners ℝ A H) (J : ModelWithCorners ℝ B H')
  {E : Type uE} [TopologicalSpace E] [ChartedSpace H E]
  {E' : Type uE'} [TopologicalSpace E'] [ChartedSpace H' E']
  {X : Type uX} [TopologicalSpace X] [ChartedSpace H X]
  {X' : Type uX'} [TopologicalSpace X'] [ChartedSpace H' X']
  {n : ℕ∞ω}

/-- A homeomorphism of total spaces which covers a diffeomorphism of bases is a diffeomorphism,
provided both projections are local diffeomorphisms. -/
def diffeomorphOfHomeomorphOverDiffeomorph
    (p : E → X) (p' : E' → X')
    (hp : IsLocalDiffeomorph I I n p)
    (hp' : IsLocalDiffeomorph J J n p')
    (e : X ≃ₘ^n⟮I, J⟯ X') (F : E ≃ₜ E')
    (hproj : ∀ z, p' (F z) = e (p z)) :
    E ≃ₘ^n⟮I, J⟯ E' where
  toEquiv := F.toEquiv
  contMDiff_toFun := by
    apply contMDiff_of_comp_isLocalDiffeomorph I J J hp' F.continuous
    exact (e.contMDiff.comp hp.contMDiff).congr fun z ↦ by
      simpa only [comp_apply] using hproj z
  contMDiff_invFun := by
    apply contMDiff_of_comp_isLocalDiffeomorph J I I hp F.symm.continuous
    apply (e.symm.contMDiff.comp hp'.contMDiff).congr
    intro z
    change p (F.symm z) = e.symm (p' z)
    have h := congrArg e.symm (hproj (F.symm z))
    rw [F.apply_symm_apply, e.symm_apply_apply] at h
    exact h.symm

@[simp]
theorem diffeomorphOfHomeomorphOverDiffeomorph_apply
    (p : E → X) (p' : E' → X')
    (hp : IsLocalDiffeomorph I I n p)
    (hp' : IsLocalDiffeomorph J J n p')
    (e : X ≃ₘ^n⟮I, J⟯ X') (F : E ≃ₜ E')
    (hproj : ∀ z, p' (F z) = e (p z)) (z : E) :
    diffeomorphOfHomeomorphOverDiffeomorph I J p p' hp hp' e F hproj z = F z :=
  rfl

@[simp]
theorem diffeomorphOfHomeomorphOverDiffeomorph_symm_apply
    (p : E → X) (p' : E' → X')
    (hp : IsLocalDiffeomorph I I n p)
    (hp' : IsLocalDiffeomorph J J n p')
    (e : X ≃ₘ^n⟮I, J⟯ X') (F : E ≃ₜ E')
    (hproj : ∀ z, p' (F z) = e (p z)) (z : E') :
    (diffeomorphOfHomeomorphOverDiffeomorph I J p p' hp hp' e F hproj).symm z = F.symm z :=
  rfl

end SplittingSpheres
