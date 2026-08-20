/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothEmbedding

/-!
# Source reparametrization of equal embedded ranges

Two smooth embeddings with the same range differ by a unique source homeomorphism.  This file
proves that homeomorphism and its inverse are smooth, hence upgrades it to a diffeomorphism.  The
smoothness proof uses Mathlib's cancellation theorem for composition with an immersion: composing
the source homeomorphism with one embedding gives the other, already-smooth embedding.
-/

@[expose] public section

open Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.SmoothEmbedding

universe uE uE' uH uH' uM uN

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type uH} [TopologicalSpace H] {H' : Type uH'} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω}

/-- The canonical source homeomorphism between two embeddings with equal ranges.  It goes from
the source through the range of `f`, retags that range as the range of `g`, and returns through
the inverse of `g`. -/
def sourceHomeomorphOfRangeEq
    (f g : TauCeti.SmoothEmbedding I J n M N) (h : range f = range g) : M ≃ₜ M :=
  (f.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr h)).trans
    g.isEmbedding.toHomeomorph.symm

/-- Reparametrizing `g` by the canonical homeomorphism gives `f` pointwise. -/
@[simp]
theorem sourceHomeomorphOfRangeEq_apply
    (f g : TauCeti.SmoothEmbedding I J n M N) (h : range f = range g) (x : M) :
    g (sourceHomeomorphOfRangeEq f g h x) = f x := by
  have hy := g.isEmbedding.toHomeomorph.apply_symm_apply
    ((Homeomorph.setCongr h) (f.isEmbedding.toHomeomorph x))
  exact congrArg Subtype.val hy

/-- The inverse reparametrization carries `f` back to `g`. -/
@[simp]
theorem sourceHomeomorphOfRangeEq_symm_apply
    (f g : TauCeti.SmoothEmbedding I J n M N) (h : range f = range g) (x : M) :
    f ((sourceHomeomorphOfRangeEq f g h).symm x) = g x := by
  have hy := f.isEmbedding.toHomeomorph.apply_symm_apply
    ((Homeomorph.setCongr h).symm (g.isEmbedding.toHomeomorph x))
  exact congrArg Subtype.val hy

variable [IsManifold I n M] [IsManifold J n N]

/-- Equal embedded ranges induce a canonical smooth source diffeomorphism. -/
def sourceDiffeomorphOfRangeEq
    (f g : TauCeti.SmoothEmbedding I J n M N) (h : range f = range g) :
    M ≃ₘ^n⟮I, I⟯ M where
  toEquiv := (sourceHomeomorphOfRangeEq f g h).toEquiv
  contMDiff_toFun := by
    rw [ContMDiff.iff_comp_isImmersion g.isImmersion]
    refine ⟨(sourceHomeomorphOfRangeEq f g h).continuous, ?_⟩
    convert f.contMDiff using 1
    funext x
    exact sourceHomeomorphOfRangeEq_apply f g h x
  contMDiff_invFun := by
    rw [ContMDiff.iff_comp_isImmersion f.isImmersion]
    refine ⟨(sourceHomeomorphOfRangeEq f g h).symm.continuous, ?_⟩
    convert g.contMDiff using 1
    funext x
    exact sourceHomeomorphOfRangeEq_symm_apply f g h x

@[simp]
theorem sourceDiffeomorphOfRangeEq_apply
    (f g : TauCeti.SmoothEmbedding I J n M N) (h : range f = range g) (x : M) :
    g (sourceDiffeomorphOfRangeEq f g h x) = f x :=
  sourceHomeomorphOfRangeEq_apply f g h x

@[simp]
theorem sourceDiffeomorphOfRangeEq_symm_apply
    (f g : TauCeti.SmoothEmbedding I J n M N) (h : range f = range g) (x : M) :
    f ((sourceDiffeomorphOfRangeEq f g h).symm x) = g x :=
  sourceHomeomorphOfRangeEq_symm_apply f g h x

end TauCeti.SmoothEmbedding
