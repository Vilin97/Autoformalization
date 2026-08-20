/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.RelativeDiffeomorph
public import SplittingSpheres.Foundations.SmoothIsotopy

/-!
# Operations on relative smooth diffeotopies

These are the parameterwise operations whose joint smoothness follows directly from composition:
time reversal, multiplication on either side by a fixed relative diffeomorphism, and conjugation
by a fixed relative diffeomorphism.  A parameterwise inverse needs a separate parametric inverse
theorem and is deliberately not assumed here.
-/

@[expose] public section

open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

universe uM uH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {IM : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {s : Set M}

namespace RelativeDiffeotopy

/-- Reverse the time parameter of a relative diffeotopy. -/
def symm {f g : TauCeti.RelativeDiff (I := IM) M ∞ s}
    (F : RelativeDiffeotopy s f g) : RelativeDiffeotopy s g f where
  toFun p := F.toFun (unitInterval.symm p.1, p.2)
  contMDiff_toFun := F.contMDiff_toFun.comp
    ((unitInterval.contMDiff_symm.comp contMDiff_fst).prodMk contMDiff_snd)
  slice t := F.slice (unitInterval.symm t)
  zero x := by simpa using F.one x
  one x := by simpa using F.zero x

/-- Multiply every slice on the left by a fixed relative diffeomorphism. -/
def mulLeft (h : TauCeti.RelativeDiff (I := IM) M ∞ s)
    {f g : TauCeti.RelativeDiff (I := IM) M ∞ s}
    (F : RelativeDiffeotopy s f g) : RelativeDiffeotopy s (h * f) (h * g) where
  toFun p := h.1 (F.toFun p)
  contMDiff_toFun := h.1.contMDiff.comp F.contMDiff_toFun
  slice t := by
    obtain ⟨φ, hφ⟩ := F.slice t
    refine ⟨h * φ, fun x ↦ ?_⟩
    rw [hφ]
    rfl
  zero x := by
    rw [F.zero]
    rfl
  one x := by
    rw [F.one]
    rfl

/-- Multiply every slice on the right by a fixed relative diffeomorphism. -/
def mulRight (h : TauCeti.RelativeDiff (I := IM) M ∞ s)
    {f g : TauCeti.RelativeDiff (I := IM) M ∞ s}
    (F : RelativeDiffeotopy s f g) : RelativeDiffeotopy s (f * h) (g * h) where
  toFun p := F.toFun (p.1, h.1 p.2)
  contMDiff_toFun := F.contMDiff_toFun.comp
    (contMDiff_fst.prodMk (h.1.contMDiff.comp contMDiff_snd))
  slice t := by
    obtain ⟨φ, hφ⟩ := F.slice t
    refine ⟨φ * h, fun x ↦ ?_⟩
    rw [hφ]
    rfl
  zero x := by
    rw [F.zero]
    rfl
  one x := by
    rw [F.one]
    rfl

/-- Conjugate every slice by a fixed relative diffeomorphism. -/
def conj (h : TauCeti.RelativeDiff (I := IM) M ∞ s)
    {f g : TauCeti.RelativeDiff (I := IM) M ∞ s}
    (F : RelativeDiffeotopy s f g) :
    RelativeDiffeotopy s (h * f * h⁻¹) (h * g * h⁻¹) :=
  (F.mulLeft h).mulRight h⁻¹

end RelativeDiffeotopy

/-- Genuine relative diffeotopies remain equal after quotienting further by any selected family
of representatives. -/
theorem RelativeDiffeotopy.mappingClassMod_eq
    {T : Set (TauCeti.RelativeDiff (I := IM) M ∞ s)}
    {f g : TauCeti.RelativeDiff (I := IM) M ∞ s}
    (F : RelativeDiffeotopy s f g) :
    relativeMappingClassModMk (IM := IM) s T f =
      relativeMappingClassModMk (IM := IM) s T g := by
  apply congrArg
    (QuotientGroup.mk' (Subgroup.normalClosure (relativeMappingClassMk (IM := IM) s '' T)))
  exact F.mappingClass_eq

end SplittingSpheres
