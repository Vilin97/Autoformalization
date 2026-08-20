/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import TauCeti.Geometry.Diffeomorphism.FixingSubgroup

/-!
# Relative smooth diffeotopies and their algebraic quotient

This file introduces a joint-smoothness notion for a path of relative diffeomorphisms.  The
mapping-class group is presented as the quotient by the normal closure of endpoint differences of
such paths.  Defining the quotient this way makes its group structure independent of later
parametric-inverse and concatenation constructions, while retaining the theorem that the two
endpoints of every genuine smooth diffeotopy have equal classes.
-/

@[expose] public section

open Set
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

universe uM uH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {IM : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

/-- A jointly smooth path from one relative diffeomorphism to another.  Every time slice is
required to be a relative diffeomorphism fixing `s`; this records both invertibility and the
relative boundary condition without weakening either to a pointwise property of the endpoints. -/
structure RelativeDiffeotopy (s : Set M)
    (f g : TauCeti.RelativeDiff (I := IM) M ∞ s) where
  /-- The evaluation map of the family. -/
  toFun : unitInterval × M → M
  /-- Smoothness jointly in time and the manifold variable. -/
  contMDiff_toFun : ContMDiff ((𝓡∂ 1).prod IM) IM ∞ toFun
  /-- Each time slice is represented by a relative diffeomorphism. -/
  slice : ∀ t : unitInterval,
    ∃ φ : TauCeti.RelativeDiff (I := IM) M ∞ s, ∀ x, toFun (t, x) = φ.1 x
  /-- The initial slice is `f`. -/
  zero : ∀ x, toFun (0, x) = f.1 x
  /-- The final slice is `g`. -/
  one : ∀ x, toFun (1, x) = g.1 x

namespace RelativeDiffeotopy

/-- The constant family is a relative diffeotopy. -/
protected def refl (s : Set M) (f : TauCeti.RelativeDiff (I := IM) M ∞ s) :
    RelativeDiffeotopy s f f where
  toFun p := f.1 p.2
  contMDiff_toFun := f.1.contMDiff.comp contMDiff_snd
  slice _t := ⟨f, fun _ ↦ rfl⟩
  zero _ := rfl
  one _ := rfl

end RelativeDiffeotopy

/-- A self-diffeomorphism is supported in `U` when it fixes every point outside `U`. -/
def DiffeomorphSupportedIn (f : TauCeti.Diff IM M ∞) (U : Set M) : Prop :=
  ∀ ⦃x : M⦄, x ∉ U → f x = x

namespace DiffeomorphSupportedIn

/-- The identity diffeomorphism is supported in every set. -/
theorem one (U : Set M) : DiffeomorphSupportedIn (IM := IM) (1 : TauCeti.Diff IM M ∞) U := by
  intro x _
  rfl

/-- Enlarging the supporting set preserves supportedness. -/
theorem mono {f : TauCeti.Diff IM M ∞} {U V : Set M} (hUV : U ⊆ V)
    (hf : DiffeomorphSupportedIn f U) : DiffeomorphSupportedIn f V := by
  intro x hx
  exact hf fun hxU ↦ hx (hUV hxU)

/-- A product of diffeomorphisms supported in one set is supported in that set. -/
theorem mul {f g : TauCeti.Diff IM M ∞} {U : Set M}
    (hf : DiffeomorphSupportedIn f U) (hg : DiffeomorphSupportedIn g U) :
    DiffeomorphSupportedIn (f * g) U := by
  intro x hx
  rw [TauCeti.Diffeomorph.mul_apply, hg hx, hf hx]

/-- The inverse of a diffeomorphism supported in `U` is supported in `U`. -/
theorem inv {f : TauCeti.Diff IM M ∞} {U : Set M} (hf : DiffeomorphSupportedIn f U) :
    DiffeomorphSupportedIn f⁻¹ U := by
  intro x hx
  rw [TauCeti.Diffeomorph.inv_apply]
  apply f.injective
  exact (f.apply_symm_apply x).trans (hf hx).symm

/-- Conjugation transports support by the conjugating diffeomorphism. -/
theorem conj {f h : TauCeti.Diff IM M ∞} {U : Set M}
    (hf : DiffeomorphSupportedIn f U) :
    DiffeomorphSupportedIn (h * f * h⁻¹) (h '' U) := by
  intro x hx
  have hy : h.symm x ∉ U := by
    intro hy'
    exact hx ⟨h.symm x, hy', h.apply_symm_apply x⟩
  simp only [TauCeti.Diffeomorph.mul_apply, TauCeti.Diffeomorph.inv_apply]
  rw [hf hy, h.apply_symm_apply]

end DiffeomorphSupportedIn

/-- Relative diffeomorphisms whose underlying maps are supported in `U`. -/
def relativeDiffSupportedIn (s U : Set M) :
    Set (TauCeti.RelativeDiff (I := IM) M ∞ s) :=
  {f | DiffeomorphSupportedIn f.1 U}

/-- Relative diffeomorphisms supported in one fixed subset form a subgroup. -/
def relativeDiffSupportedInSubgroup (s U : Set M) :
    Subgroup (TauCeti.RelativeDiff (I := IM) M ∞ s) where
  carrier := relativeDiffSupportedIn (IM := IM) s U
  one_mem' := DiffeomorphSupportedIn.one U
  mul_mem' hf hg := DiffeomorphSupportedIn.mul hf hg
  inv_mem' hf := DiffeomorphSupportedIn.inv hf

/-- Endpoint differences of genuine relative diffeotopies. -/
def relativeDiffeotopyRelators (s : Set M) :
    Set (TauCeti.RelativeDiff (I := IM) M ∞ s) :=
  {r | ∃ f g, Nonempty (RelativeDiffeotopy s f g) ∧ r = f / g}

/-- The normal subgroup imposing all relative-diffeotopy endpoint relations. -/
def relativeDiffeotopyNormal (s : Set M) :
    Subgroup (TauCeti.RelativeDiff (I := IM) M ∞ s) :=
  Subgroup.normalClosure (relativeDiffeotopyRelators (IM := IM) s)

instance relativeDiffeotopyNormal_normal (s : Set M) :
    (relativeDiffeotopyNormal (IM := IM) s).Normal :=
  Subgroup.normalClosure_normal

/-- The relative smooth mapping-class group, presented by genuine joint-smooth diffeotopies. -/
abbrev RelativeMappingClass (s : Set M) :=
  TauCeti.RelativeDiff (I := IM) M ∞ s ⧸ relativeDiffeotopyNormal (IM := IM) s

/-- The canonical homomorphism from relative diffeomorphisms to relative mapping classes. -/
def relativeMappingClassMk (s : Set M) :
    TauCeti.RelativeDiff (I := IM) M ∞ s →* RelativeMappingClass (IM := IM) s :=
  QuotientGroup.mk' (relativeDiffeotopyNormal (IM := IM) s)

@[simp]
theorem relativeMappingClassMk_one (s : Set M) :
    relativeMappingClassMk (IM := IM) s 1 = 1 :=
  map_one _

/-- The endpoints of a relative smooth diffeotopy define the same mapping class. -/
theorem RelativeDiffeotopy.mappingClass_eq {s : Set M}
    {f g : TauCeti.RelativeDiff (I := IM) M ∞ s} (h : RelativeDiffeotopy s f g) :
    relativeMappingClassMk (IM := IM) s f = relativeMappingClassMk (IM := IM) s g := by
  change (f : RelativeMappingClass (IM := IM) s) = g
  apply QuotientGroup.eq_iff_div_mem.mpr
  exact Subgroup.subset_normalClosure ⟨f, g, ⟨h⟩, rfl⟩

/-- A second quotient which declares every member of a chosen collection `T` trivial after
passing to mapping classes.  The ball-supported quotient is obtained later by taking `T` to be
the set of relative diffeomorphisms supported in embedded interior four-balls. -/
abbrev RelativeMappingClassMod (s : Set M)
    (T : Set (TauCeti.RelativeDiff (I := IM) M ∞ s)) :=
  RelativeMappingClass (IM := IM) s ⧸
    Subgroup.normalClosure (relativeMappingClassMk (IM := IM) s '' T)

/-- The canonical map to a relative mapping-class quotient by the collection `T`. -/
def relativeMappingClassModMk (s : Set M)
    (T : Set (TauCeti.RelativeDiff (I := IM) M ∞ s)) :
    TauCeti.RelativeDiff (I := IM) M ∞ s →*
      RelativeMappingClassMod (IM := IM) s T :=
  (QuotientGroup.mk' (Subgroup.normalClosure (relativeMappingClassMk (IM := IM) s '' T))).comp
    (relativeMappingClassMk (IM := IM) s)

/-- Every selected representative is trivial in the corresponding mapping-class quotient. -/
theorem relativeMappingClassModMk_eq_one {s : Set M}
    {T : Set (TauCeti.RelativeDiff (I := IM) M ∞ s)}
    {f : TauCeti.RelativeDiff (I := IM) M ∞ s}
    (hf : f ∈ T) : relativeMappingClassModMk (IM := IM) s T f = 1 := by
  change ((relativeMappingClassMk (IM := IM) s f : RelativeMappingClass (IM := IM) s) :
    RelativeMappingClassMod (IM := IM) s T) = 1
  exact (QuotientGroup.eq_one_iff _).mpr <|
    Subgroup.subset_normalClosure (mem_image_of_mem _ hf)

end SplittingSpheres
