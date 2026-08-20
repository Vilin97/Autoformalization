/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Proper.Basic
public import SplittingSpheres.Foundations.TopologicalCoverPullback

/-!
# Compactness of pullbacks of proper maps

If `p : E → X` is proper and `f : Y → X` is continuous with compact source, then their
point-set pullback is compact.  We prove this by identifying the pullback with the closed
equalizer inside

`Y × p⁻¹(range f)`.

The second factor is compact by properness, and the equalizer is closed because `X` is
Hausdorff.  This result is independent of covering-space theory.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

universe uE uX uY

variable {E : Type uE} {X : Type uX} {Y : Type uY}
variable [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]

/-- A compact ambient model for a pullback of a proper map. -/
def topologicalCoverPullbackCompactModelSet (p : E → X) (f : Y → X) :
    Set (Y × (p ⁻¹' Set.range f)) :=
  {q | f q.1 = p q.2.1}

/-- The ordinary pullback is homeomorphic to its compact equalizer model. -/
def topologicalCoverPullbackCompactModelHomeomorph (p : E → X) (f : Y → X) :
    TopologicalCoverPullback p f ≃ₜ topologicalCoverPullbackCompactModelSet p f where
  toFun z := ⟨(z.1.1, ⟨z.1.2, ⟨z.1.1, z.2⟩⟩), z.2⟩
  invFun z := ⟨(z.1.1, z.1.2.1), z.2⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val))

omit [TopologicalSpace X] in
@[simp]
theorem topologicalCoverPullbackCompactModelHomeomorph_base
    (p : E → X) (f : Y → X) (z : TopologicalCoverPullback p f) :
    (topologicalCoverPullbackCompactModelHomeomorph p f z).1.1 = z.1.1 :=
  rfl

omit [TopologicalSpace X] in
@[simp]
theorem topologicalCoverPullbackCompactModelHomeomorph_fiber
    (p : E → X) (f : Y → X) (z : TopologicalCoverPullback p f) :
    (topologicalCoverPullbackCompactModelHomeomorph p f z).1.2.1 = z.1.2 :=
  rfl

/-- The compact model is a closed equalizer. -/
theorem isClosed_topologicalCoverPullbackCompactModelSet
    [T2Space X] (p : E → X) (f : Y → X)
    (hp : Continuous p) (hf : Continuous f) :
    IsClosed (topologicalCoverPullbackCompactModelSet p f) := by
  exact isClosed_eq (hf.comp continuous_fst)
    (hp.comp (continuous_subtype_val.comp continuous_snd))

/-- The inverse image of the compact range of `f` is compact under a proper map. -/
theorem isCompact_preimage_range_of_isProperMap
    (p : E → X) (f : Y → X) (hp : IsProperMap p) (hf : Continuous f)
    [CompactSpace Y] :
    IsCompact (p ⁻¹' Set.range f) :=
  hp.isCompact_preimage (isCompact_range hf)

/-- A pullback of a proper map along a continuous map from a compact space is compact. -/
theorem topologicalCoverPullbackCompactSpace [T2Space X] [CompactSpace Y]
    (p : E → X) (f : Y → X) (hp : IsProperMap p) (hf : Continuous f) :
    CompactSpace (TopologicalCoverPullback p f) := by
  let _ : CompactSpace (p ⁻¹' Set.range f) :=
    isCompact_iff_compactSpace.mp
      (isCompact_preimage_range_of_isProperMap p f hp hf)
  let _ : CompactSpace (topologicalCoverPullbackCompactModelSet p f) :=
    isCompact_iff_compactSpace.mp
      ((isClosed_topologicalCoverPullbackCompactModelSet p f hp.continuous hf).isCompact)
  exact (topologicalCoverPullbackCompactModelHomeomorph p f).isClosedEmbedding.compactSpace

end SplittingSpheres
