/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Thickening
public import SplittingSpheres.Geometry.UnlinkImmersion

/-!
# Compact traces of unlink-complement isotopies

A smooth sphere isotopy has compact parameter space, hence compact trace.  The explicit unlink
carrier is also compact because both components are ranges of smooth embeddings of `S²`.
Consequently an isotopy which avoids the unlink does so by a uniform positive metric margin.

This is the point-set part of the passage from the strict link complement to a compact tubular
exterior.  No tubular neighborhood or collar-compression construction is asserted here.
-/

@[expose] public section

open Function Metric Set
open scoped ContDiff Manifold unitInterval

noncomputable section

namespace SplittingSpheres

/-- The unparametrized trace of all slices of a smooth sphere isotopy. -/
def SmoothSphereIsotopy.trace {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁) : Set (Sphere 4) :=
  range H.toFun

/-- The trace of a smooth sphere isotopy is compact. -/
theorem SmoothSphereIsotopy.isCompact_trace
    {S₀ S₁ : SmoothSphereEmbedding 3 4} (H : SmoothSphereIsotopy S₀ S₁) :
    IsCompact H.trace := by
  rw [SmoothSphereIsotopy.trace, ← image_univ]
  exact isCompact_univ.image H.contMDiff_toFun.continuous

/-- Each frozen coordinate unlink component is compact. -/
theorem isCompact_standardUnlinkComponent (i : Fin 2) :
    IsCompact (standardUnlinkComponent i) := by
  rw [← range_standardUnlinkEmbedding i, ← image_univ]
  exact isCompact_univ.image (standardUnlinkEmbedding i).contMDiff.continuous

/-- The whole frozen coordinate unlink carrier is compact. -/
theorem isCompact_standardUnlinkCarrier : IsCompact standardUnlinkCarrier := by
  rw [standardUnlinkCarrier]
  exact (isCompact_standardUnlinkComponent 0).union
    (isCompact_standardUnlinkComponent 1)

/-- A metric compact exterior of the coordinate unlink.  This point-set exterior is not claimed
to be a smooth tubular exterior; that requires separate normal-bundle coordinates. -/
def metricUnlinkExterior (δ : ℝ) : Set (Sphere 4) :=
  (Metric.thickening δ standardUnlinkCarrier)ᶜ

/-- Every metric unlink exterior is compact, since it is closed in the compact ambient sphere. -/
theorem isCompact_metricUnlinkExterior (δ : ℝ) : IsCompact (metricUnlinkExterior δ) := by
  apply IsClosed.isCompact
  exact Metric.isOpen_thickening.isClosed_compl

/-- Pointwise avoidance of the unlink is exactly disjointness of the whole trace from its
carrier. -/
theorem SmoothSphereIsotopy.disjoint_trace_standardUnlinkCarrier
    {S₀ S₁ : SmoothSphereEmbedding 3 4} (H : SmoothSphereIsotopy S₀ S₁)
    (havoid : ∀ p : I × Sphere 3, H.toFun p ∉ standardUnlinkCarrier) :
    Disjoint H.trace standardUnlinkCarrier := by
  rw [Set.disjoint_left]
  rintro y ⟨p, rfl⟩ hy
  exact havoid p hy

/-- A link-avoiding isotopy trace and the compact coordinate unlink have a uniform positive
extended-metric separation. -/
theorem SmoothSphereIsotopy.exists_uniform_edist_to_standardUnlinkCarrier
    {S₀ S₁ : SmoothSphereEmbedding 3 4} (H : SmoothSphereIsotopy S₀ S₁)
    (havoid : ∀ p : I × Sphere 3, H.toFun p ∉ standardUnlinkCarrier) :
    ∃ ε : NNReal, 0 < ε ∧
      ∀ p : I × Sphere 3, ∀ y ∈ standardUnlinkCarrier,
        (ε : ENNReal) < edist (H.toFun p) y := by
  obtain ⟨ε, hε, hsep⟩ := Metric.exists_pos_forall_lt_edist H.isCompact_trace
    isCompact_standardUnlinkCarrier.isClosed
    (H.disjoint_trace_standardUnlinkCarrier havoid)
  exact ⟨ε, hε, fun p y hy ↦ hsep (H.toFun p) ⟨p, rfl⟩ y hy⟩

/-- Real-valued form of the uniform positive separation theorem. -/
theorem SmoothSphereIsotopy.exists_uniform_dist_to_standardUnlinkCarrier
    {S₀ S₁ : SmoothSphereEmbedding 3 4} (H : SmoothSphereIsotopy S₀ S₁)
    (havoid : ∀ p : I × Sphere 3, H.toFun p ∉ standardUnlinkCarrier) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ p : I × Sphere 3, ∀ y ∈ standardUnlinkCarrier,
        ε < dist (H.toFun p) y := by
  obtain ⟨ε, hε, hsep⟩ := H.exists_uniform_edist_to_standardUnlinkCarrier havoid
  refine ⟨ε, by exact_mod_cast hε, ?_⟩
  intro p y hy
  simpa [edist_dist] using hsep p y hy

/-- The trace and unlink have disjoint closed metric neighborhoods of one common positive
radius.  This packages the uniform margin in a form suited to later exterior constructions. -/
theorem SmoothSphereIsotopy.exists_disjoint_closedThickenings_standardUnlinkCarrier
    {S₀ S₁ : SmoothSphereEmbedding 3 4} (H : SmoothSphereIsotopy S₀ S₁)
    (havoid : ∀ p : I × Sphere 3, H.toFun p ∉ standardUnlinkCarrier) :
    ∃ δ : ℝ, 0 < δ ∧
      Disjoint (Metric.cthickening δ H.trace)
        (Metric.cthickening δ standardUnlinkCarrier) :=
  (H.disjoint_trace_standardUnlinkCarrier havoid).exists_cthickenings
    H.isCompact_trace isCompact_standardUnlinkCarrier.isClosed

/-- Every complement isotopy trace lies in one compact metric exterior of positive radius. -/
theorem SmoothSphereIsotopy.exists_trace_subset_metricUnlinkExterior
    {S₀ S₁ : SmoothSphereEmbedding 3 4} (H : SmoothSphereIsotopy S₀ S₁)
    (havoid : ∀ p : I × Sphere 3, H.toFun p ∉ standardUnlinkCarrier) :
    ∃ δ : ℝ, 0 < δ ∧ H.trace ⊆ metricUnlinkExterior δ := by
  obtain ⟨δ, hδ, hdisj⟩ :=
    H.exists_disjoint_closedThickenings_standardUnlinkCarrier havoid
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  rw [metricUnlinkExterior, mem_compl_iff]
  intro hxthick
  exact Set.disjoint_left.1 hdisj
    (Metric.self_subset_cthickening H.trace hx)
    (Metric.thickening_subset_cthickening δ standardUnlinkCarrier hxthick)

/-- Unpack a frozen complement isotopy together with one compact metric exterior containing its
entire trace. -/
theorem SmoothlyIsotopicInComplement.exists_isotopy_trace_in_metricUnlinkExterior
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (h : SmoothlyIsotopicInComplement S₀ S₁) :
    ∃ H : SmoothSphereIsotopy S₀ S₁, ∃ δ : ℝ,
      0 < δ ∧ H.trace ⊆ metricUnlinkExterior δ := by
  obtain ⟨H, havoid⟩ := h
  obtain ⟨δ, hδ, htrace⟩ := H.exists_trace_subset_metricUnlinkExterior havoid
  exact ⟨H, δ, hδ, htrace⟩

end SplittingSpheres
