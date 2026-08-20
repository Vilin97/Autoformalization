/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothIsotopy
public import SplittingSpheres.Geometry.UnlinkTubes

/-!
# Transporting isotopies through coordinate unlink exteriors

An ambient diffeomorphism which fixes both endpoint spheres pointwise can postcompose an isotopy
without changing its endpoint ranges.  If it preserves the unlink carrier by preimage, it also
preserves link avoidance.  Finally, an image bound between coordinate exteriors transports a
uniform trace bound.

The source exterior radius is assumed positive.  This is necessary: for a nonpositive radius the
open unlink tubes are empty, so membership in their complement says nothing about link avoidance.
-/

@[expose] public section

open Function Set
open scoped ContDiff Manifold unitInterval

noncomputable section

namespace SplittingSpheres

/-- Postcompose an isotopy by an ambient diffeomorphism which fixes both endpoint images, then
retag the resulting endpoint embeddings by the original endpoints. -/
def SmoothSphereIsotopy.endpointRelativePostcomp
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁)
    (e : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4)
    (h₀ : Set.EqOn e id (range S₀))
    (h₁ : Set.EqOn e id (range S₁)) :
    SmoothSphereIsotopy S₀ S₁ :=
  (H.postcompDiffeomorph e).congrRange
    ((TauCeti.SmoothEmbedding.range_postcompDiffeomorph S₀ e).trans h₀.image_eq_self)
    ((TauCeti.SmoothEmbedding.range_postcompDiffeomorph S₁ e).trans h₁.image_eq_self)

@[simp]
theorem SmoothSphereIsotopy.endpointRelativePostcomp_toFun
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁)
    (e : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4)
    (h₀ : Set.EqOn e id (range S₀))
    (h₁ : Set.EqOn e id (range S₁)) (p : I × Sphere 3) :
    (H.endpointRelativePostcomp e h₀ h₁).toFun p = e (H.toFun p) :=
  rfl

/-- The transported trace is exactly the ambient image of the original trace. -/
theorem SmoothSphereIsotopy.trace_endpointRelativePostcomp
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁)
    (e : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4)
    (h₀ : Set.EqOn e id (range S₀))
    (h₁ : Set.EqOn e id (range S₁)) :
    (H.endpointRelativePostcomp e h₀ h₁).trace = e '' H.trace := by
  rw [SmoothSphereIsotopy.trace, SmoothSphereIsotopy.trace]
  change range (e ∘ H.toFun) = e '' range H.toFun
  exact Set.range_comp e H.toFun

/-- A point in a positive-radius coordinate exterior misses the frozen unlink carrier. -/
theorem not_mem_standardUnlinkCarrier_of_mem_coordinateUnlinkExterior
    {r : ℝ} (hr : 0 < r) {x : Sphere 4} (hx : x ∈ coordinateUnlinkExterior r) :
    x ∉ standardUnlinkCarrier := by
  intro hxcarrier
  exact hx (standardUnlinkCarrier_subset_openTubes hr hxcarrier)

/-- Endpoint-relative postcomposition preserves link avoidance when the ambient diffeomorphism
preserves the unlink carrier by preimage. -/
theorem SmoothSphereIsotopy.endpointRelativePostcomp_avoids_standardUnlinkCarrier
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁)
    (e : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4)
    (h₀ : Set.EqOn e id (range S₀))
    (h₁ : Set.EqOn e id (range S₁))
    (hcarrier : e ⁻¹' standardUnlinkCarrier = standardUnlinkCarrier)
    {r : ℝ} (hr : 0 < r) (htrace : H.trace ⊆ coordinateUnlinkExterior r) :
    ∀ p : I × Sphere 3,
      (H.endpointRelativePostcomp e h₀ h₁).toFun p ∉ standardUnlinkCarrier := by
  intro p hp
  have hpPreimage : H.toFun p ∈ e ⁻¹' standardUnlinkCarrier := hp
  rw [hcarrier] at hpPreimage
  exact not_mem_standardUnlinkCarrier_of_mem_coordinateUnlinkExterior hr
    (htrace ⟨p, rfl⟩) hpPreimage

/-- An image bound between coordinate exteriors transports the entire isotopy trace. -/
theorem SmoothSphereIsotopy.endpointRelativePostcomp_trace_subset
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁)
    (e : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4)
    (h₀ : Set.EqOn e id (range S₀))
    (h₁ : Set.EqOn e id (range S₁))
    {r q : ℝ} (htrace : H.trace ⊆ coordinateUnlinkExterior r)
    (himage : e '' coordinateUnlinkExterior r ⊆ coordinateUnlinkExterior q) :
    (H.endpointRelativePostcomp e h₀ h₁).trace ⊆ coordinateUnlinkExterior q := by
  rw [H.trace_endpointRelativePostcomp e h₀ h₁]
  exact (Set.image_mono htrace).trans himage

/-- Package endpoint-relative transport, link avoidance, and the target exterior trace bound.

No positivity assumption on `q` is needed: avoidance follows from the positive source exterior and
carrier preservation, while `q` only indexes the asserted target trace bound. -/
theorem SmoothSphereIsotopy.exists_endpointRelativeExteriorTransport
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁)
    (e : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4)
    (h₀ : Set.EqOn e id (range S₀))
    (h₁ : Set.EqOn e id (range S₁))
    (hcarrier : e ⁻¹' standardUnlinkCarrier = standardUnlinkCarrier)
    {r q : ℝ} (hr : 0 < r) (htrace : H.trace ⊆ coordinateUnlinkExterior r)
    (himage : e '' coordinateUnlinkExterior r ⊆ coordinateUnlinkExterior q) :
    ∃ H' : SmoothSphereIsotopy S₀ S₁,
      (∀ p : I × Sphere 3, H'.toFun p ∉ standardUnlinkCarrier) ∧
        H'.trace ⊆ coordinateUnlinkExterior q := by
  refine ⟨H.endpointRelativePostcomp e h₀ h₁, ?_, ?_⟩
  · exact H.endpointRelativePostcomp_avoids_standardUnlinkCarrier e h₀ h₁
      hcarrier hr htrace
  · exact H.endpointRelativePostcomp_trace_subset e h₀ h₁ htrace himage

/-- Endpoint-relative exterior transport supplies an isotopy in the frozen unlink complement. -/
theorem SmoothSphereIsotopy.smoothlyIsotopicInComplement_of_endpointRelativeExteriorTransport
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁)
    (e : Sphere 4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ Sphere 4)
    (h₀ : Set.EqOn e id (range S₀))
    (h₁ : Set.EqOn e id (range S₁))
    (hcarrier : e ⁻¹' standardUnlinkCarrier = standardUnlinkCarrier)
    {r : ℝ} (hr : 0 < r) (htrace : H.trace ⊆ coordinateUnlinkExterior r) :
    SmoothlyIsotopicInComplement S₀ S₁ :=
  ⟨H.endpointRelativePostcomp e h₀ h₁,
    H.endpointRelativePostcomp_avoids_standardUnlinkCarrier e h₀ h₁
      hcarrier hr htrace⟩

end SplittingSpheres
