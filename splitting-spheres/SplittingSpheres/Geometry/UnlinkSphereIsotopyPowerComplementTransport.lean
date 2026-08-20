/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import SplittingSpheres.Geometry.UnlinkSphereIsotopyPowerLift
public import TauCeti.Topology.Homotopy.AmbientIsotopic.Complement

/-!
# Conditional complement transport for lifted unlink-avoiding isotopies

The lifted sphere isotopy in `UnlinkSphereIsotopyPowerLift` is an isotopy through smooth
embeddings in the cyclic power cover, but an isotopy of an embedded sphere does not by itself
give a homeomorphism of its complement.  This file isolates the precise additional input needed:
an actual `TauCeti.AmbientIsotopy` whose final map agrees on the initial labelled equator with the
time-one lifted sphere.

From that endpoint-only agreement, the final ambient homeomorphism restricts to a homeomorphism
between the two sphere complements.  We record its forward and inverse underlying-value laws,
its action on relative connected components in the ambient power cover, and the induced
homeomorphism of `ConnectedComponents` of the complement subtypes.

No ambient extension is constructed or postulated here.  The missing existence result has the
following exact shape: from the jointly smooth map
`standardUnlinkPowerIsotopyLift m a H havoid`, whose every slice is a smooth embedding, produce
`Phi : TauCeti.AmbientIsotopy (StandardUnlinkPowerPullback m)` satisfying
`Phi.final (equatorUnlinkPowerLift m a x) =
standardUnlinkPowerIsotopyLift m a H havoid (1, x)` for every `x`.  This is the isotopy-extension
direction; the current TauCeti and Mathlib APIs provide ambient-isotopy restriction and
complement transport, but not this existence theorem.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open scoped unitInterval

namespace SplittingSpheres

variable {S : SmoothSphereEmbedding 3 4}

/-! ## Endpoint maps and the conditional ambient-extension witness -/

/-- The labelled equatorial lift bundled as a continuous map. -/
def equatorUnlinkPowerLiftContinuousMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(Sphere 3, StandardUnlinkPowerPullback m) where
  toFun := equatorUnlinkPowerLift m a
  continuous_toFun := continuous_equatorUnlinkPowerLift m a

@[simp]
theorem equatorUnlinkPowerLiftContinuousMap_apply
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    equatorUnlinkPowerLiftContinuousMap m a x =
      equatorUnlinkPowerLift m a x :=
  rfl

/-- The time-one slice of the lifted isotopy, bundled as a continuous map. -/
def standardUnlinkPowerIsotopyLiftFinalContinuousMap
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    C(Sphere 3, StandardUnlinkPowerPullback m) where
  toFun x := standardUnlinkPowerIsotopyLift m a H havoid (1, x)
  continuous_toFun :=
    (standardUnlinkPowerIsotopyLift m a H havoid).continuous.comp
      (continuous_const.prodMk continuous_id)

@[simp]
theorem standardUnlinkPowerIsotopyLiftFinalContinuousMap_apply
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) (x : Sphere 3) :
    standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid x =
      standardUnlinkPowerIsotopyLift m a H havoid (1, x) :=
  rfl

/-- Conditional ambient-extension data for one labelled lifted sphere isotopy.

Only final-time agreement on the initial equator is assumed.  No agreement away from that sphere
or at intermediate times is needed for complement transport. -/
structure StandardUnlinkPowerIsotopyLiftAmbientExtension
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) where
  /-- An actual ambient isotopy of the cyclic power cover. -/
  ambientIsotopy : TauCeti.AmbientIsotopy (StandardUnlinkPowerPullback m)
  /-- Its final map agrees pointwise with the time-one lifted sphere on the initial labelled
  equator. -/
  final_agrees : ∀ x,
    ambientIsotopy.final (equatorUnlinkPowerLift m a x) =
      standardUnlinkPowerIsotopyLift m a H havoid (1, x)

namespace StandardUnlinkPowerIsotopyLiftAmbientExtension

variable {m : ℕ} [NeZero m] {a : ZMod m}
  {H : SmoothSphereIsotopy standardSplittingSphere S}
  {havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier}

/-- Endpoint agreement as equality of the bundled continuous maps. -/
theorem final_comp_equatorUnlinkPowerLiftContinuousMap
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid) :
    E.ambientIsotopy.final.comp (equatorUnlinkPowerLiftContinuousMap m a) =
      standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid := by
  apply ContinuousMap.ext
  intro x
  exact E.final_agrees x

/-- A point misses the initial lifted sphere exactly when its final ambient image misses the
time-one lifted sphere. -/
theorem finalHomeomorph_notMem_range_iff
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid)
    (y : StandardUnlinkPowerPullback m) :
    y ∉ range (equatorUnlinkPowerLiftContinuousMap m a) ↔
      E.ambientIsotopy.finalHomeomorph y ∉
        range (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid) := by
  rw [← E.final_comp_equatorUnlinkPowerLiftContinuousMap]
  exact E.ambientIsotopy.notMem_range_iff
    (equatorUnlinkPowerLiftContinuousMap m a) y

/-! ## The induced homeomorphism of sphere complements -/

/-- The final ambient homeomorphism restricted to the complements of the initial and final
lifted spheres. -/
noncomputable def complementHomeomorph
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid) :
    ↥(range (equatorUnlinkPowerLiftContinuousMap m a))ᶜ ≃ₜ
      ↥(range (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ :=
  E.ambientIsotopy.finalHomeomorph.subtype fun y ↦ by
    change y ∉ range (equatorUnlinkPowerLiftContinuousMap m a) ↔
      E.ambientIsotopy.finalHomeomorph y ∉
        range (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid)
    exact E.finalHomeomorph_notMem_range_iff y

/-- The complement homeomorphism is the final ambient homeomorphism on underlying points. -/
theorem coe_complementHomeomorph_apply
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid)
    (y : ↥(range (equatorUnlinkPowerLiftContinuousMap m a))ᶜ) :
    (E.complementHomeomorph y : StandardUnlinkPowerPullback m) =
      E.ambientIsotopy.finalHomeomorph y := by
  exact Homeomorph.subtype_apply_coe _ _ y

/-- The inverse complement homeomorphism is the inverse final ambient homeomorphism on
underlying points. -/
theorem coe_complementHomeomorph_symm_apply
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid)
    (y : ↥(range
      (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ) :
    (E.complementHomeomorph.symm y : StandardUnlinkPowerPullback m) =
      E.ambientIsotopy.finalHomeomorph.symm y := by
  exact Homeomorph.subtype_symm_apply_coe _ _ y

/-- The final ambient homeomorphism carries the initial lifted sphere range exactly onto the
time-one lifted sphere range. -/
theorem image_range_equatorUnlinkPowerLift
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid) :
    E.ambientIsotopy.finalHomeomorph ''
        range (equatorUnlinkPowerLiftContinuousMap m a) =
      range (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid) := by
  rw [← E.final_comp_equatorUnlinkPowerLiftContinuousMap,
    E.ambientIsotopy.range_final_comp]

/-- The final ambient homeomorphism carries the initial sphere complement exactly onto the
time-one sphere complement. -/
theorem image_compl_range_equatorUnlinkPowerLift
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid) :
    E.ambientIsotopy.finalHomeomorph ''
        (range (equatorUnlinkPowerLiftContinuousMap m a))ᶜ =
      (range (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ := by
  rw [E.ambientIsotopy.finalHomeomorph.image_compl,
    E.image_range_equatorUnlinkPowerLift]

/-! ## Connected-component transport -/

/-- Exact transport of relative connected components in the ambient power cover. -/
theorem image_connectedComponentIn_compl_range_equatorUnlinkPowerLift
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid)
    {y : StandardUnlinkPowerPullback m}
    (hy : y ∈ (range (equatorUnlinkPowerLiftContinuousMap m a))ᶜ) :
    E.ambientIsotopy.finalHomeomorph ''
        connectedComponentIn
          (range (equatorUnlinkPowerLiftContinuousMap m a))ᶜ y =
      connectedComponentIn
        (range (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ
        (E.ambientIsotopy.finalHomeomorph y) := by
  rw [E.ambientIsotopy.finalHomeomorph.image_connectedComponentIn hy,
    E.image_compl_range_equatorUnlinkPowerLift]

/-- Every point fiber of the complement homeomorphism is a connected singleton. -/
theorem isConnected_complementHomeomorph_preimage_singleton
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid)
    (y : ↥(range
      (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ) :
    IsConnected (E.complementHomeomorph ⁻¹' {y}) := by
  rw [show E.complementHomeomorph ⁻¹' {y} =
      {E.complementHomeomorph.symm y} by
        ext x
        simp only [mem_preimage, mem_singleton_iff]
        exact E.complementHomeomorph.eq_symm_apply.symm]
  exact isConnected_singleton

/-- The complement homeomorphism induces a homeomorphism of the spaces of connected
components. -/
noncomputable def connectedComponentsHomeomorph
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid) :
    ConnectedComponents
        ↥(range (equatorUnlinkPowerLiftContinuousMap m a))ᶜ ≃ₜ
      ConnectedComponents
        ↥(range
          (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ :=
  E.complementHomeomorph.isQuotientMap.isCoinducing.connectedComponentsHomeomorph
    (isConnected_complementHomeomorph_preimage_singleton E)

/-- The induced connected-component homeomorphism sends the class of a point to the class of
its image. -/
@[simp]
theorem connectedComponentsHomeomorph_mk
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid)
    (y : ↥(range (equatorUnlinkPowerLiftContinuousMap m a))ᶜ) :
    E.connectedComponentsHomeomorph (ConnectedComponents.mk y) =
      ConnectedComponents.mk (E.complementHomeomorph y) := by
  exact Topology.IsCoinducing.connectedComponentsHomeomorph_mk _ _ y

/-- The inverse induced homeomorphism sends the class of a point to the class of its inverse
image. -/
@[simp]
theorem connectedComponentsHomeomorph_symm_mk
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid)
    (y : ↥(range
      (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ) :
    E.connectedComponentsHomeomorph.symm (ConnectedComponents.mk y) =
      ConnectedComponents.mk (E.complementHomeomorph.symm y) := by
  apply E.connectedComponentsHomeomorph.injective
  simp

/-- The complement homeomorphism carries the connected component of a complement point exactly
onto the connected component of its image. -/
theorem image_connectedComponent_complementHomeomorph
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid)
    (y : ↥(range (equatorUnlinkPowerLiftContinuousMap m a))ᶜ) :
    E.complementHomeomorph '' connectedComponent y =
      connectedComponent (E.complementHomeomorph y) := by
  exact E.complementHomeomorph.isQuotientMap.isCoinducing.image_connectedComponent
    (isConnected_complementHomeomorph_preimage_singleton E) y

end StandardUnlinkPowerIsotopyLiftAmbientExtension

end SplittingSpheres

end
