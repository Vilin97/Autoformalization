/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkSphereIsotopyPowerComplementTransport
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckFullCoverComponents

/-!
# Conditional component transport along a lifted sphere isotopy

The explicit coordinate equator in the full unlink power cover has a rigorously computed
component partition: its complement has two displayed clopen sides, and its component space is
the dependent sum of the component spaces of those sides.  An ambient extension of a lifted
sphere isotopy carries this entire partition to the time-one lifted sphere.

This file composes those two results.  It remains conditional on
`StandardUnlinkPowerIsotopyLiftAmbientExtension`; no ambient isotopy is constructed here.  It also
does not strengthen the displayed partition to exactly two components, since preconnectedness of
the two strict-core sides is not yet known.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

variable {S : SmoothSphereEmbedding 3 4}
variable {m : ℕ} [NeZero m] {a : ZMod m}
variable {H : SmoothSphereIsotopy standardSplittingSphere S}
variable {havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier}

namespace StandardUnlinkPowerIsotopyLiftAmbientExtension

private theorem range_equatorUnlinkPowerLiftContinuousMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range (equatorUnlinkPowerLiftContinuousMap m a) =
      range (equatorUnlinkPowerLift m a) := by
  ext y
  constructor <;> rintro ⟨x, rfl⟩ <;> exact ⟨x, rfl⟩

/-- The components of the time-one lifted-sphere complement, conditionally transported back to
the exact two-side component partition of the initial coordinate equator.

Each `Fin 2` fiber may still contain more than one component. -/
noncomputable def finalConnectedComponentsEquivRestrictedSides
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid) :
    ConnectedComponents
        ↥(range
          (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ ≃
      Σ i : Fin 2,
        ConnectedComponents
          (coordinateUnlinkExteriorPlanarFullCoverEquatorRestrictedSide m a i) :=
  E.connectedComponentsHomeomorph.symm.toEquiv.trans
    (coordinateUnlinkExteriorPlanarFullCoverEquatorConnectedComponentsEquivRestrictedSides
      m a)

/-- On a transported initial component, the final component decomposition has exactly the
original restricted-side label and component. -/
@[simp]
theorem finalConnectedComponentsEquivRestrictedSides_image
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid)
    (c : ConnectedComponents
      ↥(range (equatorUnlinkPowerLiftContinuousMap m a))ᶜ) :
    E.finalConnectedComponentsEquivRestrictedSides
        (E.connectedComponentsHomeomorph c) =
      coordinateUnlinkExteriorPlanarFullCoverEquatorConnectedComponentsEquivRestrictedSides
        m a c := by
  change
    coordinateUnlinkExteriorPlanarFullCoverEquatorConnectedComponentsEquivRestrictedSides
        m a (E.connectedComponentsHomeomorph.symm
          (E.connectedComponentsHomeomorph c)) = _
  rw [E.connectedComponentsHomeomorph.symm_apply_apply]

/-- The time-one lifted-sphere complement has at least two connected components whenever the
lifted isotopy admits the stated ambient extension. -/
theorem nontrivial_connectedComponents_finalComplement
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid) :
    Nontrivial
      (ConnectedComponents
        ↥(range
          (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ) := by
  let _ : Nontrivial
      (ConnectedComponents
        ↥(range (equatorUnlinkPowerLiftContinuousMap m a))ᶜ) := by
    rw [range_equatorUnlinkPowerLiftContinuousMap]
    exact
      nontrivial_connectedComponents_coordinateUnlinkExteriorPlanarFullCoverEquatorComplement
        m a
  exact E.connectedComponentsHomeomorph.toEquiv.symm.nontrivial

/-- Conditional ambient extension preserves the proved failure of preconnectedness of the
selected equator complement. -/
theorem not_preconnectedSpace_finalComplement
    (E : StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid) :
    ¬PreconnectedSpace
      ↥(range
        (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ := by
  intro hfinal
  let _ : PreconnectedSpace
      ↥(range
        (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ := hfinal
  have hfinalUniv : IsPreconnected
      (univ : Set
        ↥(range
          (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ) :=
    isPreconnected_univ
  have hinitialUniv : IsPreconnected
      (univ : Set ↥(range (equatorUnlinkPowerLiftContinuousMap m a))ᶜ) := by
    have hpreimage :=
      E.complementHomeomorph.symm.isPreconnected_image.mpr hfinalUniv
    simpa using hpreimage
  have hinitial : PreconnectedSpace
      ↥(range (equatorUnlinkPowerLiftContinuousMap m a))ᶜ :=
    ⟨hinitialUniv⟩
  have hnot :=
    not_preconnectedSpace_coordinateUnlinkExteriorPlanarFullCoverEquatorComplement m a
  apply hnot
  rw [← range_equatorUnlinkPowerLiftContinuousMap]
  exact hinitial

end StandardUnlinkPowerIsotopyLiftAmbientExtension

end SplittingSpheres
