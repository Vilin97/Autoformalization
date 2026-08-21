/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkComplementAmbientIsotopyExtension
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckIsotopyComponentTransport

/-!
# Exact components after an unlink-avoiding sphere isotopy

The ambient-extension construction for normalized unlink-avoiding sphere isotopies discharges the
only hypothesis in the conditional component-transport layer.  Consequently the complement of the
time-one lifted sphere in every finite cyclic power cover has exactly two connected components,
canonically labelled by `Fin 2`, and is not preconnected.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

variable {S : SmoothSphereEmbedding 3 4}

/-- The final lifted-sphere complement components, identified with the two restricted coordinate
sides of the initial equator complement. -/
noncomputable def
    standardUnlinkPowerIsotopyLiftFinalConnectedComponentsEquivRestrictedSides
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ConnectedComponents
        ↥(range
          (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ ≃
      Σ i : Fin 2,
        ConnectedComponents
          (coordinateUnlinkExteriorPlanarFullCoverEquatorRestrictedSide m a i) :=
  (standardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid)
    |>.finalConnectedComponentsEquivRestrictedSides

/-- The complement of the time-one lifted sphere has exactly the two component labels `Fin 2`. -/
noncomputable def standardUnlinkPowerIsotopyLiftFinalConnectedComponentsEquivFinTwo
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ConnectedComponents
        ↥(range
          (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ ≃
      Fin 2 :=
  (standardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid)
    |>.finalConnectedComponentsEquivFinTwo

/-- The complement of the time-one lifted sphere has exactly two connected components. -/
theorem natCard_connectedComponents_standardUnlinkPowerIsotopyLiftFinalComplement
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    Nat.card
      (ConnectedComponents
        ↥(range
          (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ) = 2 :=
  (standardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid)
    |>.natCard_connectedComponents_finalComplement

/-- The space of connected components of the time-one lifted-sphere complement is nontrivial. -/
theorem nontrivial_connectedComponents_standardUnlinkPowerIsotopyLiftFinalComplement
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    Nontrivial
      (ConnectedComponents
        ↥(range
          (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ) :=
  (standardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid)
    |>.nontrivial_connectedComponents_finalComplement

/-- The complement of the time-one lifted sphere is not preconnected. -/
theorem not_preconnectedSpace_standardUnlinkPowerIsotopyLiftFinalComplement
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ¬PreconnectedSpace
      ↥(range
        (standardUnlinkPowerIsotopyLiftFinalContinuousMap m a H havoid))ᶜ :=
  (standardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid)
    |>.not_preconnectedSpace_finalComplement

end SplittingSpheres
