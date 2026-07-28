/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerComponentCorrespondenceTarget
import McKayConjecture.InductiveMcKay.LayerIntermediateReduction

/-!
# The layer correspondence inside the layer intermediate

The componentwise correspondence for the layer naturally lands in the
component-local subgroup pulled back to `E(G)`.  The same subgroup occurs as
a normal subgroup of the layer intermediate

`componentLocalSubgroup G M ⊔ N_G(Q)`.

This file transports the layer correspondence to that internal normal
subgroup.  Keeping the target internal to the intermediate is what makes the
result suitable for Clifford theory in the next reduction step.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}
variable {D : LayerSylowCoordinateData G p Q}

noncomputable local instance
    layerIntermediateCorrespondenceComponentIndexFintype :
    Fintype (ComponentIndex G) :=
  Fintype.ofFinite (ComponentIndex G)

namespace ComponentOrbitLocalData

/-- The componentwise layer correspondence, with target the component-local
normal subgroup internal to the layer intermediate. -/
def intermediateComponentLocalPPrimeCharacterEquiv
    (d : ComponentOrbitLocalData D) :
    PPrimeIrreducibleCharacter (layer G) p ≃
      PPrimeIrreducibleCharacter
        d.intermediateComponentLocal p :=
  d.toLayerComponentLocalData.componentLocalPPrimeCharacterEquiv.trans
    (IrreducibleCharacter.pPrimeComapEquiv p
      d.intermediateComponentLocalEquivInLayer)

@[simp]
theorem intermediateComponentLocalPPrimeCharacterEquiv_apply
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    d.intermediateComponentLocalPPrimeCharacterEquiv θ =
      IrreducibleCharacter.pPrimeComapEquiv p
        d.intermediateComponentLocalEquivInLayer
        (d.toLayerComponentLocalData
          |>.componentLocalPPrimeCharacterEquiv θ) :=
  rfl

@[simp]
theorem intermediateComponentLocalPPrimeCharacterEquiv_apply_coe
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1 =
      (d.toLayerComponentLocalData
        |>.componentLocalPPrimeCharacterEquiv θ).1.comap
          d.intermediateComponentLocalEquivInLayer :=
  rfl

@[simp]
theorem intermediateComponentLocalPPrimeCharacterEquiv_symm_apply
    (d : ComponentOrbitLocalData D)
    (ψ :
      PPrimeIrreducibleCharacter
        d.intermediateComponentLocal p) :
    d.intermediateComponentLocalPPrimeCharacterEquiv.symm ψ =
      (d.toLayerComponentLocalData
        |>.componentLocalPPrimeCharacterEquiv).symm
          ((IrreducibleCharacter.pPrimeComapEquiv p
            d.intermediateComponentLocalEquivInLayer).symm ψ) :=
  rfl

/-- Transport into the layer intermediate does not change character degree. -/
@[simp]
theorem intermediateComponentLocalPPrimeCharacterEquiv_degree
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1.degree =
      ∏ K,
        (d.correspondence K
          (((GroupTheory.layerPPrimeCharacterEquiv
            G p).symm θ).1 K)).1.degree := by
  calc
    (d.intermediateComponentLocalPPrimeCharacterEquiv
        θ).1.degree =
        (d.toLayerComponentLocalData
          |>.componentLocalPPrimeCharacterEquiv θ).1.degree :=
      rfl
    _ = ∏ K,
          (d.correspondence K
            (((GroupTheory.layerPPrimeCharacterEquiv
              G p).symm θ).1 K)).1.degree := by
      exact
        d.toLayerComponentLocalData
          |>.componentLocalPPrimeCharacterEquiv_degree θ

end ComponentOrbitLocalData
end InductiveMcKay
end McKayConjecture
