/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.LayerLocalSubgroupIdentification
import McKayConjecture.InductiveMcKay.LayerComponentCorrespondence

/-!
# The componentwise layer correspondence with its ambiently generated target

The componentwise correspondence initially lands in the subgroup
constructed as the image of the coordinate product.  The identification
of that subgroup with the pullback of the ambiently generated
component-local subgroup transports the correspondence to the target
used by the layer intermediate construction.
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
    layerComponentCorrespondenceTargetComponentIndexFintype :
    Fintype (ComponentIndex G) :=
  Fintype.ofFinite (ComponentIndex G)

namespace LayerComponentLocalData

/-- The canonical multiplicative equivalence from the pulled-back
ambient component-local subgroup to the coordinate-product subgroup. -/
def componentLocalInLayerEquivLayerLocal
    (d : LayerComponentLocalData D) :
    componentLocalSubgroupInLayer G d.intermediate ≃*
      layerLocalSubgroup G d.intermediate :=
  MulEquiv.subgroupCongr
    (layerLocalSubgroup_eq_componentLocalSubgroupInLayer
      G d.intermediate).symm

@[simp]
theorem componentLocalInLayerEquivLayerLocal_apply_coe
    (d : LayerComponentLocalData D)
    (x : componentLocalSubgroupInLayer G d.intermediate) :
    ((d.componentLocalInLayerEquivLayerLocal x :
        layerLocalSubgroup G d.intermediate) :
      layer G) =
        x :=
  rfl

/-- The explicit `p'`-character correspondence from the layer to the
component-local subgroup used by the layer intermediate construction. -/
def componentLocalPPrimeCharacterEquiv
    (d : LayerComponentLocalData D) :
    PPrimeIrreducibleCharacter (layer G) p ≃
      PPrimeIrreducibleCharacter
        (componentLocalSubgroupInLayer G d.intermediate) p :=
  d.layerPPrimeCharacterEquiv.trans
    (IrreducibleCharacter.pPrimeComapEquiv p
      d.componentLocalInLayerEquivLayerLocal)

@[simp]
theorem componentLocalPPrimeCharacterEquiv_apply
    (d : LayerComponentLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    d.componentLocalPPrimeCharacterEquiv θ =
      IrreducibleCharacter.pPrimeComapEquiv p
        d.componentLocalInLayerEquivLayerLocal
        (d.layerPPrimeCharacterEquiv θ) :=
  rfl

@[simp]
theorem componentLocalPPrimeCharacterEquiv_apply_coe
    (d : LayerComponentLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    (d.componentLocalPPrimeCharacterEquiv θ).1 =
      (d.layerPPrimeCharacterEquiv θ).1.comap
        d.componentLocalInLayerEquivLayerLocal :=
  rfl

@[simp]
theorem componentLocalPPrimeCharacterEquiv_symm_apply
    (d : LayerComponentLocalData D)
    (ψ : PPrimeIrreducibleCharacter
      (componentLocalSubgroupInLayer G d.intermediate) p) :
    d.componentLocalPPrimeCharacterEquiv.symm ψ =
      d.layerPPrimeCharacterEquiv.symm
        ((IrreducibleCharacter.pPrimeComapEquiv p
          d.componentLocalInLayerEquivLayerLocal).symm ψ) :=
  rfl

/-- Transport to the explicit component-local target preserves the
degree formula supplied by the coordinate correspondence. -/
@[simp]
theorem componentLocalPPrimeCharacterEquiv_degree
    (d : LayerComponentLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    (d.componentLocalPPrimeCharacterEquiv θ).1.degree =
      ∏ K,
        (d.correspondence K
          (((GroupTheory.layerPPrimeCharacterEquiv
            G p).symm θ).1 K)).1.degree := by
  rw [componentLocalPPrimeCharacterEquiv_apply,
    IrreducibleCharacter.pPrimeComapEquiv_degree,
    layerPPrimeCharacterEquiv_degree]

end LayerComponentLocalData
end InductiveMcKay
end McKayConjecture
