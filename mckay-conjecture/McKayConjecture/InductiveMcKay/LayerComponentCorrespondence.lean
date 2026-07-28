/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.LayerKernelCompatibility
import McKayConjecture.InductiveMcKay.CentralQuotientTriviality
import McKayConjecture.InductiveMcKay.LayerComponentLocalData

/-!
# Componentwise local correspondence for the layer

Full local inductive-McKay data on every component supplies a
coordinatewise `p'`-character correspondence.  Central character-triple
compatibility gives exactly the cross-multiplied central-scalar identity
needed to preserve the multiplication-kernel compatibility condition.

The coordinate correspondences therefore restrict to compatible
families, and quotient-product classification turns the resulting family
equivalence into an explicit correspondence

`Irr_{p'}(E(G)) ≃ Irr_{p'}(E_M(G))`

for the layer-local subgroup assembled from the coordinate
intermediates.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}
variable {D : LayerSylowCoordinateData G p Q}

noncomputable local instance
    layerComponentCorrespondenceComponentIndexFintype :
    Fintype (ComponentIndex G) :=
  Fintype.ofFinite (ComponentIndex G)

namespace LayerComponentLocalData

/-- The component correspondence has the central cross identity in the
orientation ambient component to coordinate-local intermediate. -/
theorem coordinate_correspondence_central_cross
    (d : LayerComponentLocalData D)
    (K : ComponentIndex G)
    (χ : PPrimeIrreducibleCharacter K.1 p) :
    ComponentLocalCentralCrossIdentity
      G d.intermediate K χ.1
        (d.correspondence K χ).1 := by
  intro y hy
  exact
    (d.data K).correspondence_central_cross
      χ (y : K.1) hy y.2

/-- The coordinatewise component correspondences restrict to an
equivalence between the ambient and layer-local kernel-compatible
`p'`-character families. -/
def compatiblePPrimeFamilyEquiv
    (d : LayerComponentLocalData D) :
    LayerCompatiblePPrimeCharacterFamily G p ≃
      LayerLocalCompatiblePPrimeCharacterFamily
        G d.intermediate p :=
  layerCompatiblePPrimeFamilyEquivOfCentralCross
    G d.intermediate p d.center_le_intermediate
      d.correspondence
      (fun K χ ↦
        d.coordinate_correspondence_central_cross K χ)

@[simp]
theorem compatiblePPrimeFamilyEquiv_apply_coordinate
    (d : LayerComponentLocalData D)
    (χ : LayerCompatiblePPrimeCharacterFamily G p)
    (K : ComponentIndex G) :
    (d.compatiblePPrimeFamilyEquiv χ).1 K =
      d.correspondence K (χ.1 K) :=
  rfl

@[simp]
theorem compatiblePPrimeFamilyEquiv_symm_apply_coordinate
    (d : LayerComponentLocalData D)
    (ψ :
      LayerLocalCompatiblePPrimeCharacterFamily
        G d.intermediate p)
    (K : ComponentIndex G) :
    (d.compatiblePPrimeFamilyEquiv.symm ψ).1 K =
      (d.correspondence K).symm (ψ.1 K) :=
  rfl

/-- The explicit `p'`-character correspondence from the layer to the
layer-local subgroup assembled from the coordinate intermediates. -/
def layerPPrimeCharacterEquiv
    (d : LayerComponentLocalData D) :
    PPrimeIrreducibleCharacter (layer G) p ≃
      PPrimeIrreducibleCharacter
        (layerLocalSubgroup G d.intermediate) p :=
  (GroupTheory.layerPPrimeCharacterEquiv G p).symm |>.trans
    (d.compatiblePPrimeFamilyEquiv.trans
      (layerLocalPPrimeCharacterEquiv
        G d.intermediate p))

@[simp]
theorem layerPPrimeCharacterEquiv_apply
    (d : LayerComponentLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    d.layerPPrimeCharacterEquiv θ =
      layerLocalPPrimeCharacterEquiv
        G d.intermediate p
        (d.compatiblePPrimeFamilyEquiv
          ((GroupTheory.layerPPrimeCharacterEquiv
            G p).symm θ)) :=
  rfl

/-- Values of the layer-local image on a coordinate product are the
product of the values of the matched coordinate characters. -/
@[simp]
theorem layerPPrimeCharacterEquiv_values_layerLocalProduct
    (d : LayerComponentLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (x : ∀ K : ComponentIndex G, d.intermediate K) :
    (d.layerPPrimeCharacterEquiv θ).1.values
        (layerLocalProductHom G d.intermediate x) =
      ∏ K,
        (d.correspondence K
          (((GroupTheory.layerPPrimeCharacterEquiv
            G p).symm θ).1 K)).1.values (x K) := by
  rw [layerPPrimeCharacterEquiv_apply,
    layerLocalPPrimeCharacterEquiv_values_componentProduct]
  rfl

/-- The degree of the layer-local image is the product of the degrees of
the matched coordinate characters. -/
@[simp]
theorem layerPPrimeCharacterEquiv_degree
    (d : LayerComponentLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    (d.layerPPrimeCharacterEquiv θ).1.degree =
      ∏ K,
        (d.correspondence K
          (((GroupTheory.layerPPrimeCharacterEquiv
            G p).symm θ).1 K)).1.degree := by
  rw [layerPPrimeCharacterEquiv_apply,
    layerLocalPPrimeCharacterEquiv_degree]
  rfl

end LayerComponentLocalData
end InductiveMcKay
end McKayConjecture
