/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralQuotientProductClassification
import McKayConjecture.GroupTheory.LayerLocalProduct

/-!
# Irreducible characters of layer-local product subgroups

For a finite Type-0 group `G` and chosen subgroups `M K ≤ K` in every
component, the indexed product `∀ K, M K` maps surjectively onto
`layerLocalSubgroup G M`.  Quotient-product character classification
therefore identifies irreducible characters of this image with families
whose finite external tensor character is trivial on the exact restricted
multiplication kernel.

That kernel is the preimage of the ambient layer multiplication kernel
under coordinatewise inclusion.  It is not asserted to equal the ambient
kernel, since the two subgroups live in different product groups.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace GroupTheory

open IrreducibleCharacter

variable (G : Type) [Group G] [Finite G]
variable (M : ∀ K : ComponentIndex G, Subgroup K.1)

noncomputable local instance layerLocalComponentIndexFintype :
    Fintype (ComponentIndex G) :=
  Fintype.ofFinite (ComponentIndex G)

/-! ### Compatible local-component character families -/

/-- A family of irreducible characters of the coordinate local groups is
compatible when its finite external tensor character is trivial on the
kernel of restricted component multiplication. -/
abbrev LayerLocalCompatibleCharacterFamily :=
  KernelCompatibleCharacterFamily
    (fun K : ComponentIndex G ↦ M K)
    (layerLocalProductHom G M)

/-- The kernel governing layer-local character compatibility is exactly
the preimage of the ambient layer multiplication kernel. -/
theorem layerLocalCharacterKernel :
    (layerLocalProductHom G M).ker =
      (layerProductHom G).ker.comap
        (piLocalSubgroupInclusion M) :=
  layerLocalProductHom_ker G M

/-! ### Ordinary irreducible characters -/

/-- Compatible coordinate-local character families classify irreducible
characters of the layer-local product subgroup. -/
def layerLocalCharacterEquiv :
    LayerLocalCompatibleCharacterFamily G M ≃
      IrreducibleCharacter (layerLocalSubgroup G M) :=
  quotientProductCharacterEquiv
    (fun K : ComponentIndex G ↦ M K)
    (layerLocalProductHom G M)
    (layerLocalProductHom_surjective G M)

@[simp]
theorem layerLocalCharacterEquiv_apply
    (χ : LayerLocalCompatibleCharacterFamily G M) :
    layerLocalCharacterEquiv G M χ =
      quotientProductCharacterEquiv
        (fun K : ComponentIndex G ↦ M K)
        (layerLocalProductHom G M)
        (layerLocalProductHom_surjective G M)
        χ :=
  rfl

@[simp]
theorem layerLocalCharacterEquiv_symm_apply
    (θ : IrreducibleCharacter (layerLocalSubgroup G M)) :
    (layerLocalCharacterEquiv G M).symm θ =
      (quotientProductCharacterEquiv
        (fun K : ComponentIndex G ↦ M K)
        (layerLocalProductHom G M)
        (layerLocalProductHom_surjective G M)).symm θ :=
  rfl

@[simp]
theorem layerLocalCharacterEquiv_values_componentProduct
    (χ : LayerLocalCompatibleCharacterFamily G M)
    (x : ∀ K : ComponentIndex G, M K) :
    (layerLocalCharacterEquiv G M χ).values
        (layerLocalProductHom G M x) =
      ∏ K, (χ.1 K).values (x K) :=
  quotientProductCharacterEquiv_values_apply
    (fun K : ComponentIndex G ↦ M K)
    (layerLocalProductHom G M)
    (layerLocalProductHom_surjective G M)
    χ x

@[simp]
theorem layerLocalCharacterEquiv_degree
    (χ : LayerLocalCompatibleCharacterFamily G M) :
    (layerLocalCharacterEquiv G M χ).degree =
      ∏ K, (χ.1 K).degree :=
  quotientProductCharacterEquiv_degree
    (fun K : ComponentIndex G ↦ M K)
    (layerLocalProductHom G M)
    (layerLocalProductHom_surjective G M)
    χ

@[simp]
theorem layerLocalCharacterEquiv_apply_symm_apply
    (θ : IrreducibleCharacter (layerLocalSubgroup G M)) :
    layerLocalCharacterEquiv G M
        ((layerLocalCharacterEquiv G M).symm θ) =
      θ :=
  (layerLocalCharacterEquiv G M).apply_symm_apply θ

@[simp]
theorem layerLocalCharacterEquiv_symm_apply_apply
    (χ : LayerLocalCompatibleCharacterFamily G M) :
    (layerLocalCharacterEquiv G M).symm
        (layerLocalCharacterEquiv G M χ) =
      χ :=
  (layerLocalCharacterEquiv G M).symm_apply_apply χ

@[simp]
theorem layerLocalCharacterEquiv_symm_finiteExternalTensor_values
    (θ : IrreducibleCharacter (layerLocalSubgroup G M))
    (x : ∀ K : ComponentIndex G, M K) :
    (finiteExternalTensor
        ((layerLocalCharacterEquiv G M).symm θ).1).values x =
      θ.values (layerLocalProductHom G M x) :=
  quotientProductCharacterEquiv_symm_finiteExternalTensor_values
    (fun K : ComponentIndex G ↦ M K)
    (layerLocalProductHom G M)
    (layerLocalProductHom_surjective G M)
    θ x

@[simp]
theorem layerLocalCharacterEquiv_symm_finiteExternalTensor_degree
    (θ : IrreducibleCharacter (layerLocalSubgroup G M)) :
    (finiteExternalTensor
        ((layerLocalCharacterEquiv G M).symm θ).1).degree =
      θ.degree :=
  quotientProductCharacterEquiv_symm_finiteExternalTensor_degree
    (fun K : ComponentIndex G ↦ M K)
    (layerLocalProductHom G M)
    (layerLocalProductHom_surjective G M)
    θ

/-! ### Characters of `p'`-degree -/

/-- Compatible families of `p'`-degree irreducible characters of the
coordinate local groups. -/
abbrev LayerLocalCompatiblePPrimeCharacterFamily (p : ℕ) :=
  KernelCompatiblePPrimeCharacterFamily
    (fun K : ComponentIndex G ↦ M K)
    (layerLocalProductHom G M)
    p

/-- Compatible `p'`-degree coordinate-local character families classify
the `p'`-degree irreducible characters of the layer-local subgroup. -/
def layerLocalPPrimeCharacterEquiv
    (p : ℕ) [Fact p.Prime] :
    LayerLocalCompatiblePPrimeCharacterFamily G M p ≃
      PPrimeIrreducibleCharacter (layerLocalSubgroup G M) p :=
  pPrimeQuotientProductCharacterEquiv
    (fun K : ComponentIndex G ↦ M K)
    (layerLocalProductHom G M)
    (layerLocalProductHom_surjective G M)
    p

@[simp]
theorem layerLocalPPrimeCharacterEquiv_apply_coe
    (p : ℕ) [Fact p.Prime]
    (χ : LayerLocalCompatiblePPrimeCharacterFamily G M p) :
    (layerLocalPPrimeCharacterEquiv G M p χ).1 =
      layerLocalCharacterEquiv G M
        (compatiblePPrimeFamilyToCompatibleFamily
          (fun K : ComponentIndex G ↦ M K)
          (layerLocalProductHom G M) p χ) :=
  rfl

@[simp]
theorem layerLocalPPrimeCharacterEquiv_values_componentProduct
    (p : ℕ) [Fact p.Prime]
    (χ : LayerLocalCompatiblePPrimeCharacterFamily G M p)
    (x : ∀ K : ComponentIndex G, M K) :
    (layerLocalPPrimeCharacterEquiv G M p χ).1.values
        (layerLocalProductHom G M x) =
      ∏ K, (χ.1 K).1.values (x K) :=
  pPrimeQuotientProductCharacterEquiv_values_apply
    (fun K : ComponentIndex G ↦ M K)
    (layerLocalProductHom G M)
    (layerLocalProductHom_surjective G M)
    p χ x

@[simp]
theorem layerLocalPPrimeCharacterEquiv_degree
    (p : ℕ) [Fact p.Prime]
    (χ : LayerLocalCompatiblePPrimeCharacterFamily G M p) :
    (layerLocalPPrimeCharacterEquiv G M p χ).1.degree =
      ∏ K, (χ.1 K).1.degree :=
  pPrimeQuotientProductCharacterEquiv_degree
    (fun K : ComponentIndex G ↦ M K)
    (layerLocalProductHom G M)
    (layerLocalProductHom_surjective G M)
    p χ

@[simp]
theorem layerLocalPPrimeCharacterEquiv_apply_symm_apply
    (p : ℕ) [Fact p.Prime]
    (θ : PPrimeIrreducibleCharacter
      (layerLocalSubgroup G M) p) :
    layerLocalPPrimeCharacterEquiv G M p
        ((layerLocalPPrimeCharacterEquiv G M p).symm θ) =
      θ :=
  (layerLocalPPrimeCharacterEquiv G M p).apply_symm_apply θ

@[simp]
theorem layerLocalPPrimeCharacterEquiv_symm_apply_apply
    (p : ℕ) [Fact p.Prime]
    (χ : LayerLocalCompatiblePPrimeCharacterFamily G M p) :
    (layerLocalPPrimeCharacterEquiv G M p).symm
        (layerLocalPPrimeCharacterEquiv G M p χ) =
      χ :=
  (layerLocalPPrimeCharacterEquiv G M p).symm_apply_apply χ

@[simp]
theorem
    layerLocalPPrimeCharacterEquiv_symm_finiteExternalTensor_values
    (p : ℕ) [Fact p.Prime]
    (θ : PPrimeIrreducibleCharacter
      (layerLocalSubgroup G M) p)
    (x : ∀ K : ComponentIndex G, M K) :
    (finiteExternalTensor
        (fun K ↦
          (((layerLocalPPrimeCharacterEquiv G M p).symm θ).1 K).1)).values x =
      θ.1.values (layerLocalProductHom G M x) :=
  pPrimeQuotientProductCharacterEquiv_symm_finiteExternalTensor_values
    (fun K : ComponentIndex G ↦ M K)
    (layerLocalProductHom G M)
    (layerLocalProductHom_surjective G M)
    p θ x

@[simp]
theorem
    layerLocalPPrimeCharacterEquiv_symm_finiteExternalTensor_degree
    (p : ℕ) [Fact p.Prime]
    (θ : PPrimeIrreducibleCharacter
      (layerLocalSubgroup G M) p) :
    (finiteExternalTensor
        (fun K ↦
          (((layerLocalPPrimeCharacterEquiv G M p).symm θ).1 K).1)).degree =
      θ.1.degree :=
  pPrimeQuotientProductCharacterEquiv_symm_finiteExternalTensor_degree
    (fun K : ComponentIndex G ↦ M K)
    (layerLocalProductHom G M)
    (layerLocalProductHom_surjective G M)
    p θ

end GroupTheory
end McKayConjecture
