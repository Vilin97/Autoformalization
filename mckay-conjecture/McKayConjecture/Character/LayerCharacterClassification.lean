/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralQuotientProductClassification
import McKayConjecture.GroupTheory.LayerCentralProduct

/-!
# Irreducible characters of the layer

For a finite Type-0 group `G`, the layer `E(G)` is the surjective image of
the external direct product of all components under `layerProductHom G`.
Specializing quotient-product character classification identifies
irreducible characters of `E(G)` with component-character families whose
finite external tensor character is trivial on the multiplication kernel.

The same specialization is recorded for characters of `p'`-degree.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace GroupTheory

open IrreducibleCharacter

variable (G : Type) [Group G] [Finite G]

noncomputable local instance componentIndexFintype :
    Fintype (ComponentIndex G) :=
  Fintype.ofFinite (ComponentIndex G)

/-! ### Compatible component-character families -/

/-- A family of irreducible characters of the components is compatible
with layer multiplication when its finite external tensor character is
trivial on the kernel of `layerProductHom G`. -/
abbrev LayerCompatibleCharacterFamily :=
  KernelCompatibleCharacterFamily
    (fun K : ComponentIndex G ↦ K.1)
    (layerProductHom G)

/-- The first-isomorphism-theorem equivalence used by generic quotient
classification is the canonical quotient description of the layer. -/
theorem layer_surjectiveQuotientEquiv_eq :
    surjectiveQuotientEquiv
        (fun K : ComponentIndex G ↦ K.1)
        (layerProductHom G)
        (layerProductHom_surjective G) =
      layerProductQuotientEquiv G :=
  rfl

/-! ### Ordinary irreducible characters -/

/-- Kernel-compatible component-character families classify the
irreducible characters of the layer. -/
def layerCharacterEquiv :
    LayerCompatibleCharacterFamily G ≃
      IrreducibleCharacter (layer G) :=
  quotientProductCharacterEquiv
    (fun K : ComponentIndex G ↦ K.1)
    (layerProductHom G)
    (layerProductHom_surjective G)

@[simp]
theorem layerCharacterEquiv_apply
    (χ : LayerCompatibleCharacterFamily G) :
    layerCharacterEquiv G χ =
      quotientProductCharacterEquiv
        (fun K : ComponentIndex G ↦ K.1)
        (layerProductHom G)
        (layerProductHom_surjective G)
        χ :=
  rfl

@[simp]
theorem layerCharacterEquiv_symm_apply
    (θ : IrreducibleCharacter (layer G)) :
    (layerCharacterEquiv G).symm θ =
      (quotientProductCharacterEquiv
        (fun K : ComponentIndex G ↦ K.1)
        (layerProductHom G)
        (layerProductHom_surjective G)).symm θ :=
  rfl

@[simp]
theorem layerCharacterEquiv_values_componentProduct
    (χ : LayerCompatibleCharacterFamily G)
    (x : ∀ K : ComponentIndex G, K.1) :
    (layerCharacterEquiv G χ).values
        (layerProductHom G x) =
      ∏ K, (χ.1 K).values (x K) :=
  quotientProductCharacterEquiv_values_apply
    (fun K : ComponentIndex G ↦ K.1)
    (layerProductHom G)
    (layerProductHom_surjective G)
    χ x

@[simp]
theorem layerCharacterEquiv_degree
    (χ : LayerCompatibleCharacterFamily G) :
    (layerCharacterEquiv G χ).degree =
      ∏ K, (χ.1 K).degree :=
  quotientProductCharacterEquiv_degree
    (fun K : ComponentIndex G ↦ K.1)
    (layerProductHom G)
    (layerProductHom_surjective G)
    χ

@[simp]
theorem layerCharacterEquiv_apply_symm_apply
    (θ : IrreducibleCharacter (layer G)) :
    layerCharacterEquiv G ((layerCharacterEquiv G).symm θ) =
      θ :=
  (layerCharacterEquiv G).apply_symm_apply θ

@[simp]
theorem layerCharacterEquiv_symm_apply_apply
    (χ : LayerCompatibleCharacterFamily G) :
    (layerCharacterEquiv G).symm (layerCharacterEquiv G χ) =
      χ :=
  (layerCharacterEquiv G).symm_apply_apply χ

@[simp]
theorem layerCharacterEquiv_symm_finiteExternalTensor_values
    (θ : IrreducibleCharacter (layer G))
    (x : ∀ K : ComponentIndex G, K.1) :
    (finiteExternalTensor
        ((layerCharacterEquiv G).symm θ).1).values x =
      θ.values (layerProductHom G x) :=
  quotientProductCharacterEquiv_symm_finiteExternalTensor_values
    (fun K : ComponentIndex G ↦ K.1)
    (layerProductHom G)
    (layerProductHom_surjective G)
    θ x

@[simp]
theorem layerCharacterEquiv_symm_finiteExternalTensor_degree
    (θ : IrreducibleCharacter (layer G)) :
    (finiteExternalTensor
        ((layerCharacterEquiv G).symm θ).1).degree =
      θ.degree :=
  quotientProductCharacterEquiv_symm_finiteExternalTensor_degree
    (fun K : ComponentIndex G ↦ K.1)
    (layerProductHom G)
    (layerProductHom_surjective G)
    θ

/-! ### Characters of `p'`-degree -/

/-- Compatible families of `p'`-degree irreducible component
characters. -/
abbrev LayerCompatiblePPrimeCharacterFamily (p : ℕ) :=
  KernelCompatiblePPrimeCharacterFamily
    (fun K : ComponentIndex G ↦ K.1)
    (layerProductHom G)
    p

/-- Compatible `p'`-degree component-character families classify the
`p'`-degree irreducible characters of the layer. -/
def layerPPrimeCharacterEquiv
    (p : ℕ) [Fact p.Prime] :
    LayerCompatiblePPrimeCharacterFamily G p ≃
      PPrimeIrreducibleCharacter (layer G) p :=
  pPrimeQuotientProductCharacterEquiv
    (fun K : ComponentIndex G ↦ K.1)
    (layerProductHom G)
    (layerProductHom_surjective G)
    p

@[simp]
theorem layerPPrimeCharacterEquiv_apply_coe
    (p : ℕ) [Fact p.Prime]
    (χ : LayerCompatiblePPrimeCharacterFamily G p) :
    (layerPPrimeCharacterEquiv G p χ).1 =
      layerCharacterEquiv G
        (compatiblePPrimeFamilyToCompatibleFamily
          (fun K : ComponentIndex G ↦ K.1)
          (layerProductHom G) p χ) :=
  rfl

@[simp]
theorem layerPPrimeCharacterEquiv_values_componentProduct
    (p : ℕ) [Fact p.Prime]
    (χ : LayerCompatiblePPrimeCharacterFamily G p)
    (x : ∀ K : ComponentIndex G, K.1) :
    (layerPPrimeCharacterEquiv G p χ).1.values
        (layerProductHom G x) =
      ∏ K, (χ.1 K).1.values (x K) :=
  pPrimeQuotientProductCharacterEquiv_values_apply
    (fun K : ComponentIndex G ↦ K.1)
    (layerProductHom G)
    (layerProductHom_surjective G)
    p χ x

@[simp]
theorem layerPPrimeCharacterEquiv_degree
    (p : ℕ) [Fact p.Prime]
    (χ : LayerCompatiblePPrimeCharacterFamily G p) :
    (layerPPrimeCharacterEquiv G p χ).1.degree =
      ∏ K, (χ.1 K).1.degree :=
  pPrimeQuotientProductCharacterEquiv_degree
    (fun K : ComponentIndex G ↦ K.1)
    (layerProductHom G)
    (layerProductHom_surjective G)
    p χ

@[simp]
theorem layerPPrimeCharacterEquiv_apply_symm_apply
    (p : ℕ) [Fact p.Prime]
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    layerPPrimeCharacterEquiv G p
        ((layerPPrimeCharacterEquiv G p).symm θ) =
      θ :=
  (layerPPrimeCharacterEquiv G p).apply_symm_apply θ

@[simp]
theorem layerPPrimeCharacterEquiv_symm_apply_apply
    (p : ℕ) [Fact p.Prime]
    (χ : LayerCompatiblePPrimeCharacterFamily G p) :
    (layerPPrimeCharacterEquiv G p).symm
        (layerPPrimeCharacterEquiv G p χ) =
      χ :=
  (layerPPrimeCharacterEquiv G p).symm_apply_apply χ

@[simp]
theorem layerPPrimeCharacterEquiv_symm_finiteExternalTensor_values
    (p : ℕ) [Fact p.Prime]
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (x : ∀ K : ComponentIndex G, K.1) :
    (finiteExternalTensor
        (fun K ↦
          (((layerPPrimeCharacterEquiv G p).symm θ).1 K).1)).values x =
      θ.1.values (layerProductHom G x) :=
  pPrimeQuotientProductCharacterEquiv_symm_finiteExternalTensor_values
    (fun K : ComponentIndex G ↦ K.1)
    (layerProductHom G)
    (layerProductHom_surjective G)
    p θ x

@[simp]
theorem layerPPrimeCharacterEquiv_symm_finiteExternalTensor_degree
    (p : ℕ) [Fact p.Prime]
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    (finiteExternalTensor
        (fun K ↦
          (((layerPPrimeCharacterEquiv G p).symm θ).1 K).1)).degree =
      θ.1.degree :=
  pPrimeQuotientProductCharacterEquiv_symm_finiteExternalTensor_degree
    (fun K : ComponentIndex G ↦ K.1)
    (layerProductHom G)
    (layerProductHom_surjective G)
    p θ

end GroupTheory
end McKayConjecture
