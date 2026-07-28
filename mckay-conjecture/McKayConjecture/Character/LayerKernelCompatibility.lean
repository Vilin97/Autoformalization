/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralKernelCompatibility
import McKayConjecture.Character.LayerCharacterClassification
import McKayConjecture.Character.LayerLocalCharacterClassification
import McKayConjecture.GroupTheory.LayerLocalProduct

/-!
# Compatibility across layer and layer-local multiplication kernels

Assume every chosen component-local subgroup `M K` contains the center of
the component `K`.  Since the kernel of layer multiplication is central,
every ambient kernel tuple then lies coordinatewise in `M K`.  Coordinate
inclusion consequently identifies the restricted multiplication kernel
with the ambient layer multiplication kernel.

The generic matched-central-kernel theorem then shows that component
character families satisfying the normalized central cross identity have
simultaneously kernel-trivial finite external tensor characters.  This
gives equivalences between the compatible-family subtypes, both ordinarily
and at `p'`-degree.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

open IrreducibleCharacter

variable (G : Type) [Group G] [Finite G]
variable (M : ∀ K : ComponentIndex G, Subgroup K.1)

noncomputable local instance layerKernelCompatibilityComponentIndexFintype :
    Fintype (ComponentIndex G) :=
  Fintype.ofFinite (ComponentIndex G)

/-! ### Identification of the two multiplication kernels -/

/-- Regard an ambient layer-kernel tuple as a tuple in the local coordinate
groups, using containment of every component center. -/
def layerKernelToLocalTuple
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K)
    (z : (layerProductHom G).ker) :
    ∀ K : ComponentIndex G, M K :=
  fun K ↦
    ⟨z.1 K,
      hcenter K
        (mem_center_coordinate
          (G := fun L : ComponentIndex G ↦ L.1)
          z.1
          (layerProductHom_ker_le_center G z.2)
          K)⟩

@[simp]
theorem layerKernelToLocalTuple_coe
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K)
    (z : (layerProductHom G).ker)
    (K : ComponentIndex G) :
    (layerKernelToLocalTuple G M hcenter z K : K.1) =
      z.1 K :=
  rfl

/-- Coordinate inclusion identifies the restricted layer-local
multiplication kernel with the ambient layer multiplication kernel. -/
def layerLocalKernelEquiv
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K) :
    (layerLocalProductHom G M).ker ≃*
      (layerProductHom G).ker where
  toFun z :=
    ⟨piLocalSubgroupInclusion M z.1,
      (mem_layerLocalProductHom_ker_iff G M z.1).1 z.2⟩
  invFun z :=
    ⟨layerKernelToLocalTuple G M hcenter z, by
      apply
        (mem_layerLocalProductHom_ker_iff G M
          (layerKernelToLocalTuple G M hcenter z)).2
      change z.1 ∈ (layerProductHom G).ker
      exact z.2⟩
  left_inv z := by
    apply Subtype.ext
    funext K
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    funext K
    rfl
  map_mul' x y := by
    apply Subtype.ext
    funext K
    rfl

@[simp]
theorem layerLocalKernelEquiv_apply_coe
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K)
    (z : (layerLocalProductHom G M).ker) :
    (layerLocalKernelEquiv G M hcenter z).1 =
      piLocalSubgroupInclusion M z.1 :=
  rfl

@[simp]
theorem layerLocalKernelEquiv_apply_coordinate
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K)
    (z : (layerLocalProductHom G M).ker)
    (K : ComponentIndex G) :
    (layerLocalKernelEquiv G M hcenter z).1 K =
      (z.1 K : K.1) :=
  rfl

@[simp]
theorem layerLocalKernelEquiv_symm_apply_coordinate
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K)
    (z : (layerProductHom G).ker)
    (K : ComponentIndex G) :
    (((layerLocalKernelEquiv G M hcenter).symm z).1 K :
        K.1) =
      z.1 K :=
  rfl

/-- The restricted multiplication kernel is central in the product of
the coordinate local groups. -/
theorem layerLocalProductHom_ker_le_center :
    (layerLocalProductHom G M).ker ≤
      Subgroup.center
        (∀ K : ComponentIndex G, M K) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro y
  funext K
  apply Subtype.ext
  have hzAmbient :
      piLocalSubgroupInclusion M z ∈
        (layerProductHom G).ker :=
    (mem_layerLocalProductHom_ker_iff G M z).1 hz
  have hzK :
      (z K : K.1) ∈ Subgroup.center K.1 := by
    exact
      mem_center_coordinate
        (G := fun L : ComponentIndex G ↦ L.1)
        (piLocalSubgroupInclusion M z)
        (layerProductHom_ker_le_center G hzAmbient)
        K
  exact
    (Subgroup.mem_center_iff.mp hzK) (y K : K.1)

/-! ### Transfer of compatibility -/

/-- The cross-multiplied equality saying that an ambient component
character and a character of its chosen local subgroup have the same
normalized scalar on central elements of the local subgroup. -/
def ComponentLocalCentralCrossIdentity
    (K : ComponentIndex G)
    (χ : IrreducibleCharacter K.1)
    (ψ : IrreducibleCharacter (M K)) : Prop :=
  ∀ y : M K,
    (y : K.1) ∈ Subgroup.center K.1 →
      χ.values (y : K.1) * (ψ.degree : ℂ) =
        ψ.values y * (χ.degree : ℂ)

/-- Coordinatewise central cross identities for two component-character
families. -/
def LayerLocalCentralCrossIdentity
    (χ : ∀ K : ComponentIndex G,
      IrreducibleCharacter K.1)
    (ψ : ∀ K : ComponentIndex G,
      IrreducibleCharacter (M K)) : Prop :=
  ∀ K : ComponentIndex G,
    ComponentLocalCentralCrossIdentity G M K (χ K) (ψ K)

/-- Under the central cross identity, the ambient and local finite
external tensor characters are simultaneously trivial on their
respective multiplication kernels. -/
theorem finiteExternalTensor_layerKernelCompatible_iff
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K)
    (χ : ∀ K : ComponentIndex G,
      IrreducibleCharacter K.1)
    (ψ : ∀ K : ComponentIndex G,
      IrreducibleCharacter (M K))
    (hcross : LayerLocalCentralCrossIdentity G M χ ψ) :
    (finiteExternalTensor χ).TrivialOn
        (layerProductHom G).ker ↔
      (finiteExternalTensor ψ).TrivialOn
        (layerLocalProductHom G M).ker := by
  exact
    finiteExternalTensor_trivialOn_iff_of_matchedCentralCross
      (fun K : ComponentIndex G ↦ (M K).subtype)
      (layerProductHom G).ker
      (layerLocalProductHom G M).ker
      (layerProductHom_ker_le_center G)
      (layerLocalProductHom_ker_le_center G M)
      (layerLocalKernelEquiv G M hcenter)
      (fun _ _ ↦ rfl)
      χ ψ
      (fun K y hy ↦ hcross K y hy)

/-! ### Compatible-family equivalences -/

/-- Coordinatewise character equivalences preserving the normalized
central scalars induce an equivalence between ambient and local
kernel-compatible families. -/
def layerCompatibleFamilyEquivOfCentralCross
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K)
    (E : ∀ K : ComponentIndex G,
      IrreducibleCharacter K.1 ≃
        IrreducibleCharacter (M K))
    (hE : ∀ (K : ComponentIndex G)
      (χ : IrreducibleCharacter K.1),
      ComponentLocalCentralCrossIdentity G M K χ (E K χ)) :
    LayerCompatibleCharacterFamily G ≃
      LayerLocalCompatibleCharacterFamily G M :=
  (Equiv.piCongrRight E).subtypeEquiv
    (fun χ ↦
      finiteExternalTensor_layerKernelCompatible_iff
        G M hcenter χ (fun K ↦ E K (χ K))
        (fun K ↦ hE K (χ K)))

@[simp]
theorem layerCompatibleFamilyEquivOfCentralCross_apply_coe
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K)
    (E : ∀ K : ComponentIndex G,
      IrreducibleCharacter K.1 ≃
        IrreducibleCharacter (M K))
    (hE : ∀ (K : ComponentIndex G)
      (χ : IrreducibleCharacter K.1),
      ComponentLocalCentralCrossIdentity G M K χ (E K χ))
    (χ : LayerCompatibleCharacterFamily G)
    (K : ComponentIndex G) :
    (layerCompatibleFamilyEquivOfCentralCross
        G M hcenter E hE χ).1 K =
      E K (χ.1 K) :=
  rfl

@[simp]
theorem layerCompatibleFamilyEquivOfCentralCross_symm_apply_coe
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K)
    (E : ∀ K : ComponentIndex G,
      IrreducibleCharacter K.1 ≃
        IrreducibleCharacter (M K))
    (hE : ∀ (K : ComponentIndex G)
      (χ : IrreducibleCharacter K.1),
      ComponentLocalCentralCrossIdentity G M K χ (E K χ))
    (ψ : LayerLocalCompatibleCharacterFamily G M)
    (K : ComponentIndex G) :
    ((layerCompatibleFamilyEquivOfCentralCross
        G M hcenter E hE).symm ψ).1 K =
      (E K).symm (ψ.1 K) :=
  rfl

/-- The induced correspondence between irreducible characters of the
layer and of the layer-local subgroup. -/
def layerCharacterEquivOfCentralCross
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K)
    (E : ∀ K : ComponentIndex G,
      IrreducibleCharacter K.1 ≃
        IrreducibleCharacter (M K))
    (hE : ∀ (K : ComponentIndex G)
      (χ : IrreducibleCharacter K.1),
      ComponentLocalCentralCrossIdentity G M K χ (E K χ)) :
    IrreducibleCharacter (layer G) ≃
      IrreducibleCharacter (layerLocalSubgroup G M) :=
  (layerCharacterEquiv G).symm |>.trans
    ((layerCompatibleFamilyEquivOfCentralCross
      G M hcenter E hE).trans
        (layerLocalCharacterEquiv G M))

/-! ### The `p'`-degree version -/

/-- Coordinatewise equivalences of `p'`-degree characters preserving
central scalars induce an equivalence between the compatible
`p'`-degree families. -/
def layerCompatiblePPrimeFamilyEquivOfCentralCross
    (p : ℕ)
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K)
    (E : ∀ K : ComponentIndex G,
      PPrimeIrreducibleCharacter K.1 p ≃
        PPrimeIrreducibleCharacter (M K) p)
    (hE : ∀ (K : ComponentIndex G)
      (χ : PPrimeIrreducibleCharacter K.1 p),
      ComponentLocalCentralCrossIdentity
        G M K χ.1 (E K χ).1) :
    LayerCompatiblePPrimeCharacterFamily G p ≃
      LayerLocalCompatiblePPrimeCharacterFamily G M p :=
  (Equiv.piCongrRight E).subtypeEquiv
    (fun χ ↦
      finiteExternalTensor_layerKernelCompatible_iff
        G M hcenter
        (fun K ↦ (χ K).1)
        (fun K ↦ (E K (χ K)).1)
        (fun K ↦ hE K (χ K)))

@[simp]
theorem layerCompatiblePPrimeFamilyEquivOfCentralCross_apply_coe
    (p : ℕ)
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K)
    (E : ∀ K : ComponentIndex G,
      PPrimeIrreducibleCharacter K.1 p ≃
        PPrimeIrreducibleCharacter (M K) p)
    (hE : ∀ (K : ComponentIndex G)
      (χ : PPrimeIrreducibleCharacter K.1 p),
      ComponentLocalCentralCrossIdentity
        G M K χ.1 (E K χ).1)
    (χ : LayerCompatiblePPrimeCharacterFamily G p)
    (K : ComponentIndex G) :
    (layerCompatiblePPrimeFamilyEquivOfCentralCross
        G M p hcenter E hE χ).1 K =
      E K (χ.1 K) :=
  rfl

@[simp]
theorem layerCompatiblePPrimeFamilyEquivOfCentralCross_symm_apply_coe
    (p : ℕ)
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K)
    (E : ∀ K : ComponentIndex G,
      PPrimeIrreducibleCharacter K.1 p ≃
        PPrimeIrreducibleCharacter (M K) p)
    (hE : ∀ (K : ComponentIndex G)
      (χ : PPrimeIrreducibleCharacter K.1 p),
      ComponentLocalCentralCrossIdentity
        G M K χ.1 (E K χ).1)
    (ψ : LayerLocalCompatiblePPrimeCharacterFamily G M p)
    (K : ComponentIndex G) :
    ((layerCompatiblePPrimeFamilyEquivOfCentralCross
        G M p hcenter E hE).symm ψ).1 K =
      (E K).symm (ψ.1 K) :=
  rfl

/-- The resulting equivalence between the `p'`-degree irreducible
characters of the layer and of the layer-local subgroup. -/
def layerPPrimeCharacterEquivOfCentralCross
    (p : ℕ) [Fact p.Prime]
    (hcenter : ∀ K, Subgroup.center K.1 ≤ M K)
    (E : ∀ K : ComponentIndex G,
      PPrimeIrreducibleCharacter K.1 p ≃
        PPrimeIrreducibleCharacter (M K) p)
    (hE : ∀ (K : ComponentIndex G)
      (χ : PPrimeIrreducibleCharacter K.1 p),
      ComponentLocalCentralCrossIdentity
        G M K χ.1 (E K χ).1) :
    PPrimeIrreducibleCharacter (layer G) p ≃
      PPrimeIrreducibleCharacter
        (layerLocalSubgroup G M) p :=
  (layerPPrimeCharacterEquiv G p).symm |>.trans
    ((layerCompatiblePPrimeFamilyEquivOfCentralCross
      G M p hcenter E hE).trans
        (layerLocalPPrimeCharacterEquiv G M p))

end GroupTheory
end McKayConjecture
