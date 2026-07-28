/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DependentProductTransport
import McKayConjecture.GroupTheory.ComponentStabilizer
import McKayConjecture.GroupTheory.LayerLocalNormalizerAction
import McKayConjecture.InductiveMcKay.Equivariance
import McKayConjecture.InductiveMcKay.EquivariantTransport
import McKayConjecture.InductiveMcKay.LayerComponentCorrespondenceTarget

/-!
# Equivariance of the componentwise layer correspondence

The componentwise layer correspondence is equivariant under the
ambient normalizer of the selected Sylow subgroup provided that its
coordinate correspondences commute with conjugation between matched
components.  The coordinate law is stated using the canonical
conjugation equivalence of component carriers and its restriction to
the chosen intermediate subgroups.
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
    layerComponentCorrespondenceEquivarianceComponentIndexFintype :
    Fintype (ComponentIndex G) :=
  Fintype.ofFinite (ComponentIndex G)

namespace LayerComponentLocalData

/-- Conjugation restricted from a component to the corresponding
chosen intermediate subgroup. -/
def relativeIntermediateConjugationEquiv
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G) :
    d.intermediate K ≃*
      d.intermediate ((a : G) • K) :=
  ((componentConjugationEquiv G (a : G) K).subgroupMap
      (d.intermediate K)).trans
    (MulEquiv.subgroupCongr (hM a K))

@[simp]
theorem relativeIntermediateConjugationEquiv_apply_coe
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G)
    (x : d.intermediate K) :
    ((d.relativeIntermediateConjugationEquiv
        hM a K x :
      d.intermediate ((a : G) • K)) :
        ((a : G) • K).1) =
      componentConjugationEquiv G (a : G) K x :=
  rfl

@[simp]
theorem relativeIntermediateConjugationEquiv_apply_coe_ambient
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G)
    (x : d.intermediate K) :
    (((d.relativeIntermediateConjugationEquiv
        hM a K x :
      d.intermediate ((a : G) • K)) :
        ((a : G) • K).1) : G) =
      (a : G) * ((x : d.intermediate K) : K.1) *
        (a : G)⁻¹ := by
  rw [relativeIntermediateConjugationEquiv_apply_coe,
    componentConjugationEquiv_apply_coe]

/-- The restricted conjugation equivalences, indexed with the
component-conjugation permutation as their codomain family. -/
def relativeIntermediateConjugationFamily
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (a : LayerSylowAmbientNormalizer G Q) :
    ∀ K : ComponentIndex G,
      d.intermediate K ≃*
        d.intermediate
          (componentConjugationPermutation G (a : G) K) :=
  fun K ↦
    show d.intermediate K ≃*
        d.intermediate
          (componentConjugationPermutation G (a : G) K)
      from d.relativeIntermediateConjugationEquiv hM a K

@[simp]
theorem relativeIntermediateConjugationFamily_apply
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G)
    (x : d.intermediate K) :
    d.relativeIntermediateConjugationFamily hM a K x =
      d.relativeIntermediateConjugationEquiv hM a K x :=
  rfl

/-- Exact coordinate naturality required of the component
correspondences.  Pulling a character on the conjugate component back
to `K` before applying the correspondence agrees with first applying
the correspondence in the conjugate component and then pulling back
along the restricted intermediate-subgroup equivalence. -/
def IsCoordinateCorrespondenceEquivariant
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate) : Prop :=
  ∀ (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G)
    (χ : PPrimeIrreducibleCharacter
      (((a : G) • K).1) p),
    d.correspondence K
        (IrreducibleCharacter.pPrimeComapEquiv p
          (componentConjugationEquiv G (a : G) K) χ) =
      IrreducibleCharacter.pPrimeComapEquiv p
        (d.relativeIntermediateConjugationEquiv hM a K)
        (d.correspondence ((a : G) • K) χ)

/-- The ambient layer-Sylow normalizer action on `p'`-characters of
the layer. -/
@[instance_reducible]
def ambientNormalizerLayerPPrimeCharacterMulAction :
    MulAction (LayerSylowAmbientNormalizer G Q)
      (PPrimeIrreducibleCharacter (layer G) p) :=
  MulAction.compHom _
    (layerSylowAmbientNormalizerLayerAction G Q)

/-- The ambient layer-Sylow normalizer action on `p'`-characters of
the component-local pullback inside the layer. -/
@[instance_reducible]
def ambientNormalizerComponentLocalInLayerPPrimeCharacterMulAction
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate) :
    MulAction (LayerSylowAmbientNormalizer G Q)
      (PPrimeIrreducibleCharacter
        (componentLocalSubgroupInLayer G d.intermediate) p) :=
  MulAction.compHom _
    (layerSylowAmbientNormalizerComponentLocalInLayerAction
      G Q d.intermediate hM)

/-- Transport the component-local pullback action across its canonical
identification with `layerLocalSubgroup`. -/
def ambientNormalizerLayerLocalAction
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate) :
    LayerSylowAmbientNormalizer G Q →*
      MulAut (layerLocalSubgroup G d.intermediate) :=
  (MulAut.congr
      d.componentLocalInLayerEquivLayerLocal).toMonoidHom.comp
    (layerSylowAmbientNormalizerComponentLocalInLayerAction
      G Q d.intermediate hM)

/-- The corresponding induced action on `p'`-characters of
`layerLocalSubgroup`. -/
@[instance_reducible]
def ambientNormalizerLayerLocalPPrimeCharacterMulAction
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate) :
    MulAction (LayerSylowAmbientNormalizer G Q)
      (PPrimeIrreducibleCharacter
        (layerLocalSubgroup G d.intermediate) p) :=
  MulAction.compHom _
    (d.ambientNormalizerLayerLocalAction hM)

@[simp]
theorem componentLocalInLayerEquivLayerLocal_symm_apply_coe
    (d : LayerComponentLocalData D)
    (x : layerLocalSubgroup G d.intermediate) :
    ((((d.componentLocalInLayerEquivLayerLocal).symm x :
        componentLocalSubgroupInLayer G d.intermediate) :
      layer G) : G) =
        (((x : layerLocalSubgroup G d.intermediate) :
          layer G) : G) :=
  rfl

/-- On underlying ambient elements, the transported action on the
layer-local subgroup is conjugation. -/
@[simp]
theorem ambientNormalizerLayerLocalAction_apply_coe
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (a : LayerSylowAmbientNormalizer G Q)
    (x : layerLocalSubgroup G d.intermediate) :
    (((d.ambientNormalizerLayerLocalAction hM a x :
        layerLocalSubgroup G d.intermediate) :
      layer G) : G) =
      (a : G) * (((x : layerLocalSubgroup G d.intermediate) :
        layer G) : G) * (a : G)⁻¹ := by
  change
    (((d.componentLocalInLayerEquivLayerLocal
      (layerSylowAmbientNormalizerComponentLocalInLayerAction
        G Q d.intermediate hM a
        ((d.componentLocalInLayerEquivLayerLocal).symm x)) :
      layerLocalSubgroup G d.intermediate) : layer G) : G) =
      _
  rw [componentLocalInLayerEquivLayerLocal_apply_coe,
    layerSylowAmbientNormalizerComponentLocalInLayerAction_apply_coe,
    componentLocalInLayerEquivLayerLocal_symm_apply_coe]

/-- The dependent product of the restricted intermediate-subgroup
conjugation equivalences. -/
def intermediateProductConjugationEquiv
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (a : LayerSylowAmbientNormalizer G Q) :
    (∀ K : ComponentIndex G, d.intermediate K) ≃*
      (∀ K : ComponentIndex G, d.intermediate K) :=
  IrreducibleCharacter.dependentProductMulEquiv
    (G := fun K : ComponentIndex G ↦ d.intermediate K)
    (H := fun K : ComponentIndex G ↦ d.intermediate K)
    (componentConjugationPermutation G (a : G))
    (d.relativeIntermediateConjugationFamily hM a)

@[simp]
theorem intermediateProductConjugationEquiv_apply_apply
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (a : LayerSylowAmbientNormalizer G Q)
    (x : ∀ K : ComponentIndex G, d.intermediate K)
    (K : ComponentIndex G) :
    d.intermediateProductConjugationEquiv hM a x
        (componentConjugationPermutation G (a : G) K) =
      (show d.intermediate
            (componentConjugationPermutation G (a : G) K)
          from
            d.relativeIntermediateConjugationEquiv hM a K (x K)) := by
  exact
    IrreducibleCharacter.dependentProductMulEquiv_apply_apply
      (G := fun L : ComponentIndex G ↦ d.intermediate L)
      (H := fun L : ComponentIndex G ↦ d.intermediate L)
      (componentConjugationPermutation G (a : G))
      (d.relativeIntermediateConjugationFamily hM a)
      x K

/-- Coordinate inclusion intertwines restricted intermediate-product
transport with conjugation of the full component product. -/
theorem piLocalSubgroupInclusion_intermediateProductConjugation
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (a : LayerSylowAmbientNormalizer G Q)
    (x : ∀ K : ComponentIndex G, d.intermediate K) :
    piLocalSubgroupInclusion d.intermediate
        (d.intermediateProductConjugationEquiv hM a x) =
      layerComponentProductConjugation G (a : G)
        (piLocalSubgroupInclusion d.intermediate x) := by
  funext L
  obtain ⟨K, rfl⟩ :=
    (componentConjugationPermutation G (a : G)).surjective L
  apply Subtype.ext
  change
    ((((d.intermediateProductConjugationEquiv hM a) x
      (componentConjugationPermutation G (a : G) K) :
        d.intermediate
          (componentConjugationPermutation G (a : G) K)) :
      (componentConjugationPermutation G (a : G) K).1) : G) =
      ((layerComponentProductConjugation G (a : G)
        (piLocalSubgroupInclusion d.intermediate x)
        (componentConjugationPermutation G (a : G) K) :
          (componentConjugationPermutation G (a : G) K).1) : G)
  rw [intermediateProductConjugationEquiv_apply_apply]
  change
    ((((d.relativeIntermediateConjugationEquiv hM a K) (x K) :
        d.intermediate ((a : G) • K)) :
      ((a : G) • K).1) : G) =
      ((layerComponentProductConjugation G (a : G)
        (piLocalSubgroupInclusion d.intermediate x)
        ((a : G) • K) : ((a : G) • K).1) : G)
  rw [relativeIntermediateConjugationEquiv_apply_coe_ambient,
    layerComponentProductConjugation_apply_coe]
  have hindex :
      (a : G)⁻¹ • ((a : G) • K) = K :=
    inv_smul_smul (a : G) K
  have hcoe :
      (((piLocalSubgroupInclusion d.intermediate x)
          ((a : G)⁻¹ • ((a : G) • K)) :
        ((a : G)⁻¹ • ((a : G) • K)).1) : G) =
        ((x K : d.intermediate K) : K.1) := by
    rw [hindex]
    rfl
  rw [hcoe]

/-- Restricted component multiplication intertwines the dependent
intermediate-product action with the transported action on the
layer-local subgroup. -/
theorem layerLocalProductHom_comp_intermediateProductConjugation
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (a : LayerSylowAmbientNormalizer G Q) :
    (layerLocalProductHom G d.intermediate).comp
        (d.intermediateProductConjugationEquiv
          hM a).toMonoidHom =
      (d.ambientNormalizerLayerLocalAction
        hM a).toMonoidHom.comp
        (layerLocalProductHom G d.intermediate) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change
    ((layerProductHom G
      (piLocalSubgroupInclusion d.intermediate
        (d.intermediateProductConjugationEquiv hM a x)) :
      layer G) : G) =
      _
  rw [piLocalSubgroupInclusion_intermediateProductConjugation]
  have hproduct :=
    DFunLike.congr_fun
      (layerProductHom_comp_conjugation G (a : G))
      (piLocalSubgroupInclusion d.intermediate x)
  calc
    ((layerProductHom G
        (layerComponentProductConjugation G (a : G)
          (piLocalSubgroupInclusion d.intermediate x)) :
      layer G) : G) =
        (((MulAut.conjNormal (a : G) :
            MulAut (layer G))
          (layerProductHom G
            (piLocalSubgroupInclusion d.intermediate x)) :
          layer G) : G) :=
      congrArg (fun y : layer G => (y : G)) hproduct
    _ = (a : G) *
          (((layerLocalProductHom G d.intermediate x :
              layerLocalSubgroup G d.intermediate) :
            layer G) : G) *
          (a : G)⁻¹ :=
      rfl
    _ =
        (((d.ambientNormalizerLayerLocalAction hM a
          (layerLocalProductHom G d.intermediate x) :
            layerLocalSubgroup G d.intermediate) :
          layer G) : G) :=
      (ambientNormalizerLayerLocalAction_apply_coe
        d hM a
        (layerLocalProductHom G d.intermediate x)).symm

/-- The component-character family classified by a `p'`-character of
the layer. -/
def layerCoordinatePPrimeFamily
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    ∀ K : ComponentIndex G,
      PPrimeIrreducibleCharacter K.1 p :=
  ((GroupTheory.layerPPrimeCharacterEquiv G p).symm θ).1

@[simp]
theorem layerCoordinatePPrimeFamily_apply
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :
    layerCoordinatePPrimeFamily θ K =
      ((GroupTheory.layerPPrimeCharacterEquiv G p).symm θ).1 K :=
  rfl

/-- The family of intermediate-subgroup characters obtained by
applying the selected coordinate correspondences. -/
def localCoordinatePPrimeFamily
    (d : LayerComponentLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    ∀ K : ComponentIndex G,
      PPrimeIrreducibleCharacter (d.intermediate K) p :=
  fun K ↦ d.correspondence K (layerCoordinatePPrimeFamily θ K)

@[simp]
theorem localCoordinatePPrimeFamily_apply
    (d : LayerComponentLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :
    d.localCoordinatePPrimeFamily θ K =
      d.correspondence K
        (((GroupTheory.layerPPrimeCharacterEquiv G p).symm θ).1 K) :=
  rfl

/-- Under arbitrary ambient conjugation, the component-character family
classified by a layer character is obtained by dependent pullback from the
inversely conjugated component family. -/
theorem layerPPrimeCoordinateFamily_ambient_smul
    (g : G)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    layerCoordinatePPrimeFamily (g • θ) =
      IrreducibleCharacter.dependentProductPPrimeEquiv p
        (componentConjugationPermutation G g⁻¹)
        (fun K ↦
          show K.1 ≃*
              (componentConjugationPermutation G g⁻¹ K).1
            from componentConjugationEquiv G g⁻¹ K)
        (layerCoordinatePPrimeFamily θ) := by
  let e :=
    componentConjugationPermutation G g⁻¹
  let c :
      ∀ K : ComponentIndex G,
        K.1 ≃* (e K).1 :=
    fun K ↦
      show K.1 ≃*
          (componentConjugationPermutation G g⁻¹ K).1
        from componentConjugationEquiv G g⁻¹ K
  change
    layerCoordinatePPrimeFamily (g • θ) =
      IrreducibleCharacter.dependentProductPPrimeEquiv
        p e c (layerCoordinatePPrimeFamily θ)
  apply
    (IrreducibleCharacter.finiteProductPPrimeEquiv
      (fun K : ComponentIndex G ↦ K.1) p).injective
  have hnatural :
      IrreducibleCharacter.pPrimeComapEquiv p
          (IrreducibleCharacter.dependentProductMulEquiv e c)
            (IrreducibleCharacter.finiteProductPPrimeEquiv
            (fun K : ComponentIndex G ↦ K.1) p
            (layerCoordinatePPrimeFamily θ)) =
        IrreducibleCharacter.finiteProductPPrimeEquiv
            (fun K : ComponentIndex G ↦ K.1) p
          (IrreducibleCharacter.dependentProductPPrimeEquiv
            p e c (layerCoordinatePPrimeFamily θ)) :=
    IrreducibleCharacter.finiteProductPPrimeEquiv_comap_dependentProduct
        (G := fun K : ComponentIndex G ↦ K.1)
        (H := fun K : ComponentIndex G ↦ K.1)
        p e c
        (layerCoordinatePPrimeFamily θ)
  refine Eq.trans ?_ hnatural
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext x
  have hinv :
      (MulAut.conjNormal (H := layer G) g).symm =
        MulAut.conjNormal (H := layer G) g⁻¹ := by
    symm
    exact map_inv (MulAut.conjNormal (H := layer G)) g
  have hproduct :=
    DFunLike.congr_fun
      (layerProductHom_comp_conjugation G g⁻¹) x
  calc
    (IrreducibleCharacter.finiteProductPPrimeEquiv
        (fun K : ComponentIndex G ↦ K.1) p
        ((GroupTheory.layerPPrimeCharacterEquiv
          G p).symm (g • θ)).1).1.values x =
        (g • θ).1.values (layerProductHom G x) := by
      rw [IrreducibleCharacter.finiteProductPPrimeEquiv_apply,
        IrreducibleCharacter.finiteExternalTensorPPrime_coe,
        GroupTheory.layerPPrimeCharacterEquiv_symm_finiteExternalTensor_values]
    _ = θ.1.values
          ((MulAut.conjNormal (H := layer G) g).symm
            (layerProductHom G x)) :=
      rfl
    _ = θ.1.values
          (layerProductHom G
            (layerComponentProductConjugation G g⁻¹ x)) := by
      apply congrArg θ.1.values
      rw [hinv]
      exact hproduct.symm
    _ =
        (IrreducibleCharacter.finiteProductPPrimeEquiv
          (fun K : ComponentIndex G ↦ K.1) p
          ((GroupTheory.layerPPrimeCharacterEquiv
            G p).symm θ).1).1.values
            (layerComponentProductConjugation G g⁻¹ x) := by
      rw [IrreducibleCharacter.finiteProductPPrimeEquiv_apply,
        IrreducibleCharacter.finiteExternalTensorPPrime_coe,
        GroupTheory.layerPPrimeCharacterEquiv_symm_finiteExternalTensor_values]
    _ =
        (IrreducibleCharacter.pPrimeComapEquiv p
          (IrreducibleCharacter.dependentProductMulEquiv e c)
          (IrreducibleCharacter.finiteProductPPrimeEquiv
            (fun K : ComponentIndex G ↦ K.1) p
            ((GroupTheory.layerPPrimeCharacterEquiv
              G p).symm θ).1)).1.values x := by
      rw [IrreducibleCharacter.dependentProductMulEquiv_componentConjugation]
      rfl

/-- A component normalizer element which fixes a layer character also fixes
the corresponding component character. -/
theorem layerCoordinatePPrimeCharacter_fixed
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G)
    (g : Subgroup.normalizer (K.1 : Set G))
    (hθ : (g : G) • θ = θ) :
    componentNormalizerAction G K g •
        layerCoordinatePPrimeFamily θ K =
      layerCoordinatePPrimeFamily θ K := by
  have hginv :
      (g : G)⁻¹ ∈ MulAction.stabilizer G K := by
    rw [component_stabilizer_eq_normalizer G K]
    exact (Subgroup.normalizer (K.1 : Set G)).inv_mem g.2
  have hfixed :
      (g : G) • K = K := by
    rw [← MulAction.mem_stabilizer_iff,
      component_stabilizer_eq_normalizer G K]
    exact g.2
  have hfixedInv :
      (g : G)⁻¹ • K = K :=
    MulAction.mem_stabilizer_iff.mp hginv
  have hfamily :=
    congrFun
      (layerPPrimeCoordinateFamily_ambient_smul
        (G := G) (p := p) (g : G) θ) ((g : G) • K)
  rw [hθ, IrreducibleCharacter.dependentProductPPrimeEquiv_apply]
    at hfamily
  rw [hfixed] at hfamily
  change
    layerCoordinatePPrimeFamily θ K =
      IrreducibleCharacter.pPrimeComapEquiv p
        (componentConjugationEquiv G (g : G)⁻¹ K)
        (layerCoordinatePPrimeFamily θ ((g : G)⁻¹ • K))
    at hfamily
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext x
  have hsigma :
      (⟨(g : G)⁻¹ • K,
          (layerCoordinatePPrimeFamily θ
            ((g : G)⁻¹ • K)).1.values⟩ :
        Σ J : ComponentIndex G, J.1 → ℂ) =
        ⟨K, (layerCoordinatePPrimeFamily θ K).1.values⟩ :=
    congrArg
      (fun J : ComponentIndex G ↦
        (⟨J, (layerCoordinatePPrimeFamily θ J).1.values⟩ :
          Σ L : ComponentIndex G, L.1 → ℂ))
      hfixedInv
  have hfunctions :
      HEq
          (layerCoordinatePPrimeFamily θ
            ((g : G)⁻¹ • K)).1.values
          (layerCoordinatePPrimeFamily θ K).1.values :=
    (Sigma.mk.inj_iff.mp hsigma).2
  have hsubgroup :
      ((g : G)⁻¹ • K).1 = K.1 :=
    congrArg (fun J : ComponentIndex G ↦ J.1) hfixedInv
  have helement :
      HEq
          (componentConjugationEquiv G (g : G)⁻¹ K x)
          ((componentNormalizerAction G K g).symm x) := by
    apply
      (Subtype.heq_iff_coe_eq
        (fun y : G ↦ by rw [hsubgroup])).2
    rw [componentConjugationEquiv_apply_coe]
    rfl
  have htransport :
      (layerCoordinatePPrimeFamily θ
          ((g : G)⁻¹ • K)).1.values
          (componentConjugationEquiv G (g : G)⁻¹ K x) =
        (layerCoordinatePPrimeFamily θ K).1.values
          ((componentNormalizerAction G K g).symm x) :=
    congr_heq hfunctions helement
  have hvalue :=
    congrArg
      (fun χ : PPrimeIrreducibleCharacter K.1 p ↦ χ.1.values x)
      hfamily
  exact htransport.symm.trans hvalue.symm

/-- Under the normalizer action, the component-character family
classified by a layer character is obtained by dependent pullback from
the inversely conjugated component family. -/
theorem layerPPrimeCoordinateFamily_smul
    (_d : LayerComponentLocalData D)
    (a : LayerSylowAmbientNormalizer G Q)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    letI := ambientNormalizerLayerPPrimeCharacterMulAction
      (G := G) (p := p) (Q := Q)
    layerCoordinatePPrimeFamily (a • θ) =
      IrreducibleCharacter.dependentProductPPrimeEquiv p
        (componentConjugationPermutation G ((a⁻¹ : _) : G))
        (fun K ↦
          show K.1 ≃*
              (componentConjugationPermutation
                G ((a⁻¹ : _) : G) K).1
            from componentConjugationEquiv
              G ((a⁻¹ : _) : G) K)
        (layerCoordinatePPrimeFamily θ) := by
  letI := ambientNormalizerLayerPPrimeCharacterMulAction
    (G := G) (p := p) (Q := Q)
  let e :=
    componentConjugationPermutation G ((a⁻¹ : _) : G)
  let c :
      ∀ K : ComponentIndex G,
        K.1 ≃* (e K).1 :=
    fun K ↦
      show K.1 ≃*
          (componentConjugationPermutation
            G ((a⁻¹ : _) : G) K).1
        from componentConjugationEquiv
          G ((a⁻¹ : _) : G) K
  change
    layerCoordinatePPrimeFamily (a • θ) =
      IrreducibleCharacter.dependentProductPPrimeEquiv
        p e c (layerCoordinatePPrimeFamily θ)
  apply
    (IrreducibleCharacter.finiteProductPPrimeEquiv
      (fun K : ComponentIndex G ↦ K.1) p).injective
  have hnatural :
      IrreducibleCharacter.pPrimeComapEquiv p
          (IrreducibleCharacter.dependentProductMulEquiv e c)
            (IrreducibleCharacter.finiteProductPPrimeEquiv
            (fun K : ComponentIndex G ↦ K.1) p
            (layerCoordinatePPrimeFamily θ)) =
        IrreducibleCharacter.finiteProductPPrimeEquiv
            (fun K : ComponentIndex G ↦ K.1) p
          (IrreducibleCharacter.dependentProductPPrimeEquiv
            p e c (layerCoordinatePPrimeFamily θ)) :=
    IrreducibleCharacter.finiteProductPPrimeEquiv_comap_dependentProduct
        (G := fun K : ComponentIndex G ↦ K.1)
        (H := fun K : ComponentIndex G ↦ K.1)
        p e c
        (layerCoordinatePPrimeFamily θ)
  refine Eq.trans ?_ hnatural
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext x
  have hinv :
      (layerSylowAmbientNormalizerLayerAction
        G Q a).symm =
        layerSylowAmbientNormalizerLayerAction
          G Q a⁻¹ := by
    symm
    exact
      map_inv
        (layerSylowAmbientNormalizerLayerAction G Q) a
  have hproduct :=
    DFunLike.congr_fun
      (layerProductHom_comp_conjugation
        G ((a⁻¹ : _) : G)) x
  calc
    (IrreducibleCharacter.finiteProductPPrimeEquiv
        (fun K : ComponentIndex G ↦ K.1) p
        ((GroupTheory.layerPPrimeCharacterEquiv
          G p).symm (a • θ)).1).1.values x =
        (a • θ).1.values (layerProductHom G x) := by
      rw [IrreducibleCharacter.finiteProductPPrimeEquiv_apply,
        IrreducibleCharacter.finiteExternalTensorPPrime_coe,
        GroupTheory.layerPPrimeCharacterEquiv_symm_finiteExternalTensor_values]
    _ = θ.1.values
          ((layerSylowAmbientNormalizerLayerAction
            G Q a).symm (layerProductHom G x)) :=
      rfl
    _ = θ.1.values
          (layerProductHom G
            (layerComponentProductConjugation
              G ((a⁻¹ : _) : G) x)) := by
      apply congrArg θ.1.values
      rw [hinv]
      exact hproduct.symm
    _ =
        (IrreducibleCharacter.finiteProductPPrimeEquiv
          (fun K : ComponentIndex G ↦ K.1) p
          ((GroupTheory.layerPPrimeCharacterEquiv
            G p).symm θ).1).1.values
            (layerComponentProductConjugation
              G ((a⁻¹ : _) : G) x) := by
      rw [IrreducibleCharacter.finiteProductPPrimeEquiv_apply,
        IrreducibleCharacter.finiteExternalTensorPPrime_coe,
        GroupTheory.layerPPrimeCharacterEquiv_symm_finiteExternalTensor_values]
    _ =
        (IrreducibleCharacter.pPrimeComapEquiv p
          (IrreducibleCharacter.dependentProductMulEquiv e c)
          (IrreducibleCharacter.finiteProductPPrimeEquiv
            (fun K : ComponentIndex G ↦ K.1) p
            ((GroupTheory.layerPPrimeCharacterEquiv
              G p).symm θ).1)).1.values x := by
      rw [IrreducibleCharacter.dependentProductMulEquiv_componentConjugation]
      rfl

/-- Coordinate naturality upgrades the transport law for component
characters to the family obtained after applying all coordinate
correspondences. -/
theorem coordinateCorrespondenceFamily_smul
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (hcoordinate :
      d.IsCoordinateCorrespondenceEquivariant hM)
    (a : LayerSylowAmbientNormalizer G Q)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    letI := ambientNormalizerLayerPPrimeCharacterMulAction
      (G := G) (p := p) (Q := Q)
    d.localCoordinatePPrimeFamily (a • θ) =
      IrreducibleCharacter.dependentProductPPrimeEquiv p
        (componentConjugationPermutation G ((a⁻¹ : _) : G))
        (d.relativeIntermediateConjugationFamily hM a⁻¹)
        (d.localCoordinatePPrimeFamily θ) := by
  letI := ambientNormalizerLayerPPrimeCharacterMulAction
    (G := G) (p := p) (Q := Q)
  funext K
  have hsource :=
    congrFun (d.layerPPrimeCoordinateFamily_smul a θ) K
  have hsource' :
      ((GroupTheory.layerPPrimeCharacterEquiv G p).symm
          (a • θ)).1 K =
        IrreducibleCharacter.pPrimeComapEquiv p
          (componentConjugationEquiv
            G ((a⁻¹ : _) : G) K)
          (((GroupTheory.layerPPrimeCharacterEquiv G p).symm θ).1
            ((a⁻¹ : LayerSylowAmbientNormalizer G Q) • K)) := by
    change
      layerCoordinatePPrimeFamily (a • θ) K =
        IrreducibleCharacter.pPrimeComapEquiv p
          (componentConjugationEquiv
            G ((a⁻¹ : _) : G) K)
          (layerCoordinatePPrimeFamily θ
            ((a⁻¹ : LayerSylowAmbientNormalizer G Q) • K))
    rw [hsource]
    rfl
  rw [IrreducibleCharacter.dependentProductPPrimeEquiv_apply]
  simp only [localCoordinatePPrimeFamily_apply]
  rw [hsource']
  exact
    hcoordinate a⁻¹ K
      (layerCoordinatePPrimeFamily θ
        ((a⁻¹ : LayerSylowAmbientNormalizer G Q) • K))

/-- Product-of-values form of coordinate naturality.  Reindexing by
component conjugation changes the product of the transported family
into evaluation of the original family on the conjugated product
coordinate. -/
theorem localCoordinatePPrimeFamily_values_smul
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (hcoordinate :
      d.IsCoordinateCorrespondenceEquivariant hM)
    (a : LayerSylowAmbientNormalizer G Q)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (x : ∀ K : ComponentIndex G, d.intermediate K) :
    letI := ambientNormalizerLayerPPrimeCharacterMulAction
      (G := G) (p := p) (Q := Q)
    ∏ K,
        (d.localCoordinatePPrimeFamily (a • θ) K).1.values (x K) =
      ∏ K,
        (d.localCoordinatePPrimeFamily θ K).1.values
          ((d.intermediateProductConjugationEquiv hM a⁻¹ x) K) := by
  letI := ambientNormalizerLayerPPrimeCharacterMulAction
    (G := G) (p := p) (Q := Q)
  let e :=
    componentConjugationPermutation G ((a⁻¹ : _) : G)
  have hfamily :=
    d.coordinateCorrespondenceFamily_smul
      hM hcoordinate a θ
  calc
    ∏ K,
        (d.localCoordinatePPrimeFamily (a • θ) K).1.values
          (x K) =
      ∏ K,
        ((IrreducibleCharacter.dependentProductPPrimeEquiv p e
          (d.relativeIntermediateConjugationFamily hM a⁻¹)
          (d.localCoordinatePPrimeFamily θ)) K).1.values
            (x K) := by
      rw [hfamily]
    _ =
      ∏ K,
        (d.localCoordinatePPrimeFamily θ (e K)).1.values
          (d.relativeIntermediateConjugationFamily
            hM a⁻¹ K (x K)) := by
      apply Finset.prod_congr rfl
      intro K _
      rfl
    _ =
      ∏ K,
        (d.localCoordinatePPrimeFamily θ (e K)).1.values
          ((d.intermediateProductConjugationEquiv
            hM a⁻¹ x) (e K)) := by
      apply Finset.prod_congr rfl
      intro K _
      rw [intermediateProductConjugationEquiv_apply_apply]
      rfl
    _ =
      ∏ K,
        (d.localCoordinatePPrimeFamily θ K).1.values
          ((d.intermediateProductConjugationEquiv
            hM a⁻¹ x) K) :=
      Equiv.prod_comp e
        (fun K ↦
          (d.localCoordinatePPrimeFamily θ K).1.values
            ((d.intermediateProductConjugationEquiv
              hM a⁻¹ x) K))

/-- Value form of componentwise equivariance before passage to the
quotient product: conjugating the layer character transports the
coordinate tensor by inverse product conjugation. -/
theorem layerPPrimeCharacterEquiv_values_smul_product
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (hcoordinate :
      d.IsCoordinateCorrespondenceEquivariant hM)
    (a : LayerSylowAmbientNormalizer G Q)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (x : ∀ K : ComponentIndex G, d.intermediate K) :
    letI := ambientNormalizerLayerPPrimeCharacterMulAction
      (G := G) (p := p) (Q := Q)
    (d.layerPPrimeCharacterEquiv (a • θ)).1.values
        (layerLocalProductHom G d.intermediate x) =
      (d.layerPPrimeCharacterEquiv θ).1.values
        (layerLocalProductHom G d.intermediate
          (d.intermediateProductConjugationEquiv
            hM a⁻¹ x)) := by
  letI := ambientNormalizerLayerPPrimeCharacterMulAction
    (G := G) (p := p) (Q := Q)
  rw [d.layerPPrimeCharacterEquiv_values_layerLocalProduct,
    d.layerPPrimeCharacterEquiv_values_layerLocalProduct]
  exact
    d.localCoordinatePPrimeFamily_values_smul
      hM hcoordinate a θ x

/-- The componentwise layer correspondence intertwines the ambient
normalizer action on the layer with the transported action on the
coordinate-product local subgroup. -/
theorem layerPPrimeCharacterEquiv_map_smul
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (hcoordinate :
      d.IsCoordinateCorrespondenceEquivariant hM) :
    letI := ambientNormalizerLayerPPrimeCharacterMulAction
      (G := G) (p := p) (Q := Q)
    letI := d.ambientNormalizerLayerLocalPPrimeCharacterMulAction hM
    ∀ (a : LayerSylowAmbientNormalizer G Q)
      (θ : PPrimeIrreducibleCharacter (layer G) p),
      d.layerPPrimeCharacterEquiv (a • θ) =
        a • d.layerPPrimeCharacterEquiv θ := by
  letI := ambientNormalizerLayerPPrimeCharacterMulAction
    (G := G) (p := p) (Q := Q)
  letI := d.ambientNormalizerLayerLocalPPrimeCharacterMulAction hM
  intro a θ
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext y
  obtain ⟨x, rfl⟩ :=
    layerLocalProductHom_surjective
      (G := G) (M := d.intermediate) y
  have hinv :
      (d.ambientNormalizerLayerLocalAction hM a).symm =
        d.ambientNormalizerLayerLocalAction hM a⁻¹ := by
    symm
    exact map_inv (d.ambientNormalizerLayerLocalAction hM) a
  have hproduct :=
    DFunLike.congr_fun
      (d.layerLocalProductHom_comp_intermediateProductConjugation
        hM a⁻¹) x
  calc
    (d.layerPPrimeCharacterEquiv (a • θ)).1.values
        (layerLocalProductHom G d.intermediate x) =
        (d.layerPPrimeCharacterEquiv θ).1.values
          (layerLocalProductHom G d.intermediate
            (d.intermediateProductConjugationEquiv
              hM a⁻¹ x)) :=
      d.layerPPrimeCharacterEquiv_values_smul_product
        hM hcoordinate a θ x
    _ =
        (d.layerPPrimeCharacterEquiv θ).1.values
          (d.ambientNormalizerLayerLocalAction hM a⁻¹
            (layerLocalProductHom G d.intermediate x)) := by
      exact
        congrArg
          (d.layerPPrimeCharacterEquiv θ).1.values hproduct
    _ =
        (d.layerPPrimeCharacterEquiv θ).1.values
          ((d.ambientNormalizerLayerLocalAction hM a).symm
            (layerLocalProductHom G d.intermediate x)) := by
      rw [hinv]
    _ =
        (a • d.layerPPrimeCharacterEquiv θ).1.values
          (layerLocalProductHom G d.intermediate x) :=
      rfl

/-- The correspondence with the coordinate-product model, bundled
with its ambient-normalizer equivariance. -/
def equivariantLayerPPrimeCorrespondence
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (hcoordinate :
      d.IsCoordinateCorrespondenceEquivariant hM) :
    letI := ambientNormalizerLayerPPrimeCharacterMulAction
      (G := G) (p := p) (Q := Q)
    letI := d.ambientNormalizerLayerLocalPPrimeCharacterMulAction hM
    EquivariantPPrimeCorrespondence
      (LayerSylowAmbientNormalizer G Q) p
      (layer G) (layerLocalSubgroup G d.intermediate) := by
  letI := ambientNormalizerLayerPPrimeCharacterMulAction
    (G := G) (p := p) (Q := Q)
  letI := d.ambientNormalizerLayerLocalPPrimeCharacterMulAction hM
  exact
    { toCorrespondence := d.layerPPrimeCharacterEquiv
      map_smul' :=
        d.layerPPrimeCharacterEquiv_map_smul
          hM hcoordinate }

@[simp]
theorem equivariantLayerPPrimeCorrespondence_apply
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (hcoordinate :
      d.IsCoordinateCorrespondenceEquivariant hM)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    letI := ambientNormalizerLayerPPrimeCharacterMulAction
      (G := G) (p := p) (Q := Q)
    letI := d.ambientNormalizerLayerLocalPPrimeCharacterMulAction hM
    d.equivariantLayerPPrimeCorrespondence
        hM hcoordinate θ =
      d.layerPPrimeCharacterEquiv θ :=
  rfl

/-- Transporting from the coordinate-product model to the explicit
component-local pullback preserves ambient-normalizer equivariance. -/
theorem componentLocalPPrimeCharacterEquiv_map_smul
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (hcoordinate :
      d.IsCoordinateCorrespondenceEquivariant hM) :
    letI := ambientNormalizerLayerPPrimeCharacterMulAction
      (G := G) (p := p) (Q := Q)
    letI :=
      d.ambientNormalizerComponentLocalInLayerPPrimeCharacterMulAction hM
    ∀ (a : LayerSylowAmbientNormalizer G Q)
      (θ : PPrimeIrreducibleCharacter (layer G) p),
      d.componentLocalPPrimeCharacterEquiv (a • θ) =
        a • d.componentLocalPPrimeCharacterEquiv θ := by
  letI := ambientNormalizerLayerPPrimeCharacterMulAction
    (G := G) (p := p) (Q := Q)
  letI :=
    d.ambientNormalizerComponentLocalInLayerPPrimeCharacterMulAction hM
  intro a θ
  rw [componentLocalPPrimeCharacterEquiv_apply,
    d.layerPPrimeCharacterEquiv_map_smul hM hcoordinate]
  change
    IrreducibleCharacter.pPrimeComapEquiv p
        d.componentLocalInLayerEquivLayerLocal
        ((MulAut.congr d.componentLocalInLayerEquivLayerLocal
          (layerSylowAmbientNormalizerComponentLocalInLayerAction
            G Q d.intermediate hM a)) •
          d.layerPPrimeCharacterEquiv θ) =
      (layerSylowAmbientNormalizerComponentLocalInLayerAction
        G Q d.intermediate hM a) •
        IrreducibleCharacter.pPrimeComapEquiv p
          d.componentLocalInLayerEquivLayerLocal
          (d.layerPPrimeCharacterEquiv θ)
  exact
    pPrimeComapEquiv_congr_smul
      d.componentLocalInLayerEquivLayerLocal p
      (layerSylowAmbientNormalizerComponentLocalInLayerAction
        G Q d.intermediate hM a)
      (d.layerPPrimeCharacterEquiv θ)

/-- The explicit component-local layer correspondence, bundled with
the ambient layer-Sylow normalizer action. -/
def equivariantComponentLocalPPrimeCorrespondence
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (hcoordinate :
      d.IsCoordinateCorrespondenceEquivariant hM) :
    letI := ambientNormalizerLayerPPrimeCharacterMulAction
      (G := G) (p := p) (Q := Q)
    letI :=
      d.ambientNormalizerComponentLocalInLayerPPrimeCharacterMulAction hM
    EquivariantPPrimeCorrespondence
      (LayerSylowAmbientNormalizer G Q) p
      (layer G)
      (componentLocalSubgroupInLayer G d.intermediate) := by
  letI := ambientNormalizerLayerPPrimeCharacterMulAction
    (G := G) (p := p) (Q := Q)
  letI :=
    d.ambientNormalizerComponentLocalInLayerPPrimeCharacterMulAction hM
  exact
    { toCorrespondence := d.componentLocalPPrimeCharacterEquiv
      map_smul' :=
        d.componentLocalPPrimeCharacterEquiv_map_smul
          hM hcoordinate }

@[simp]
theorem equivariantComponentLocalPPrimeCorrespondence_apply
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (hcoordinate :
      d.IsCoordinateCorrespondenceEquivariant hM)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    letI := ambientNormalizerLayerPPrimeCharacterMulAction
      (G := G) (p := p) (Q := Q)
    letI :=
      d.ambientNormalizerComponentLocalInLayerPPrimeCharacterMulAction hM
    d.equivariantComponentLocalPPrimeCorrespondence
        hM hcoordinate θ =
      d.componentLocalPPrimeCharacterEquiv θ :=
  rfl

end LayerComponentLocalData
end InductiveMcKay
end McKayConjecture
