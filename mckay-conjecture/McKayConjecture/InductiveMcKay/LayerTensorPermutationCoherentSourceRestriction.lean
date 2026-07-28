/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteTensorQuotientRepresentation
import McKayConjecture.InductiveMcKay.LayerCoordinateCharacterTransportValues
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCoherentNormalTrace

/-!
# Intrinsic source restriction of the coherent tensor construction

The coherent source normal operators come from an ordinary representation
of the layer.  This file constructs that representation directly: each
component is transported back to the selected representative of its target
inertia orbit, the representative normal restrictions are tensored, and the
result descends through layer multiplication.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace McKayConjecture
namespace InductiveMcKay
namespace LayerProjectiveRestrictionAssembly

open CharacterTriple
open GroupTheory
open CategoryTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}
variable {D : LayerSylowCoordinateData G p Q}
variable
  {d : ComponentOrbitLocalData D}
  {hcoordinate :
    d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
      d.isConjugationEquivariantUnder}
  {θ : PPrimeIrreducibleCharacter (layer G) p}

noncomputable local instance coherentSourceRestrictionComponentIndexFintype :
    Fintype (ComponentIndex G) :=
  Fintype.ofFinite (ComponentIndex G)

noncomputable local instance coherentSourceRestrictionOrbitTensorModuleFinite
    (o : LayerTargetComponentOrbit d θ) :
    Module.Finite ℂ
      (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
        canonicalOrbitSourceSpace d θ o) :=
  ProjectiveRepresentation.piTensorModuleFinite

noncomputable local instance coherentSourceRestrictionOrbitTensorNontrivial
    (o : LayerTargetComponentOrbit d θ) :
    Nontrivial
      (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
        canonicalOrbitSourceSpace d θ o) :=
  ProjectiveRepresentation.piTensorNontrivial

/-- Conjugation by the selected target-inertia transporter identifies the
chosen representative component with the requested component. -/
def layerTargetComponentTransportEquiv
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :
    (layerTargetComponentOrbitRepresentative d θ
      (layerTargetComponentOrbitOf d θ K)).1 ≃*
        K.1 := by
  let t :=
    layerTargetComponentTransporter d θ K
  let tG : G :=
    (((t : targetInertiaGroup d θ) :
      d.ambientIntermediate) : G)
  let R :=
    layerTargetComponentOrbitRepresentative d θ
      (layerTargetComponentOrbitOf d θ K)
  have ht : tG • R = K := by
    exact layerTargetComponentTransporter_smul_representative d θ K
  exact
    (componentConjugationEquiv G tG R).trans
      (MulEquiv.subgroupCongr (congrArg Subtype.val ht))

@[simp]
theorem layerTargetComponentTransportEquiv_apply_coe
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G)
    (x :
      (layerTargetComponentOrbitRepresentative d θ
        (layerTargetComponentOrbitOf d θ K)).1) :
    ((layerTargetComponentTransportEquiv d θ K x : K.1) : G) =
      ((((layerTargetComponentTransporter d θ K :
        targetInertiaGroup d θ) : d.ambientIntermediate) : G)) *
        (x : G) *
      ((((layerTargetComponentTransporter d θ K :
        targetInertiaGroup d θ) : d.ambientIntermediate) : G))⁻¹ := by
  simp only [layerTargetComponentTransportEquiv,
    MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    componentConjugationEquiv_apply_coe]

/-- Orbit-indexed form of the selected component transport equivalence. -/
def layerTargetOrbitCoordinateTransportEquiv
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o) :
    (layerTargetComponentOrbitRepresentative d θ o).1 ≃*
      K.1.1 := by
  let t :=
    layerTargetComponentTransporter d θ K.1
  let tG : G :=
    (((t : targetInertiaGroup d θ) :
      d.ambientIntermediate) : G)
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  have ht : tG • R = K.1 := by
    have h :=
      layerTargetComponentTransporter_smul_representative
        d θ K.1
    rw [K.2] at h
    exact h
  exact
    (componentConjugationEquiv G tG R).trans
      (MulEquiv.subgroupCongr (congrArg Subtype.val ht))

@[simp]
theorem layerTargetOrbitCoordinateTransportEquiv_apply_coe
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o)
    (x : (layerTargetComponentOrbitRepresentative d θ o).1) :
    ((layerTargetOrbitCoordinateTransportEquiv
      d θ K x : K.1.1) : G) =
      ((((layerTargetComponentTransporter d θ K.1 :
        targetInertiaGroup d θ) : d.ambientIntermediate) : G)) *
        (x : G) *
      ((((layerTargetComponentTransporter d θ K.1 :
        targetInertiaGroup d θ) : d.ambientIntermediate) : G))⁻¹ := by
  simp only [layerTargetOrbitCoordinateTransportEquiv,
    MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    componentConjugationEquiv_apply_coe]

/-- The transported representative-component character value is the
coordinate-character value at the requested component. -/
theorem coordinateLayerCharacter_values_layerTargetOrbitCoordinateTransportEquiv
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o)
    (z : (layerTargetComponentOrbitRepresentative d θ o).1) :
    (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1).1.values
        (layerTargetOrbitCoordinateTransportEquiv d θ K z) =
      (ComponentOrbitLocalData.coordinateLayerCharacter θ
        (layerTargetComponentOrbitRepresentative d θ o)).1.values z := by
  let t :=
    layerTargetComponentTransporter d θ K.1
  let tG : G :=
    (((t : targetInertiaGroup d θ) :
      d.ambientIntermediate) : G)
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  have ht : tG • R = K.1 := by
    have h :=
      layerTargetComponentTransporter_smul_representative
        d θ K.1
    rw [K.2] at h
    exact h
  have htθ : tG • θ = θ :=
    targetInertiaAmbient_smul_layerCharacter_eq
      (d := d) (θ := θ) hcoordinate t
  have htInvθ : tG⁻¹ • θ = θ := by
    calc
      tG⁻¹ • θ = tG⁻¹ • (tG • θ) := by rw [htθ]
      _ = θ := inv_smul_smul tG θ
  apply
    LayerComponentLocalData.layerCoordinatePPrimeFamily_values_of_index_eq
      tG⁻¹ θ htInvθ R K.1
  · rw [inv_inv]
    exact ht
  · rw [layerTargetOrbitCoordinateTransportEquiv_apply_coe]
    simp only [inv_inv]
    change tG * (z : G) * tG⁻¹ =
      tG * (z : G) * tG⁻¹
    rfl

/-- Product of the representative-component groups, nested in exactly the
same orbit/coordinate shape as the canonical tensor space. -/
abbrev LayerOrbitRepresentativeProduct :=
  ∀ o : LayerTargetComponentOrbit d θ,
    ∀ _K : LayerTargetOrbitCoordinate d θ o,
      (layerTargetComponentOrbitRepresentative d θ o).1

/-- The external tensor character of the repeated representative component
on one target-inertia orbit. -/
def canonicalOrbitRepresentativeSourceCharacter
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ) :
    IrreducibleCharacter
      (∀ _K : LayerTargetOrbitCoordinate d θ o,
        (layerTargetComponentOrbitRepresentative d θ o).1) :=
  IrreducibleCharacter.finiteExternalTensor
    (fun _K ↦
      (ComponentOrbitLocalData.coordinateLayerCharacter θ
        (layerTargetComponentOrbitRepresentative d θ o)).1)

/-- Orbitwise representative characters, indexed compatibly with the outer
canonical tensor product. -/
def canonicalOrbitRepresentativeSourceCharacterFamily
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    ∀ o : LayerTargetComponentOrbit d θ,
      IrreducibleCharacter
        (∀ _K : LayerTargetOrbitCoordinate d θ o,
          (layerTargetComponentOrbitRepresentative d θ o).1) :=
  canonicalOrbitRepresentativeSourceCharacter d θ

/-- Transport every representative coordinate to its actual component. -/
def layerOrbitRepresentativeToComponentProduct
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    LayerOrbitRepresentativeProduct (d := d) (θ := θ) →*
      (∀ K : ComponentIndex G, K.1) where
  toFun x K :=
    layerTargetOrbitCoordinateTransportEquiv d θ
      (⟨K, rfl⟩ : LayerTargetOrbitCoordinate d θ
        (layerTargetComponentOrbitOf d θ K))
      (x (layerTargetComponentOrbitOf d θ K) ⟨K, rfl⟩)
  map_one' := by
    funext K
    simp
  map_mul' x y := by
    funext K
    simp

/-- Coordinate transport is injective on the nested representative
product. -/
theorem layerOrbitRepresentativeToComponentProduct_injective
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    Function.Injective
      (layerOrbitRepresentativeToComponentProduct d θ) := by
  intro x y hxy
  funext o K
  rcases K with ⟨K, hK⟩
  subst o
  apply
    (layerTargetOrbitCoordinateTransportEquiv d θ
      (⟨K, rfl⟩ :
        LayerTargetOrbitCoordinate d θ
          (layerTargetComponentOrbitOf d θ K))).injective
  exact congrFun hxy K

/-- Multiply the transported representative coordinates in the layer. -/
def layerOrbitRepresentativeProductHom
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    LayerOrbitRepresentativeProduct (d := d) (θ := θ) →*
      layer G :=
  (layerProductHom G).comp
    (layerOrbitRepresentativeToComponentProduct d θ)

/-- The nested external tensor of representative characters evaluates as
the original layer character after representative-coordinate
multiplication. -/
theorem canonicalOrbitRepresentativeSourceCharacterFamily_values
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (z : LayerOrbitRepresentativeProduct (d := d) (θ := θ)) :
    (IrreducibleCharacter.finiteExternalTensor
      (canonicalOrbitRepresentativeSourceCharacterFamily d θ)).values z =
      θ.1.values (layerOrbitRepresentativeProductHom d θ z) := by
  rw [IrreducibleCharacter.finiteExternalTensor_values]
  simp_rw [canonicalOrbitRepresentativeSourceCharacterFamily,
    canonicalOrbitRepresentativeSourceCharacter,
    IrreducibleCharacter.finiteExternalTensor_values]
  have hθ :=
    GroupTheory.layerPPrimeCharacterEquiv_values_componentProduct
      G p ((GroupTheory.layerPPrimeCharacterEquiv G p).symm θ)
      (layerOrbitRepresentativeToComponentProduct d θ z)
  rw [GroupTheory.layerPPrimeCharacterEquiv_apply_symm_apply] at hθ
  calc
    (∏ o, ∏ K : LayerTargetOrbitCoordinate d θ o,
        (ComponentOrbitLocalData.coordinateLayerCharacter θ
          (layerTargetComponentOrbitRepresentative d θ o)).1.values
            (z o K)) =
      ∏ s :
        Σ o : LayerTargetComponentOrbit d θ,
          LayerTargetOrbitCoordinate d θ o,
        (ComponentOrbitLocalData.coordinateLayerCharacter θ
          (layerTargetComponentOrbitRepresentative d θ s.1)).1.values
            (z s.1 s.2) := by
      rw [Fintype.prod_sigma]
    _ =
      ∏ s :
        Σ o : LayerTargetComponentOrbit d θ,
          LayerTargetOrbitCoordinate d θ o,
        (ComponentOrbitLocalData.coordinateLayerCharacter θ s.2.1).1.values
          (layerOrbitRepresentativeToComponentProduct d θ z s.2.1) := by
      apply Finset.prod_congr rfl
      intro s _
      rcases s with ⟨o, ⟨K, hK⟩⟩
      subst o
      exact
        (coordinateLayerCharacter_values_layerTargetOrbitCoordinateTransportEquiv
          hcoordinate
          (⟨K, rfl⟩ :
            LayerTargetOrbitCoordinate d θ
              (layerTargetComponentOrbitOf d θ K))
          (z (layerTargetComponentOrbitOf d θ K) ⟨K, rfl⟩)).symm
    _ =
      ∏ K : ComponentIndex G,
        (ComponentOrbitLocalData.coordinateLayerCharacter θ K).1.values
          (layerOrbitRepresentativeToComponentProduct d θ z K) := by
      exact
        Equiv.prod_comp
          (layerTargetOrbitCoordinateSigmaEquiv d θ)
          (fun K : ComponentIndex G ↦
            (ComponentOrbitLocalData.coordinateLayerCharacter θ K).1.values
              (layerOrbitRepresentativeToComponentProduct d θ z K))
    _ = θ.1.values (layerOrbitRepresentativeProductHom d θ z) := by
      exact hθ.symm

/-- The representative-coordinate multiplication map is surjective onto
the layer. -/
theorem layerOrbitRepresentativeProductHom_surjective
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    Function.Surjective
      (layerOrbitRepresentativeProductHom d θ) := by
  intro y
  obtain ⟨u, hu⟩ :=
    layerProductHom_surjective G y
  let z :
      LayerOrbitRepresentativeProduct (d := d) (θ := θ) :=
    fun o K ↦
      (layerTargetOrbitCoordinateTransportEquiv d θ K).symm
        (u K.1)
  refine ⟨z, ?_⟩
  change
    layerProductHom G
        (layerOrbitRepresentativeToComponentProduct d θ z) =
      y
  rw [← hu]
  congr 1
  funext K
  change
    layerTargetOrbitCoordinateTransportEquiv d θ
        (⟨K, rfl⟩ :
          LayerTargetOrbitCoordinate d θ
            (layerTargetComponentOrbitOf d θ K))
        ((layerTargetOrbitCoordinateTransportEquiv d θ
          (⟨K, rfl⟩ :
            LayerTargetOrbitCoordinate d θ
              (layerTargetComponentOrbitOf d θ K))).symm
            (u K)) =
      u K
  exact
    (layerTargetOrbitCoordinateTransportEquiv d θ
      (⟨K, rfl⟩ :
        LayerTargetOrbitCoordinate d θ
          (layerTargetComponentOrbitOf d θ K))).apply_symm_apply
        (u K)

/-- The kernel of representative-coordinate multiplication is central. -/
theorem layerOrbitRepresentativeProductHom_ker_le_center
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    (layerOrbitRepresentativeProductHom d θ).ker ≤
      Subgroup.center
        (LayerOrbitRepresentativeProduct (d := d) (θ := θ)) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro y
  apply
    layerOrbitRepresentativeToComponentProduct_injective d θ
  rw [map_mul, map_mul]
  have hzComponent :
      layerOrbitRepresentativeToComponentProduct d θ z ∈
        (layerProductHom G).ker := by
    rw [MonoidHom.mem_ker]
    exact
      (show
        layerOrbitRepresentativeProductHom d θ z = 1
        from MonoidHom.mem_ker.mp hz)
  exact
    Subgroup.mem_center_iff.mp
      (layerProductHom_ker_le_center G hzComponent)
      (layerOrbitRepresentativeToComponentProduct d θ y)

/-- The repeated representative-component external tensor has the same
degree as the original layer character. -/
theorem canonicalOrbitRepresentativeSourceCharacterFamily_degree
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder) :
    (IrreducibleCharacter.finiteExternalTensor
      (canonicalOrbitRepresentativeSourceCharacterFamily d θ)).degree =
      θ.1.degree := by
  apply Nat.cast_injective (R := ℂ)
  have h :=
    canonicalOrbitRepresentativeSourceCharacterFamily_values
      hcoordinate
      (1 : LayerOrbitRepresentativeProduct (d := d) (θ := θ))
  simpa only [IrreducibleCharacter.value_one, map_one] using h

/-- The representative-component character family is compatible with the
exact kernel of multiplication onto the layer. -/
def canonicalOrbitRepresentativeSourceCompatibleFamily
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder) :
    IrreducibleCharacter.KernelCompatibleCharacterFamily
      (fun o : LayerTargetComponentOrbit d θ ↦
        ∀ _K : LayerTargetOrbitCoordinate d θ o,
          (layerTargetComponentOrbitRepresentative d θ o).1)
      (layerOrbitRepresentativeProductHom d θ) := by
  refine
    ⟨canonicalOrbitRepresentativeSourceCharacterFamily d θ, ?_⟩
  rw [IrreducibleCharacter.trivialOn_iff_values_eq_degree
    _ _ (layerOrbitRepresentativeProductHom_ker_le_center d θ)]
  intro z
  calc
    (IrreducibleCharacter.finiteExternalTensor
        (canonicalOrbitRepresentativeSourceCharacterFamily d θ)).values
          (z : LayerOrbitRepresentativeProduct (d := d) (θ := θ)) =
      θ.1.values
        (layerOrbitRepresentativeProductHom d θ
          (z : LayerOrbitRepresentativeProduct (d := d) (θ := θ))) :=
      canonicalOrbitRepresentativeSourceCharacterFamily_values
        (d := d) (θ := θ) hcoordinate z.1
    _ = θ.1.values 1 := by
      rw [MonoidHom.mem_ker.mp z.2]
    _ = (θ.1.degree : ℂ) :=
      θ.1.value_one
    _ =
      ((IrreducibleCharacter.finiteExternalTensor
        (canonicalOrbitRepresentativeSourceCharacterFamily d θ)).degree :
          ℂ) := by
      rw [
        canonicalOrbitRepresentativeSourceCharacterFamily_degree
          hcoordinate]

/-- Transporting the canonical coherent representative coordinate forward
by the selected full transporter recovers the chosen coordinate of the
original normal element. -/
theorem layerTargetOrbitCoordinateTransportEquiv_coherentRepresentativeNormalCoordinate
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o) :
    layerTargetOrbitCoordinateTransportEquiv d θ K
        ((coherentRepresentativeNormalCoordinate
          (hcoordinate := hcoordinate) x K :
            d.intermediate
              (layerTargetComponentOrbitRepresentative d θ o)) :
          (layerTargetComponentOrbitRepresentative d θ o).1) =
      (targetNormalCoordinateFamily x K.1 : K.1.1) := by
  let T :=
    layerTargetTransporterDecomposition
      d hcoordinate θ K.1
  let n :=
    layerIntermediateAmbientNormalizerEquiv
      G Q d.intermediate T.ambientNormalizerPart
  let u : ∀ J : ComponentIndex G, J.1 :=
    fun J ↦ (targetNormalCoordinateFamily x J : J.1)
  let v : ∀ J : ComponentIndex G, J.1 :=
    fun J ↦ (transporterComponentLocalCoordinateFamily T J : J.1)
  let M := layerProductHomToAmbient G v
  let tG : G :=
    ((((layerTargetComponentTransporter d θ K.1 :
      targetInertiaGroup d θ) : d.ambientIntermediate) : G))
  have hM :
      M = ((T.componentLocalPart : d.ambientIntermediate) : G) :=
    transporterComponentLocalCoordinateFamily_product_apply_coe T
  have ht :
      ((T.componentLocalPart : d.ambientIntermediate) : G) *
          ((T.ambientNormalizerPart : d.ambientIntermediate) : G) =
        tG := by
    exact congrArg
      (fun z : d.ambientIntermediate ↦ (z : G))
      T.mul_eq_transporter
  have hn :
      ((T.ambientNormalizerPart : d.ambientIntermediate) : G) =
        (n : G) := by
    rfl
  have hcoordinate :=
    coherentRepresentativeNormalCoordinateOfDecomposition_apply_coe
      x K T
  change
    (((coherentRepresentativeNormalCoordinateOfDecomposition
      x K T :
        d.intermediate
          (layerTargetComponentOrbitRepresentative d θ o)) :
      (layerTargetComponentOrbitRepresentative d θ o).1) : G) =
      (n : G)⁻¹ *
        ((v K.1 : G)⁻¹ * (u K.1 : G) * (v K.1 : G)) *
      (n : G)
    at hcoordinate
  have hlocal :=
    layerProductHomToAmbient_inv_conjugate_component
      v K.1 (u K.1)
  change
    M⁻¹ * (u K.1 : G) * M =
      (v K.1 : G)⁻¹ * (u K.1 : G) * (v K.1 : G)
    at hlocal
  apply Subtype.ext
  rw [layerTargetOrbitCoordinateTransportEquiv_apply_coe]
  change
    tG *
        (((coherentRepresentativeNormalCoordinateOfDecomposition
          x K T :
            d.intermediate
              (layerTargetComponentOrbitRepresentative d θ o)) :
          (layerTargetComponentOrbitRepresentative d θ o).1) : G) *
      tG⁻¹ =
        (u K.1 : G)
  rw [hcoordinate]
  rw [← hM, hn] at ht
  rw [← hlocal, ← ht]
  group

/-- Embed a representative component into the normal copy of its coordinate
ambient inertia triple. -/
def coordinateSourceNormalCopyHom
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (R : ComponentIndex G) :
    R.1 →*
      (ComponentOrbitLocalData.coordinateAmbientTriple
        (D := D) θ R).normalSubgroup where
  toFun y :=
    ⟨SemidirectProduct.inl y, ⟨y, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

/-- The honest representative-component action obtained by restricting the
associated source coordinate lift to its normal copy. -/
def canonicalRepresentativeSourceNormalAction
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ) :
    (layerTargetComponentOrbitRepresentative d θ o).1 →*
      (canonicalOrbitSourceSpace d θ o ≃ₗ[ℂ]
        canonicalOrbitSourceSpace d θ o) :=
  (canonicalOrbitSourceLift d θ o).associated.restriction.comp
    (coordinateSourceNormalCopyHom θ
      (layerTargetComponentOrbitRepresentative d θ o))

@[simp]
theorem canonicalRepresentativeSourceNormalAction_apply
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ)
    (y :
      d.intermediate
        (layerTargetComponentOrbitRepresentative d θ o)) :
    canonicalRepresentativeSourceNormalAction d θ o
        (y :
          (layerTargetComponentOrbitRepresentative d θ o).1) =
      (d.coordinateAmbientLift θ
        (layerTargetComponentOrbitRepresentative d θ o)).projective.operator
          (coordinateSourceNormalElement
            (d := d) (θ := θ)
            (layerTargetComponentOrbitRepresentative d θ o) y) := by
  unfold canonicalRepresentativeSourceNormalAction
  change
        (canonicalOrbitSourceLift d θ o).associated.restriction
        (coordinateSourceNormalCopyHom θ
          (layerTargetComponentOrbitRepresentative d θ o)
          (y :
            (layerTargetComponentOrbitRepresentative d θ o).1)) =
      _
  rw [(canonicalOrbitSourceLift d θ o).associated.restriction_apply]
  rfl

/-- The representative-component normal action realizes the selected
coordinate character. -/
theorem canonicalRepresentativeSourceNormalAction_character
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ) :
    (FDRep.of
      (linearRepresentationOfAction
        (canonicalRepresentativeSourceNormalAction d θ o))).character =
      (ComponentOrbitLocalData.coordinateLayerCharacter θ
        (layerTargetComponentOrbitRepresentative d θ o)).1.values := by
  funext y
  have h :=
    congrFun
      (canonicalOrbitSourceLift d θ o).associated.restriction_character
      (coordinateSourceNormalCopyHom θ
        (layerTargetComponentOrbitRepresentative d θ o) y)
  change
    LinearMap.trace ℂ (canonicalOrbitSourceSpace d θ o)
        ((linearRepresentationOfAction
          (canonicalRepresentativeSourceNormalAction d θ o)) y) =
      (ComponentOrbitLocalData.coordinateLayerCharacter θ
        (layerTargetComponentOrbitRepresentative d θ o)).1.values y
  exact h

/-- Tensor the representative-component normal actions across one
component orbit. -/
def canonicalOrbitSourceNormalAction
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ) :
    (∀ _K : LayerTargetOrbitCoordinate d θ o,
      (layerTargetComponentOrbitRepresentative d θ o).1) →*
        ((⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
          canonicalOrbitSourceSpace d θ o) ≃ₗ[ℂ]
        (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
          canonicalOrbitSourceSpace d θ o)) := by
  letI :
      ∀ _K : LayerTargetOrbitCoordinate d θ o,
        AddCommGroup (canonicalOrbitSourceSpace d θ o) :=
    fun _ ↦ inferInstance
  letI :
      ∀ _K : LayerTargetOrbitCoordinate d θ o,
        Module ℂ (canonicalOrbitSourceSpace d θ o) :=
    fun _ ↦ inferInstance
  exact
    ProjectiveRepresentation.piTensorLinearAction
      (fun _K ↦ canonicalRepresentativeSourceNormalAction d θ o)

/-- The orbitwise tensor action realizes the repeated representative
character on that orbit. -/
theorem canonicalOrbitSourceNormalAction_character
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ) :
    (FDRep.of
      (linearRepresentationOfAction
        (canonicalOrbitSourceNormalAction d θ o))).character =
      (canonicalOrbitRepresentativeSourceCharacter d θ o).values := by
  exact
    ProjectiveRepresentation.piTensorFDRep_character
      (fun _K ↦ canonicalRepresentativeSourceNormalAction d θ o)
      (fun _K ↦
        (ComponentOrbitLocalData.coordinateLayerCharacter θ
          (layerTargetComponentOrbitRepresentative d θ o)).1)
      (fun _K ↦
        canonicalRepresentativeSourceNormalAction_character d θ o)

/-- Tensor the orbitwise normal actions on the full canonical source tensor
space, before descending through layer multiplication. -/
def canonicalSourceNormalProductAction
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    LayerOrbitRepresentativeProduct (d := d) (θ := θ) →*
      ((canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceTensorSpace ≃ₗ[ℂ]
      (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceTensorSpace) :=
  ProjectiveRepresentation.piTensorLinearAction
    (canonicalOrbitSourceNormalAction d θ)

/-- Descend the representative tensor action through component
multiplication to an honest action of the layer. -/
def canonicalCoherentSourceLayerAction
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    layer G →*
      ((canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceTensorSpace ≃ₗ[ℂ]
      (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceTensorSpace) := by
  let F :=
    canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ
  letI :
      ∀ o : F.orbit,
        Module.Finite ℂ (F.sourceOrbitSpace o) :=
    fun o ↦ F.sourceOrbitModuleFinite o
  letI :
      ∀ o : F.orbit,
        Nontrivial (F.sourceOrbitSpace o) :=
    fun o ↦ F.sourceOrbitNontrivial o
  exact
    ProjectiveRepresentation.piTensorQuotientLinearAction
      (layerOrbitRepresentativeProductHom d θ)
      (layerOrbitRepresentativeProductHom_surjective d θ)
      (canonicalOrbitSourceNormalAction d θ)
      (canonicalOrbitRepresentativeSourceCompatibleFamily hcoordinate)
      (canonicalOrbitSourceNormalAction_character d θ)

/-- On a representative product, the descended layer action is the
original nested tensor action. -/
@[simp]
theorem canonicalCoherentSourceLayerAction_product
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (z : LayerOrbitRepresentativeProduct (d := d) (θ := θ)) :
    canonicalCoherentSourceLayerAction d hcoordinate θ
        (layerOrbitRepresentativeProductHom d θ z) =
      canonicalSourceNormalProductAction d hcoordinate θ z :=
  by
    let F :=
      canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ
    letI :
        ∀ o : F.orbit,
          Module.Finite ℂ (F.sourceOrbitSpace o) :=
      fun o ↦ F.sourceOrbitModuleFinite o
    letI :
        ∀ o : F.orbit,
          Nontrivial (F.sourceOrbitSpace o) :=
      fun o ↦ F.sourceOrbitNontrivial o
    exact
      ProjectiveRepresentation.piTensorQuotientLinearAction_product
        (layerOrbitRepresentativeProductHom d θ)
        (layerOrbitRepresentativeProductHom_surjective d θ)
        (canonicalOrbitSourceNormalAction d θ)
        (canonicalOrbitRepresentativeSourceCompatibleFamily hcoordinate)
        (canonicalOrbitSourceNormalAction_character d θ)
        z

/-- The quotient character classified by the representative tensor family
is exactly the original layer character. -/
theorem canonicalOrbitRepresentativeSourceQuotientCharacter_eq
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    IrreducibleCharacter.quotientProductCharacterEquiv
        (fun o : LayerTargetComponentOrbit d θ ↦
          ∀ _K : LayerTargetOrbitCoordinate d θ o,
            (layerTargetComponentOrbitRepresentative d θ o).1)
        (layerOrbitRepresentativeProductHom d θ)
        (layerOrbitRepresentativeProductHom_surjective d θ)
        (canonicalOrbitRepresentativeSourceCompatibleFamily hcoordinate) =
      θ.1 := by
  apply IrreducibleCharacter.ext
  funext y
  obtain ⟨z, rfl⟩ :=
    layerOrbitRepresentativeProductHom_surjective d θ y
  rw [
    IrreducibleCharacter.quotientProductCharacterEquiv_values_apply]
  change
    (∏ o,
      (canonicalOrbitRepresentativeSourceCharacterFamily d θ o).values
        (z o)) =
      θ.1.values (layerOrbitRepresentativeProductHom d θ z)
  simpa only [IrreducibleCharacter.finiteExternalTensor_values] using
    canonicalOrbitRepresentativeSourceCharacterFamily_values
      (d := d) (θ := θ) hcoordinate z

/-- The descended layer action affords exactly the original layer
character. -/
theorem canonicalCoherentSourceLayerAction_character
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    (FDRep.of
      (linearRepresentationOfAction
        (canonicalCoherentSourceLayerAction
          d hcoordinate θ))).character =
      θ.1.values := by
  let F :=
    canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ
  letI :
      ∀ o : F.orbit,
        Module.Finite ℂ (F.sourceOrbitSpace o) :=
    fun o ↦ F.sourceOrbitModuleFinite o
  letI :
      ∀ o : F.orbit,
        Nontrivial (F.sourceOrbitSpace o) :=
    fun o ↦ F.sourceOrbitNontrivial o
  calc
    (FDRep.of
      (linearRepresentationOfAction
        (canonicalCoherentSourceLayerAction
          d hcoordinate θ))).character =
        (IrreducibleCharacter.quotientProductCharacterEquiv
          (fun o : LayerTargetComponentOrbit d θ ↦
            ∀ _K : LayerTargetOrbitCoordinate d θ o,
              (layerTargetComponentOrbitRepresentative d θ o).1)
          (layerOrbitRepresentativeProductHom d θ)
          (layerOrbitRepresentativeProductHom_surjective d θ)
          (canonicalOrbitRepresentativeSourceCompatibleFamily
            hcoordinate)).values := by
      exact
        ProjectiveRepresentation.piTensorQuotientFDRep_character
          (layerOrbitRepresentativeProductHom d θ)
          (layerOrbitRepresentativeProductHom_surjective d θ)
          (canonicalOrbitSourceNormalAction d θ)
          (canonicalOrbitRepresentativeSourceCompatibleFamily
            hcoordinate)
          (canonicalOrbitSourceNormalAction_character d θ)
    _ = θ.1.values := by
      rw [
        canonicalOrbitRepresentativeSourceQuotientCharacter_eq
          d hcoordinate θ]

/-- Restrict the descended layer action to the canonical layer copy inside
the source inertia triple. -/
def canonicalCoherentSourceNormalRestriction
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    (sourceTriple θ).normalSubgroup →*
      ((canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceTensorSpace ≃ₗ[ℂ]
      (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceTensorSpace) :=
  (canonicalCoherentSourceLayerAction d hcoordinate θ).comp
    (CliffordEquivalence.inertiaNormalCopyEquiv
      (layer G) θ.1).toMonoidHom

/-- The intrinsic source normal restriction affords the source-triple
character. -/
theorem canonicalCoherentSourceNormalRestriction_character
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    (FDRep.of
      (linearRepresentationOfAction
        (canonicalCoherentSourceNormalRestriction
          d hcoordinate θ))).character =
      (sourceTriple θ).character.values := by
  funext x
  have h :=
    congrFun
      (canonicalCoherentSourceLayerAction_character
        d hcoordinate θ)
      (CliffordEquivalence.inertiaNormalCopyEquiv
        (layer G) θ.1 x)
  change
    LinearMap.trace ℂ
        (canonicalLayerTensorPermutationCocycleFamily
          d hcoordinate θ).sourceTensorSpace
        ((linearRepresentationOfAction
          (canonicalCoherentSourceNormalRestriction
            d hcoordinate θ)) x) =
      (sourceTriple θ).character.values x
  exact h

/-- The intrinsic source normal restriction is irreducible. -/
theorem canonicalCoherentSourceNormalRestriction_simple
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    Simple
      (FDRep.of
        (linearRepresentationOfAction
          (canonicalCoherentSourceNormalRestriction
            d hcoordinate θ))) := by
  letI : Fintype (sourceTriple θ).normalSubgroup :=
    Fintype.ofFinite _
  rw [FDRep.simple_iff_char_is_norm_one]
  have hsimple :
      Simple (sourceTriple θ).character.realization :=
    inferInstance
  have hnorm :=
    (FDRep.simple_iff_char_is_norm_one
      (sourceTriple θ).character.realization).mp hsimple
  rw [canonicalCoherentSourceNormalRestriction_character,
    ← (sourceTriple θ).character.realization_character]
  exact hnorm

/-- Character equality canonically supplies an equivalence between the
intrinsic source normal restriction and the normal restriction of any
complete associated source lift. -/
def canonicalCoherentSourceRestrictionEquiv
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (R : CompleteAssociatedProjectiveLift (sourceTriple θ)) :
    Representation.Equiv
      (linearRepresentationOfAction
        (canonicalCoherentSourceNormalRestriction
          d hcoordinate θ))
      (linearRepresentationOfAction
        R.associated.restriction) := by
  letI :
      Simple
        (FDRep.of
          (linearRepresentationOfAction
            (canonicalCoherentSourceNormalRestriction
              d hcoordinate θ))) :=
    canonicalCoherentSourceNormalRestriction_simple
      d hcoordinate θ
  let i :=
    Classical.choice
      (FDRep.nonempty_iso_of_character_eq
        (FDRep.of
          (linearRepresentationOfAction
            (canonicalCoherentSourceNormalRestriction
              d hcoordinate θ)))
        R.associated.fdRestriction
        ((canonicalCoherentSourceNormalRestriction_character
          d hcoordinate θ).trans
            R.associated.restriction_character.symm))
  let e := FDRep.isoToLinearEquiv i
  apply Representation.Equiv.mk e
  intro x
  have hconj := FDRep.Iso.conj_ρ i x
  apply LinearMap.ext
  intro v
  have hv :
    ((FDRep.of
      (linearRepresentationOfAction
        R.associated.restriction)).ρ x) (e v) =
      e
        (((FDRep.of
          (linearRepresentationOfAction
            (canonicalCoherentSourceNormalRestriction
              d hcoordinate θ))).ρ x) v)
      := by
    change
      (R.associated.fdRestriction.ρ x) (e v) =
        e
          (((FDRep.of
            (linearRepresentationOfAction
              (canonicalCoherentSourceNormalRestriction
                d hcoordinate θ))).ρ x) v)
    rw [hconj]
    simp [e, LinearEquiv.conj_apply]
  rw [FDRep.of_ρ', FDRep.of_ρ'] at hv
  exact hv.symm

/-- The underlying linear equivalence selected by intrinsic normal
character equality. -/
abbrev canonicalCoherentSourceRestrictionLinearEquiv
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (R : CompleteAssociatedProjectiveLift (sourceTriple θ)) :
    (canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ).sourceTensorSpace ≃ₗ[ℂ] R.space :=
  (canonicalCoherentSourceRestrictionEquiv
    d hcoordinate θ R).toLinearEquiv

/-- The selected equivalence intertwines the intrinsic and associated
source normal restrictions. -/
theorem canonicalCoherentSourceRestrictionLinearEquiv_intertwines
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (R : CompleteAssociatedProjectiveLift (sourceTriple θ))
    (x : (sourceTriple θ).normalSubgroup)
    (v :
      (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceTensorSpace) :
    canonicalCoherentSourceRestrictionLinearEquiv
        d hcoordinate θ R
        (canonicalCoherentSourceNormalRestriction
          d hcoordinate θ x v) =
      R.associated.restriction x
        (canonicalCoherentSourceRestrictionLinearEquiv
          d hcoordinate θ R v) := by
  exact
    LinearMap.congr_fun
      ((canonicalCoherentSourceRestrictionEquiv
        d hcoordinate θ R).isIntertwining' x) v

/-- The nested family of coherent representative coordinates attached to
one target-normal element. -/
def coherentRepresentativeNormalProduct
    (x : (targetTriple d θ).normalSubgroup) :
    LayerOrbitRepresentativeProduct (d := d) (θ := θ) :=
  fun _o K ↦
    (coherentRepresentativeNormalCoordinate
      (hcoordinate := hcoordinate) x K :
        d.intermediate
          (layerTargetComponentOrbitRepresentative d θ _o))

/-- The coherent representative family multiplies to the original layer
element underlying the target-normal element. -/
theorem layerOrbitRepresentativeProductHom_coherentRepresentativeNormalProduct
    (x : (targetTriple d θ).normalSubgroup) :
    layerOrbitRepresentativeProductHom d θ
        (coherentRepresentativeNormalProduct
          (hcoordinate := hcoordinate) x) =
      ((targetNormalLayerLocal x :
        layerLocalSubgroup G d.intermediate) : layer G) := by
  apply Subtype.ext
  change
    layerProductHomToAmbient G
        (layerOrbitRepresentativeToComponentProduct d θ
          (coherentRepresentativeNormalProduct
            (hcoordinate := hcoordinate) x)) =
      (((targetNormalLayerLocal x :
        layerLocalSubgroup G d.intermediate) : layer G) : G)
  calc
    layerProductHomToAmbient G
        (layerOrbitRepresentativeToComponentProduct d θ
          (coherentRepresentativeNormalProduct
            (hcoordinate := hcoordinate) x)) =
      layerProductHomToAmbient G
        (fun K : ComponentIndex G ↦
          (targetNormalCoordinateFamily x K : K.1)) := by
      congr 1
      funext K
      exact
        layerTargetOrbitCoordinateTransportEquiv_coherentRepresentativeNormalCoordinate
          x
          (⟨K, rfl⟩ :
            LayerTargetOrbitCoordinate d θ
              (layerTargetComponentOrbitOf d θ K))
    _ =
      (((targetNormalLayerLocal x :
        layerLocalSubgroup G d.intermediate) : layer G) : G) := by
      have h :=
        congrArg
          (fun y : layerLocalSubgroup G d.intermediate ↦
            (((y : layerLocalSubgroup G d.intermediate) :
              layer G) : G))
          (targetNormalCoordinateFamily_product x)
      exact h

/-- Evaluating the product action on the coherent representative family is
exactly the canonical coherent source normal operator. -/
theorem canonicalSourceNormalProductAction_coherentRepresentativeNormalProduct
    (x : (targetTriple d θ).normalSubgroup) :
    canonicalSourceNormalProductAction d hcoordinate θ
        (coherentRepresentativeNormalProduct
          (hcoordinate := hcoordinate) x) =
      canonicalCoherentSourceNormalOperator
        (hcoordinate := hcoordinate) x := by
  change
    PiTensorProduct.congr
        (fun o ↦
          PiTensorProduct.congr
            (fun K ↦
              canonicalRepresentativeSourceNormalAction d θ o
                ((coherentRepresentativeNormalCoordinate
                  (hcoordinate := hcoordinate) x K :
                    d.intermediate
                      (layerTargetComponentOrbitRepresentative d θ o)) :
                  (layerTargetComponentOrbitRepresentative d θ o).1))) =
      PiTensorProduct.congr
        (fun o ↦
          PiTensorProduct.congr
            (fun K ↦
              (d.coordinateAmbientLift θ
                (layerTargetComponentOrbitRepresentative
                  d θ o)).projective.operator
                    (coordinateSourceNormalElement
                      (d := d) (θ := θ)
                      (layerTargetComponentOrbitRepresentative d θ o)
                      (coherentRepresentativeNormalCoordinate
                        (hcoordinate := hcoordinate) x K))))
  congr 1
  funext o
  congr 1
  funext K
  exact
    canonicalRepresentativeSourceNormalAction_apply d θ o
      (coherentRepresentativeNormalCoordinate
        (hcoordinate := hcoordinate) x K)

/-- The intrinsic source normal restriction evaluates on the source copy
of a target-normal element as the canonical coherent normal operator. -/
theorem canonicalCoherentSourceNormalRestriction_targetNormalSourceCopy
    (x : (targetTriple d θ).normalSubgroup) :
    canonicalCoherentSourceNormalRestriction d hcoordinate θ
        (targetNormalSourceCopy x) =
      canonicalCoherentSourceNormalOperator
        (hcoordinate := hcoordinate) x := by
  change
    canonicalCoherentSourceLayerAction d hcoordinate θ
        (CliffordEquivalence.inertiaNormalCopyEquiv
          (layer G) θ.1 (targetNormalSourceCopy x)) =
      canonicalCoherentSourceNormalOperator
        (hcoordinate := hcoordinate) x
  rw [show
    CliffordEquivalence.inertiaNormalCopyEquiv
        (layer G) θ.1 (targetNormalSourceCopy x) =
      ((targetNormalLayerLocal x :
        layerLocalSubgroup G d.intermediate) : layer G) by
    exact
      (CliffordEquivalence.inertiaNormalCopyEquiv
        (layer G) θ.1).apply_symm_apply
          ((targetNormalLayerLocal x :
            layerLocalSubgroup G d.intermediate) : layer G)]
  rw [
    ← layerOrbitRepresentativeProductHom_coherentRepresentativeNormalProduct
      (hcoordinate := hcoordinate) x,
    canonicalCoherentSourceLayerAction_product]
  exact
    canonicalSourceNormalProductAction_coherentRepresentativeNormalProduct
      (hcoordinate := hcoordinate) x

/-- For the character-theoretically selected source equivalence, coherent
normal-operator intertwining is automatic. -/
theorem canonicalCoherentSourceRestrictionLinearEquiv_coherentNormal_intertwines
    (g :
      CentralRestrictionGroupData
        (sourceTriple θ) (targetTriple d θ)
        (inertiaEmbedding d hcoordinate θ))
    (R : CompleteAssociatedProjectiveLift (sourceTriple θ))
    (x : (targetTriple d θ).normalSubgroup)
    (v :
      (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceTensorSpace) :
    canonicalCoherentSourceRestrictionLinearEquiv
        d hcoordinate θ R
        (canonicalCoherentSourceNormalOperator
          (hcoordinate := hcoordinate) x v) =
      R.projective.operator
        (inertiaEmbedding d hcoordinate θ
          (x : targetInertiaGroup d θ))
        (canonicalCoherentSourceRestrictionLinearEquiv
          d hcoordinate θ R v) := by
  let E :=
    canonicalCoherentSourceRestrictionLinearEquiv
      d hcoordinate θ R
  calc
    E
        (canonicalCoherentSourceNormalOperator
          (hcoordinate := hcoordinate) x v) =
      E
        (canonicalCoherentSourceNormalRestriction
          d hcoordinate θ (targetNormalSourceCopy x) v) := by
      rw [
        canonicalCoherentSourceNormalRestriction_targetNormalSourceCopy]
    _ =
      R.associated.restriction (targetNormalSourceCopy x) (E v) :=
        canonicalCoherentSourceRestrictionLinearEquiv_intertwines
          d hcoordinate θ R (targetNormalSourceCopy x) v
    _ =
      R.projective.operator
          ((targetNormalSourceCopy x :
            (sourceTriple θ).normalSubgroup) :
            sourceInertiaGroup θ)
          (E v) := by
      rw [R.associated.restriction_apply]
    _ =
      R.projective.operator
          (inertiaEmbedding d hcoordinate θ
            (x : targetInertiaGroup d θ))
          (E v) := by
      rw [
        ← g.normalMap_coe x,
        centralRestriction_normalMap_eq_targetNormalSourceCopy g x]

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
