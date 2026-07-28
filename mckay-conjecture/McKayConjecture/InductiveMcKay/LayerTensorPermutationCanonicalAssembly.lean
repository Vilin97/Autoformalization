/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerTensorPermutationSemidirectTransport
import McKayConjecture.InductiveMcKay.LayerTensorPermutationReduction

/-!
# Canonical tensor-permutation assembly boundary for the layer

The target inertia action canonically supplies the finite orbit and
coordinate types used by the layer tensor product.  At one selected
component in each orbit, the quasisimple local datum also canonically
supplies the source and target coordinate representation spaces.

The selected transporter defects preserve both the coordinate intermediates
and their component characters.  These facts construct canonical semidirect
representatives.  The complete component witnesses then construct the paired
coordinate transports, their common projective multiplication scalars, and
their common scalar operator laws on centralizer elements.  Coordinate
finiteness, permutation actions, fixed-coordinate assertions, cocycle
factors, and factor agreement are all theorems; no local transport hypothesis
remains.

The two tensor dimensions are then proved to be exactly the degrees of the
matched source and target characters.  Finally,
`CanonicalLayerTensorPermutationRealizationData` isolates the faithful
global gap: after one common scalar gauge, the source action must extend to
an associated lift on the full source inertia group and the target tensor
action itself must be associated.  It does not compare against an arbitrary
canonical gauge, assume chart coverage, or assume a finished central
witness.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace McKayConjecture
namespace InductiveMcKay
namespace LayerProjectiveRestrictionAssembly

open CharacterTriple
open GroupTheory

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

noncomputable local instance canonicalLayerComponentIndexFintype :
    Fintype (ComponentIndex G) :=
  Fintype.ofFinite _

/-- The source coordinate lift selected at the representative of one target
inertia orbit. -/
abbrev canonicalOrbitSourceLift
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ) :=
  d.coordinateAmbientLift θ
    (layerTargetComponentOrbitRepresentative d θ o)

/-- The target coordinate lift selected at the same orbit representative. -/
abbrev canonicalOrbitTargetLift
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ) :=
  d.coordinateIntermediateLift θ
    (layerTargetComponentOrbitRepresentative d θ o)

/-- Canonical source coordinate space on one component orbit. -/
abbrev canonicalOrbitSourceSpace
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ) :=
  (canonicalOrbitSourceLift d θ o).space

/-- Canonical target coordinate space on one component orbit. -/
abbrev canonicalOrbitTargetSpace
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ) :=
  (canonicalOrbitTargetLift d θ o).space

noncomputable instance canonicalOrbitSourceSpaceAddCommGroup
    (o : LayerTargetComponentOrbit d θ) :
    AddCommGroup (canonicalOrbitSourceSpace d θ o) :=
  (canonicalOrbitSourceLift d θ o).addCommGroup

noncomputable instance canonicalOrbitSourceSpaceModule
    (o : LayerTargetComponentOrbit d θ) :
    Module ℂ (canonicalOrbitSourceSpace d θ o) :=
  (canonicalOrbitSourceLift d θ o).module

noncomputable instance canonicalOrbitSourceSpaceModuleFinite
    (o : LayerTargetComponentOrbit d θ) :
    Module.Finite ℂ (canonicalOrbitSourceSpace d θ o) :=
  (canonicalOrbitSourceLift d θ o).moduleFinite

noncomputable instance canonicalOrbitSourceSpaceNontrivial
    (o : LayerTargetComponentOrbit d θ) :
    Nontrivial (canonicalOrbitSourceSpace d θ o) :=
  (canonicalOrbitSourceLift d θ o).nontrivial

noncomputable instance canonicalOrbitTargetSpaceAddCommGroup
    (o : LayerTargetComponentOrbit d θ) :
    AddCommGroup (canonicalOrbitTargetSpace d θ o) :=
  (canonicalOrbitTargetLift d θ o).addCommGroup

noncomputable instance canonicalOrbitTargetSpaceModule
    (o : LayerTargetComponentOrbit d θ) :
    Module ℂ (canonicalOrbitTargetSpace d θ o) :=
  (canonicalOrbitTargetLift d θ o).module

noncomputable instance canonicalOrbitTargetSpaceModuleFinite
    (o : LayerTargetComponentOrbit d θ) :
    Module.Finite ℂ (canonicalOrbitTargetSpace d θ o) :=
  (canonicalOrbitTargetLift d θ o).moduleFinite

noncomputable instance canonicalOrbitTargetSpaceNontrivial
    (o : LayerTargetComponentOrbit d θ) :
    Nontrivial (canonicalOrbitTargetSpace d θ o) :=
  (canonicalOrbitTargetLift d θ o).nontrivial

/-- The source coordinate space at an orbit representative has the degree
of the corresponding component character. -/
theorem canonicalOrbitSourceSpace_finrank
    (o : LayerTargetComponentOrbit d θ) :
    Module.finrank ℂ (canonicalOrbitSourceSpace d θ o) =
      (ComponentOrbitLocalData.coordinateLayerCharacter θ
        (layerTargetComponentOrbitRepresentative d θ o)).1.degree := by
  exact
    (canonicalOrbitSourceLift d θ o).associated
      |>.finrank_eq_character_degree

/-- The target coordinate space at an orbit representative has the degree
of the corresponding local component character. -/
theorem canonicalOrbitTargetSpace_finrank
    (o : LayerTargetComponentOrbit d θ) :
    Module.finrank ℂ (canonicalOrbitTargetSpace d θ o) =
      (d.correspondence
        (layerTargetComponentOrbitRepresentative d θ o)
        (ComponentOrbitLocalData.coordinateLayerCharacter θ
          (layerTargetComponentOrbitRepresentative d θ o))).1.degree := by
  exact
    (canonicalOrbitTargetLift d θ o).associated
      |>.finrank_eq_character_degree

/-- Component characters in one target-inertia orbit have the same degree
as the character at the selected representative. -/
theorem coordinateLayerCharacter_representative_degree
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o) :
    (ComponentOrbitLocalData.coordinateLayerCharacter θ
        (layerTargetComponentOrbitRepresentative d θ o)).1.degree =
      (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1).1.degree := by
  let t :=
    layerTargetComponentTransporter d θ K.1
  let g : G := (((t : targetInertiaGroup d θ) :
    d.ambientIntermediate) : G)
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  have ht : g • R = K.1 := by
    have ht' :=
      layerTargetComponentTransporter_smul_representative
        d θ K.1
    rw [K.2] at ht'
    change g • R = K.1 at ht'
    exact ht'
  have hinv : g⁻¹ • K.1 = R := by
    rw [← ht, inv_smul_smul]
  have hinv' :
      componentConjugationPermutation G g⁻¹ K.1 = R := by
    exact hinv
  have hgθ : g • θ = θ :=
    targetInertiaAmbient_smul_layerCharacter_eq
      (d := d) (θ := θ) hcoordinate t
  have hfamily :=
    congrFun
      (LayerComponentLocalData.layerPPrimeCoordinateFamily_ambient_smul
        (G := G) (p := p) g θ) K.1
  rw [hgθ,
    IrreducibleCharacter.dependentProductPPrimeEquiv_apply]
    at hfamily
  have hdegree :=
    congrArg
      (fun χ : PPrimeIrreducibleCharacter K.1 p ↦ χ.1.degree)
      hfamily
  rw [IrreducibleCharacter.pPrimeComapEquiv_degree, hinv']
    at hdegree
  exact hdegree.symm

/-- Local correspondence characters in one target-inertia orbit have the
same degree as the character at the selected representative. -/
theorem coordinateLocalCharacter_representative_degree
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o) :
    (d.correspondence
        (layerTargetComponentOrbitRepresentative d θ o)
        (ComponentOrbitLocalData.coordinateLayerCharacter θ
          (layerTargetComponentOrbitRepresentative d θ o))).1.degree =
      (d.correspondence K.1
        (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1)).1.degree := by
  let t :=
    layerTargetComponentTransporter d θ K.1
  let h : d.ambientIntermediate :=
    (t : targetInertiaGroup d θ)
  let M : Subgroup d.ambientIntermediate :=
    d.intermediateComponentLocal
  let A : Subgroup d.ambientIntermediate :=
    layerIntermediateAmbientNormalizer G Q d.intermediate
  have hh : h ∈ M ⊔ A := by
    rw [show M ⊔ A = ⊤ from
      layerIntermediateComponentLocal_sup_ambientNormalizer_eq_top
        G Q d.intermediate]
    exact Subgroup.mem_top h
  obtain ⟨m, hm, n, hn, hmn⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hh
  let mM : M := ⟨m, hm⟩
  let nA : A := ⟨n, hn⟩
  let nN : LayerSylowAmbientNormalizer G Q :=
    layerIntermediateAmbientNormalizerEquiv
      G Q d.intermediate nA
  let mG : G := ((mM : d.ambientIntermediate) : G)
  let nG : G := ((nA : d.ambientIntermediate) : G)
  let hG : G := (h : G)
  have hfactor : mG * nG = hG := by
    exact congrArg
      (fun x : d.ambientIntermediate ↦ (x : G)) hmn
  have hmLayer : mG ∈ layer G := by
    exact
      componentLocalSubgroup_le_layer G d.intermediate mM.2
  have hmfix :
      ∀ J : ComponentIndex G, mG • J = J := by
    intro J
    rw [← MulAction.mem_stabilizer_iff,
      component_stabilizer_eq_normalizer G J]
    exact
      layer_le_normalizer_component J.2 hmLayer
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  have htR : hG • R = K.1 := by
    have htR' :=
      layerTargetComponentTransporter_smul_representative
        d θ K.1
    rw [K.2] at htR'
    change hG • R = K.1 at htR'
    exact htR'
  have hnR : nG • R = K.1 := by
    calc
      nG • R = mG • (nG • R) :=
        (hmfix (nG • R)).symm
      _ = (mG * nG) • R := (mul_smul mG nG R).symm
      _ = hG • R := by rw [hfactor]
      _ = K.1 := htR
  have hmCharacter :
      ∀ χ : PPrimeIrreducibleCharacter (layer G) p,
        mG • χ = χ := by
    intro χ
    exact
      PPrimeIrreducibleCharacter.normalSubgroup_smul_eq
        (layer G) p ⟨mG, hmLayer⟩ χ
  have hnθ : nG • θ = θ := by
    calc
      nG • θ = mG • (nG • θ) :=
        (hmCharacter (nG • θ)).symm
      _ = (mG * nG) • θ := (mul_smul mG nG θ).symm
      _ = hG • θ := by rw [hfactor]
      _ = θ :=
        targetInertiaAmbient_smul_layerCharacter_eq
          (d := d) (θ := θ) hcoordinate t
  have hnθN :
      letI :=
        LayerComponentLocalData.ambientNormalizerLayerPPrimeCharacterMulAction
          (G := G) (p := p) (Q := Q)
      nN • θ = θ := by
    exact hnθ
  have hinv : nN⁻¹ • K.1 = R := by
    change nG⁻¹ • K.1 = R
    rw [← hnR, inv_smul_smul]
  have hinv' :
      componentConjugationPermutation G ((nN⁻¹ : _) : G) K.1 =
        R := by
    exact hinv
  have hfamily :=
    congrFun
      (d.toLayerComponentLocalData.coordinateCorrespondenceFamily_smul
        d.isConjugationEquivariantUnder hcoordinate nN θ)
      K.1
  rw [hnθN,
    IrreducibleCharacter.dependentProductPPrimeEquiv_apply]
    at hfamily
  have hdegree :=
    congrArg
      (fun χ :
        PPrimeIrreducibleCharacter (d.intermediate K.1) p ↦
          χ.1.degree)
      hfamily
  rw [IrreducibleCharacter.pPrimeComapEquiv_degree, hinv']
    at hdegree
  exact hdegree.symm

/-- The canonical semidirect sections and complete component witnesses
construct paired transports; their common multiplication law is a theorem. -/
def canonicalLayerPairedTransport
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ) :
    PairedFiniteTensorPermutationTransport
      (K := ℂ) (A := targetInertiaGroup d θ)
      (ι := LayerTargetOrbitCoordinate d θ o)
      (V := canonicalOrbitSourceSpace d θ o)
      (W := canonicalOrbitTargetSpace d θ o) :=
  (canonicalOrbitSemidirectSection d hcoordinate θ o).pairedTransport

/-- Centralizer elements act through one common coordinate-scalar family.
This follows orbitwise from the local complete central witness. -/
theorem canonicalLayerCentralTransportScalar
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (a : targetInertiaGroup d θ)
    (ha :
      inertiaEmbedding d hcoordinate θ a ∈
        Subgroup.centralizer
          ((sourceTriple θ).normalSubgroup :
            Set (sourceInertiaGroup θ)))
    (o : LayerTargetComponentOrbit d θ) :
    ∃ c : LayerTargetOrbitCoordinate d θ o → ℂˣ,
      (∀ i,
        (canonicalLayerPairedTransport
          d hcoordinate θ o).sourceTransport a i =
          scalarLinearEquiv ℂ
            (canonicalOrbitSourceSpace d θ o) (c i)) ∧
      ∀ i,
        (canonicalLayerPairedTransport
          d hcoordinate θ o).targetTransport a i =
          scalarLinearEquiv ℂ
            (canonicalOrbitTargetSpace d θ o) (c i) := by
  choose c hsource htarget using
    fun i : LayerTargetOrbitCoordinate d θ o ↦
      (canonicalOrbitSemidirectSection d hcoordinate θ o
        |>.exists_common_scalar_of_mem_centralizer a ha i)
  exact ⟨c, hsource, htarget⟩

/-- The canonical finite orbit geometry and paired transports form the
complete cocycle family expected by the tensor-permutation assembler. -/
def canonicalLayerTensorPermutationCocycleFamily
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    LayerTensorPermutationCocycleFamily d hcoordinate θ where
  orbit := LayerTargetComponentOrbit d θ
  orbitFintype := inferInstance
  coordinate := LayerTargetOrbitCoordinate d θ
  coordinateFintype := fun _ ↦ inferInstance
  coordinateAction := fun _ ↦ inferInstance
  sourceCoordinateSpace := canonicalOrbitSourceSpace d θ
  sourceCoordinateAddCommGroup := fun _ ↦ inferInstance
  sourceCoordinateModule := fun _ ↦ inferInstance
  sourceCoordinateModuleFinite := fun _ ↦ inferInstance
  sourceCoordinateNontrivial := fun _ ↦ inferInstance
  targetCoordinateSpace := canonicalOrbitTargetSpace d θ
  targetCoordinateAddCommGroup := fun _ ↦ inferInstance
  targetCoordinateModule := fun _ ↦ inferInstance
  targetCoordinateModuleFinite := fun _ ↦ inferInstance
  targetCoordinateNontrivial := fun _ ↦ inferInstance
  sourceCocycle o :=
    (canonicalLayerPairedTransport
      d hcoordinate θ o).sourceCocycle
  targetCocycle o :=
    (canonicalLayerPairedTransport
      d hcoordinate θ o).targetCocycle
  cocycleAgreement o :=
    (canonicalLayerPairedTransport
      d hcoordinate θ o).cocycleAgreement
  centralCoordinateScalar a ha o := by
    apply
      (canonicalLayerPairedTransport
        d hcoordinate θ o).commonScalar
    obtain ⟨c, hsource, htarget⟩ :=
      canonicalLayerCentralTransportScalar
        d hcoordinate θ a ha o
    exact
      ⟨c,
        (fun i ↦
          targetInertia_smul_orbitCoordinate_eq_of_mem_centralizer
            d θ hcoordinate a ha i),
        hsource, htarget⟩

/-- Finite-dimensionality of the canonical full source tensor. -/
noncomputable instance canonicalLayerSourceTensorModuleFinite
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    Module.Finite ℂ
      (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceTensorSpace :=
  (canonicalLayerTensorPermutationCocycleFamily
    d hcoordinate θ).sourceTensorModuleFinite

/-- Finite-dimensionality of the canonical full target tensor. -/
noncomputable instance canonicalLayerTargetTensorModuleFinite
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    Module.Finite ℂ
      (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).targetTensorSpace :=
  (canonicalLayerTensorPermutationCocycleFamily
    d hcoordinate θ).targetTensorModuleFinite

/-- Nontriviality of the canonical full source tensor. -/
noncomputable instance canonicalLayerSourceTensorNontrivial
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    Nontrivial
      (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceTensorSpace :=
  (canonicalLayerTensorPermutationCocycleFamily
    d hcoordinate θ).sourceTensorNontrivial

/-- Nontriviality of the canonical full target tensor. -/
noncomputable instance canonicalLayerTargetTensorNontrivial
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    Nontrivial
      (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).targetTensorSpace :=
  (canonicalLayerTensorPermutationCocycleFamily
    d hcoordinate θ).targetTensorNontrivial

/-- The canonical source tensor space has the degree of the original layer
character. -/
theorem canonicalLayerSourceTensor_finrank
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    Module.finrank ℂ
        (canonicalLayerTensorPermutationCocycleFamily
          d hcoordinate θ).sourceTensorSpace =
      θ.1.degree := by
  let F :=
    canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ
  letI : ∀ o, Module.Finite ℂ (F.sourceOrbitSpace o) :=
    fun o ↦ F.sourceOrbitModuleFinite o
  calc
    Module.finrank ℂ F.sourceTensorSpace =
        ∏ o, Module.finrank ℂ (F.sourceOrbitSpace o) :=
      ProjectiveRepresentation.piTensor_finrank
    _ =
        ∏ o, ∏ _K : LayerTargetOrbitCoordinate d θ o,
          Module.finrank ℂ (canonicalOrbitSourceSpace d θ o) := by
      apply Finset.prod_congr rfl
      intro o _
      exact ProjectiveRepresentation.piTensor_finrank
    _ =
        ∏ o, ∏ K : LayerTargetOrbitCoordinate d θ o,
          (ComponentOrbitLocalData.coordinateLayerCharacter
            θ K.1).1.degree := by
      apply Finset.prod_congr rfl
      intro o _
      apply Finset.prod_congr rfl
      intro K _
      rw [canonicalOrbitSourceSpace_finrank]
      exact
        coordinateLayerCharacter_representative_degree
          hcoordinate K
    _ =
        ∏ x :
          Σ o : LayerTargetComponentOrbit d θ,
            LayerTargetOrbitCoordinate d θ o,
          (ComponentOrbitLocalData.coordinateLayerCharacter
            θ x.2.1).1.degree := by
      rw [Fintype.prod_sigma]
    _ =
        ∏ K : ComponentIndex G,
          (ComponentOrbitLocalData.coordinateLayerCharacter
            θ K).1.degree := by
      exact
        Equiv.prod_comp
          (layerTargetOrbitCoordinateSigmaEquiv d θ)
          (fun K : ComponentIndex G ↦
            (ComponentOrbitLocalData.coordinateLayerCharacter
              θ K).1.degree)
    _ = θ.1.degree := by
      have hdegree :=
        GroupTheory.layerPPrimeCharacterEquiv_degree
          G p ((GroupTheory.layerPPrimeCharacterEquiv G p).symm θ)
      rw [Equiv.apply_symm_apply] at hdegree
      exact hdegree.symm

/-- The canonical target tensor space has the degree of the matched
component-local character. -/
theorem canonicalLayerTargetTensor_finrank
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    Module.finrank ℂ
        (canonicalLayerTensorPermutationCocycleFamily
          d hcoordinate θ).targetTensorSpace =
      (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1.degree := by
  let F :=
    canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ
  letI : ∀ o, Module.Finite ℂ (F.targetOrbitSpace o) :=
    fun o ↦ F.targetOrbitModuleFinite o
  calc
    Module.finrank ℂ F.targetTensorSpace =
        ∏ o, Module.finrank ℂ (F.targetOrbitSpace o) :=
      ProjectiveRepresentation.piTensor_finrank
    _ =
        ∏ o, ∏ _K : LayerTargetOrbitCoordinate d θ o,
          Module.finrank ℂ (canonicalOrbitTargetSpace d θ o) := by
      apply Finset.prod_congr rfl
      intro o _
      exact ProjectiveRepresentation.piTensor_finrank
    _ =
        ∏ o, ∏ K : LayerTargetOrbitCoordinate d θ o,
          (d.correspondence K.1
            (ComponentOrbitLocalData.coordinateLayerCharacter
              θ K.1)).1.degree := by
      apply Finset.prod_congr rfl
      intro o _
      apply Finset.prod_congr rfl
      intro K _
      rw [canonicalOrbitTargetSpace_finrank]
      exact
        coordinateLocalCharacter_representative_degree
          hcoordinate K
    _ =
        ∏ x :
          Σ o : LayerTargetComponentOrbit d θ,
            LayerTargetOrbitCoordinate d θ o,
          (d.correspondence x.2.1
            (ComponentOrbitLocalData.coordinateLayerCharacter
              θ x.2.1)).1.degree := by
      rw [Fintype.prod_sigma]
    _ =
        ∏ K : ComponentIndex G,
          (d.correspondence K
            (ComponentOrbitLocalData.coordinateLayerCharacter
              θ K)).1.degree := by
      exact
        Equiv.prod_comp
          (layerTargetOrbitCoordinateSigmaEquiv d θ)
          (fun K : ComponentIndex G ↦
            (d.correspondence K
              (ComponentOrbitLocalData.coordinateLayerCharacter
                θ K)).1.degree)
    _ =
        (d.intermediateComponentLocalPPrimeCharacterEquiv
          θ).1.degree :=
      (d.intermediateComponentLocalPPrimeCharacterEquiv_degree
        θ).symm

/-- The source tensor is abstractly linearly equivalent to the space of
every associated source lift.  Thus only a compatible choice, not bare
dimension, remains in the source realization datum. -/
theorem canonicalLayerSourceTensor_nonempty_linearEquiv
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (R : CompleteAssociatedProjectiveLift (sourceTriple θ)) :
    Nonempty
      ((canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceTensorSpace ≃ₗ[ℂ] R.space) :=
  FiniteDimensional.nonempty_linearEquiv_of_finrank_eq <| by
    calc
      Module.finrank ℂ
          (canonicalLayerTensorPermutationCocycleFamily
            d hcoordinate θ).sourceTensorSpace =
        θ.1.degree :=
          canonicalLayerSourceTensor_finrank d hcoordinate θ
      _ = Module.finrank ℂ R.space :=
        R.associated.finrank_eq_character_degree.symm

/-- The target tensor is abstractly linearly equivalent to the space of
every associated target lift. -/
theorem canonicalLayerTargetTensor_nonempty_linearEquiv
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (R : CompleteAssociatedProjectiveLift (targetTriple d θ)) :
    Nonempty
      ((canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).targetTensorSpace ≃ₗ[ℂ] R.space) :=
  FiniteDimensional.nonempty_linearEquiv_of_finrank_eq <| by
    calc
      Module.finrank ℂ
          (canonicalLayerTensorPermutationCocycleFamily
            d hcoordinate θ).targetTensorSpace =
        (d.intermediateComponentLocalPPrimeCharacterEquiv
          θ).1.degree :=
          canonicalLayerTargetTensor_finrank d hcoordinate θ
      _ = Module.finrank ℂ R.space :=
        R.associated.finrank_eq_character_degree.symm

/-- An abstract linear equivalence from the source tensor space to the
canonical associated-lift space.  This only records the proved dimension
equality; no operator compatibility is claimed. -/
def canonicalLayerSourceLinearEquiv
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    (canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ).sourceTensorSpace ≃ₗ[ℂ]
      (canonicalSourceLift θ).space :=
  LinearEquiv.ofFinrankEq _ _ <| by
    calc
      Module.finrank ℂ
          (canonicalLayerTensorPermutationCocycleFamily
            d hcoordinate θ).sourceTensorSpace =
        θ.1.degree :=
          canonicalLayerSourceTensor_finrank d hcoordinate θ
      _ = Module.finrank ℂ (canonicalSourceLift θ).space := by
        exact
          (canonicalSourceLift θ).associated
            |>.finrank_eq_character_degree
            |>.symm

/-- An abstract linear equivalence from the target tensor space to the
canonical associated-lift space.  This only records the proved dimension
equality; no operator compatibility is claimed. -/
def canonicalLayerTargetLinearEquiv
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    (canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ).targetTensorSpace ≃ₗ[ℂ]
      (canonicalTargetLift d θ).space :=
  LinearEquiv.ofFinrankEq _ _ <| by
    calc
      Module.finrank ℂ
          (canonicalLayerTensorPermutationCocycleFamily
            d hcoordinate θ).targetTensorSpace =
        (d.intermediateComponentLocalPPrimeCharacterEquiv
          θ).1.degree :=
          canonicalLayerTargetTensor_finrank d hcoordinate θ
      _ = Module.finrank ℂ (canonicalTargetLift d θ).space := by
        exact
          (canonicalTargetLift d θ).associated
            |>.finrank_eq_character_degree
            |>.symm

/-- The remaining faithful global representation problem after canonical
finite coordinates, equal-factor cocycles, and both dimension equalities
have been proved.

On the source, one must extend the tensor action from the target inertia
group to an associated lift on the full source inertia group.  On the target,
the tensor action itself only has to be proved associated; no comparison
with an arbitrarily gauged canonical lift is requested. -/
structure CanonicalLayerTensorPermutationRealizationData
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) where
  /-- A common scalar gauge used to normalize the two tensor lifts without
  disturbing their exact comparison. -/
  gauge : targetInertiaGroup d θ → ℂˣ
  /-- An associated projective lift on the full source inertia group. -/
  sourceLift :
    CompleteAssociatedProjectiveLift (sourceTriple θ)
  /-- A compatible realization of its pullback by the source tensor. -/
  sourceRealization :
    (canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ).sourceTensorSpace ≃ₗ[ℂ]
      sourceLift.space
  /-- Source tensor-permutation operators intertwine the pulled-back source
  associated lift. -/
  sourceOperator_intertwining :
    ∀ (a : targetInertiaGroup d θ)
      (v :
        (canonicalLayerTensorPermutationCocycleFamily
          d hcoordinate θ).sourceTensorSpace),
      sourceRealization
          (((canonicalLayerTensorPermutationCocycleFamily
            d hcoordinate θ).sourceProjective.rescale gauge).operator a v) =
        sourceLift.projective.operator
          (inertiaEmbedding d hcoordinate θ a)
          (sourceRealization v)
  /-- The constructed target tensor projective representation is associated
  directly with the matched target triple. -/
  targetAssociated :
    AssociatedProjectiveRepresentation
      (targetTriple d θ)
      (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).targetTensorSpace
      ((canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).targetProjective.rescale gauge)

namespace CanonicalLayerTensorPermutationRealizationData

/-- Regard the intrinsically associated target tensor as a complete
associated projective lift. -/
def targetLift
    (R : CanonicalLayerTensorPermutationRealizationData
      d hcoordinate θ) :
    CompleteAssociatedProjectiveLift (targetTriple d θ) where
  space :=
    (canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ).targetTensorSpace
  projective :=
    (canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ).targetProjective.rescale R.gauge
  associated := R.targetAssociated

/-- Canonical-coordinate realization data is a sound
tensor-permutation central-witness assembly. -/
def toCentralWitnessAssembly
    (R : CanonicalLayerTensorPermutationRealizationData
      d hcoordinate θ) :
    LayerTensorPermutationCentralWitnessAssembly
      d hcoordinate θ where
  family :=
    canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ
  gauge := R.gauge
  sourceLift := R.sourceLift
  targetLift := R.targetLift
  sourceRealization := R.sourceRealization
  targetRealization := LinearEquiv.refl ℂ _
  sourceOperator_intertwining :=
    R.sourceOperator_intertwining
  targetOperator_intertwining := by
    intro _ _
    rfl

end CanonicalLayerTensorPermutationRealizationData

end LayerProjectiveRestrictionAssembly

open LayerProjectiveRestrictionAssembly
open GroupTheory

/-- The canonical realization obligation in exactly the minimal-counterexample
context where the layer reduction consumes it. -/
def CanonicalMinimalLayerTensorPermutationRealizationHypothesis
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G),
    MinimalCounterexampleStructure P →
      let d :=
        canonicalComponentOrbitLocalData covers P
      let hcoordinate :=
        ComponentOrbitLocalData.ofQuasisimpleHypothesis_isCoordinateCorrespondenceEquivariant
          (D := canonicalLayerSylowCoordinateData P)
          covers
      ∀ θ : PPrimeIrreducibleCharacter (layer G) p,
        Nonempty
          (CanonicalLayerTensorPermutationRealizationData
            d hcoordinate θ)

/-- The canonical-coordinate realization hypothesis supplies the
tensor-permutation assembly hypothesis used by the layer reduction. -/
theorem canonicalMinimalLayerTensorPermutationAssemblyHypothesis_of_realization
    {p : ℕ} [Fact p.Prime]
    (realization :
      CanonicalMinimalLayerTensorPermutationRealizationHypothesis p) :
    CanonicalMinimalLayerTensorPermutationAssemblyHypothesis p := by
  intro covers G _ _ P hminimal
  dsimp only
  intro θ
  exact
    Nonempty.map
      CanonicalLayerTensorPermutationRealizationData.toCentralWitnessAssembly
      (realization covers G P hminimal θ)

end InductiveMcKay
end McKayConjecture
