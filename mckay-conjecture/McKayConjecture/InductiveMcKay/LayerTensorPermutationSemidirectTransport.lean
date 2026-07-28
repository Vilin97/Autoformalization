/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteTensorPermutationConstruction
import McKayConjecture.GroupTheory.LayerLocalSubgroupIdentification
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCoordinates

/-!
# Semidirect coordinate transports for the layer tensor construction

An element of the target inertia group which fixes a component induces an
automorphism of that component.  To use the projective representations in a
complete component witness, one must lift this automorphism to the target
coordinate semidirect product.  Such a lift is not expected to be
multiplicative: two choices can differ by an element centralizing the normal
copy of the component.

This file isolates exactly that local lifting problem.  Once semidirect
representatives inducing the selected transporter-defect automorphisms are
given, the complete component witness proves the common source/target
projective multiplication law.  Thus the paired tensor-permutation transport
is constructed, rather than retained as an additional hypothesis.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple

universe u v

variable {X : Type u} {Γ : Type v} [Group X] [Group Γ]

/-- The action on the normal factor induced by an element of a semidirect
product. -/
def semidirectNormalAction
    (φ : Γ →* MulAut X) :
    (X ⋊[φ] Γ) →* MulAut X :=
  SemidirectProduct.lift (MulAut.conj : X →* MulAut X) φ (by
    intro g
    ext x
    simp)

@[simp]
theorem semidirectNormalAction_apply
    (φ : Γ →* MulAut X)
    (a : X ⋊[φ] Γ)
    (x : X) :
    semidirectNormalAction φ a x =
      a.left * φ a.right x * a.left⁻¹ :=
  rfl

/-- If the induced action on the normal factor is trivial, the semidirect
element centralizes the canonical normal copy. -/
theorem mem_centralizer_semidirectNormalSubgroup_of_action_eq_one
    (φ : Γ →* MulAut X)
    (a : X ⋊[φ] Γ)
    (ha : semidirectNormalAction φ a = 1) :
    a ∈ Subgroup.centralizer
      (semidirectNormalSubgroup φ : Set (X ⋊[φ] Γ)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxright : x.right = 1 := by
    have hxker :
        SemidirectProduct.rightHom x = 1 := by
      rw [← MonoidHom.mem_ker,
        ← SemidirectProduct.range_inl_eq_ker_rightHom]
      exact hx
    simpa only [SemidirectProduct.rightHom_eq_right] using hxker
  have haction :
      a.left * φ a.right x.left * a.left⁻¹ = x.left := by
    have hpoint := DFunLike.congr_fun ha x.left
    simpa only [semidirectNormalAction_apply,
      MulAut.one_apply] using hpoint
  have hconj : a * x * a⁻¹ = x := by
    apply SemidirectProduct.ext
    · calc
        (a * x * a⁻¹).left =
            a.left * φ a.right x.left * a.left⁻¹ := by
          exact
            conjugate_semidirectNormal_left φ a
              (⟨x, hx⟩ : semidirectNormalSubgroup φ)
        _ = x.left := haction
    · simp only [SemidirectProduct.mul_right,
        SemidirectProduct.inv_right, hxright]
      group
  symm
  calc
    a * x = (a * x * a⁻¹) * a := by simp [mul_assoc]
    _ = x * a := by rw [hconj]

/-- Conjugating an element which centralizes a normal subgroup still acts
trivially on a conjugately reindexed element of that subgroup. -/
theorem conjugate_centralizer_conjugate_eq
    {A : Type*} [Group A]
    (N : Subgroup A) [N.Normal]
    (g t x : A)
    (hg : g ∈ Subgroup.centralizer (N : Set A))
    (hx : x ∈ N) :
    (t⁻¹ * g * t) * x * (t⁻¹ * g * t)⁻¹ = x := by
  let y : A := t * x * t⁻¹
  have hy : y ∈ N :=
    (inferInstance : N.Normal).conj_mem x hx t
  have hcomm : y * g = g * y :=
    Subgroup.mem_centralizer_iff.mp hg y hy
  have hconj : g * y * g⁻¹ = y := by
    rw [← hcomm]
    simp
  calc
    (t⁻¹ * g * t) * x * (t⁻¹ * g * t)⁻¹ =
        t⁻¹ * (g * y * g⁻¹) * t := by
      simp only [y]
      group
    _ = t⁻¹ * y * t := by rw [hconj]
    _ = x := by
      simp only [y]
      group

/-- Inner automorphisms act trivially on prime-to-`p` irreducible
characters. -/
theorem inner_smul_pPrimeIrreducibleCharacter_eq
    {A : Type*} [Group A]
    (p : ℕ) (g : A)
    (χ : PPrimeIrreducibleCharacter A p) :
    MulAut.conj g • χ = χ := by
  apply Subtype.ext
  ext x
  change χ.1.values (g⁻¹ * x * g) = χ.1.values x
  simpa using
    ClassFunction.conj_apply χ.1.toClassFunction x g⁻¹

namespace ProjectiveRepresentation

variable {K : Type*} [Field K]
variable {A : Type*} [Group A]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Rewrite a projective two-step operator through a possibly different
factorization of the same group element, when the extra first factor acts by
a scalar. -/
theorem operator_mul_eq_scalar_mul_of_mul_eq
    (P : ProjectiveRepresentation K A V)
    (x y z t : A)
    (hxy : x * y = z * t)
    (c : Kˣ)
    (hz :
      P.operator z = scalarLinearEquiv K V c) :
    P.operator x * P.operator y =
      scalarLinearEquiv K V
          (P.factor x y / P.factor z t * c) *
        P.operator t := by
  calc
    P.operator x * P.operator y =
        scalarLinearEquiv K V (P.factor x y) *
          P.operator (x * y) :=
      P.map_mul x y
    _ =
        scalarLinearEquiv K V (P.factor x y) *
          P.operator (z * t) := by rw [hxy]
    _ =
        scalarLinearEquiv K V
            (P.factor x y / P.factor z t) *
          (scalarLinearEquiv K V (P.factor z t) *
            P.operator (z * t)) := by
      rw [← mul_assoc, ← scalarLinearEquiv_mul]
      congr 2
      simp
    _ =
        scalarLinearEquiv K V
            (P.factor x y / P.factor z t) *
          (P.operator z * P.operator t) := by
      rw [P.map_mul z t]
    _ =
        scalarLinearEquiv K V
            (P.factor x y / P.factor z t) *
          (scalarLinearEquiv K V c * P.operator t) := by
      rw [hz]
    _ =
        scalarLinearEquiv K V
            (P.factor x y / P.factor z t * c) *
          P.operator t := by
      rw [scalarLinearEquiv_mul, mul_assoc]

/-- Two projective representations with equal factors along an embedding
have the same two-step scalar whenever the discrepancy factor acts by one
common scalar. -/
theorem exists_common_operator_mul
    {B W : Type*} [Group B]
    [AddCommGroup W] [Module K W]
    (P : ProjectiveRepresentation K A V)
    (Q : ProjectiveRepresentation K B W)
    (e : B →* A)
    (hfactor :
      ∀ r s : B,
        P.factor (e r) (e s) = Q.factor r s)
    (x y z t : B)
    (hxy : x * y = z * t)
    (c : Kˣ)
    (hP :
      P.operator (e z) = scalarLinearEquiv K V c)
    (hQ :
      Q.operator z = scalarLinearEquiv K W c) :
    ∃ common : Kˣ,
      P.operator (e x) * P.operator (e y) =
          scalarLinearEquiv K V common * P.operator (e t) ∧
        Q.operator x * Q.operator y =
          scalarLinearEquiv K W common * Q.operator t := by
  let common := Q.factor x y / Q.factor z t * c
  refine ⟨common, ?_, ?_⟩
  · have h :=
      P.operator_mul_eq_scalar_mul_of_mul_eq
        (e x) (e y) (e z) (e t)
        (by
          calc
            e x * e y = e (x * y) := (e.map_mul x y).symm
            _ = e (z * t) := congrArg e hxy
            _ = e z * e t := e.map_mul z t) c hP
    rw [hfactor x y, hfactor z t] at h
    exact h
  · exact
      Q.operator_mul_eq_scalar_mul_of_mul_eq
        x y z t hxy c hQ

end ProjectiveRepresentation
end CharacterTriple

namespace InductiveMcKay

open CharacterTriple

namespace EquivariantLocalCorrespondence

variable {X : Type*} [Group X] [Finite X]
variable {p : ℕ} [Fact p.Prime]
variable {P : Sylow p X}

/-- An automorphism preserving the local intermediate and the source
character has a representative in the target coordinate semidirect product
which induces that automorphism after the canonical embedding.

The proof conjugates the image of the selected Sylow subgroup back to the
selected Sylow subgroup by an element of the intermediate. -/
theorem exists_semidirectRepresentative_inducing
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter X p)
    (α : MulAut X)
    (hintermediate :
      d.intermediate.map α.toMonoidHom = d.intermediate)
    (hcharacter : α • χ = χ) :
    ∃ z :
        d.intermediate ⋊[
          stabilizerIntermediateAction d χ]
          PPrimeCharacterStabilizer P χ,
      semidirectNormalAction
          (PPrimeCharacterStabilizer.ambientAction
            (P := P) (χ := χ))
          (d.semidirectEmbedding χ z) =
        α := by
  have hP :
      (P : Subgroup X) ≤ d.intermediate :=
    Subgroup.le_normalizer.trans d.normalizer_le
  have hαP :
      (α • P : Sylow p X) ≤ d.intermediate := by
    change
      (P : Subgroup X).map α.toMonoidHom ≤
        d.intermediate
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' :
        α y ∈ d.intermediate.map α.toMonoidHom :=
      ⟨y, hP hy, rfl⟩
    exact
      (congrArg (fun M : Subgroup X ↦ α y ∈ M)
        hintermediate).mp hy'
  let PM : Sylow p d.intermediate :=
    P.subtype hP
  let QM : Sylow p d.intermediate :=
    (α • P).subtype hαP
  obtain ⟨m, hm⟩ :=
    MulAction.exists_smul_eq d.intermediate QM PM
  have hmAmbient :
      (m : X) • (α • P) = P := by
    apply Sylow.subtype_injective
    simpa only [PM, QM, Sylow.smul_subtype,
      Subgroup.smul_def] using hm
  let βAuto : MulAut X :=
    MulAut.conj (m : X) * α
  have hβP : βAuto • P = P := by
    change
      (MulAut.conj (m : X) * α) • P = P
    rw [mul_smul]
    exact hmAmbient
  let β : SylowAutStabilizer P :=
    ⟨βAuto, hβP⟩
  have hβχ : β.1 • χ = χ := by
    change
      (MulAut.conj (m : X) * α) • χ = χ
    rw [mul_smul, hcharacter,
      inner_smul_pPrimeIrreducibleCharacter_eq]
  let γ : PPrimeCharacterStabilizer P χ :=
    ⟨β, hβχ⟩
  let z :
      d.intermediate ⋊[
        stabilizerIntermediateAction d χ]
        PPrimeCharacterStabilizer P χ :=
    ⟨m⁻¹, γ⟩
  refine ⟨z, ?_⟩
  apply MulEquiv.ext
  intro x
  change
    (m : X)⁻¹ *
        (MulAut.conj (m : X) * α) x *
        ((m : X)⁻¹)⁻¹ =
      α x
  change
    (m : X)⁻¹ *
        ((m : X) * α x * (m : X)⁻¹) *
        ((m : X)⁻¹)⁻¹ =
      α x
  group

end EquivariantLocalCorrespondence

namespace LayerProjectiveRestrictionAssembly

open CharacterTriple
open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}
variable {D : LayerSylowCoordinateData G p Q}
variable
  {d : ComponentOrbitLocalData D}
  {θ : PPrimeIrreducibleCharacter (layer G) p}

/-- The automorphism of the representative component induced by the shifted
selected-transporter defect. -/
def layerTargetOrbitShiftedDefectAutomorphism
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    MulAut
      (layerTargetComponentOrbitRepresentative d θ o).1 := by
  let δ :=
    layerTargetOrbitShiftedTransporterDefect d θ a K
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  let g : G := (((δ : targetInertiaGroup d θ) :
    d.ambientIntermediate) : G)
  change MulAut R.1
  exact (componentNormalizerAction G R) ⟨g, by
    rw [← component_stabilizer_eq_normalizer G R,
      MulAction.mem_stabilizer_iff]
    exact
      layerTargetOrbitShiftedTransporterDefect_smul_representative
        d θ a K⟩

@[simp]
theorem layerTargetOrbitShiftedDefectAutomorphism_apply_coe
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o)
    (x : (layerTargetComponentOrbitRepresentative d θ o).1) :
    ((layerTargetOrbitShiftedDefectAutomorphism
        (d := d) (θ := θ) a K x :
        (layerTargetComponentOrbitRepresentative d θ o).1) : G) =
      (((layerTargetOrbitShiftedTransporterDefect d θ a K :
          targetInertiaGroup d θ) : d.ambientIntermediate) : G) *
        (x : G) *
      (((layerTargetOrbitShiftedTransporterDefect d θ a K :
          targetInertiaGroup d θ) : d.ambientIntermediate) : G)⁻¹ :=
  rfl

/-- The induced component automorphisms inherit the exact multiplication
law of shifted transporter defects. -/
theorem layerTargetOrbitShiftedDefectAutomorphism_mul
    {o : LayerTargetComponentOrbit d θ}
    (a b : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) a K *
        layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) b (a⁻¹ • K) =
      layerTargetOrbitShiftedDefectAutomorphism
        (d := d) (θ := θ) (a * b) K := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change
    ((layerTargetOrbitShiftedDefectAutomorphism
        (d := d) (θ := θ) a K
      (layerTargetOrbitShiftedDefectAutomorphism
        (d := d) (θ := θ) b (a⁻¹ • K) x) :
      (layerTargetComponentOrbitRepresentative d θ o).1) : G) =
        ((layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) (a * b) K x :
          (layerTargetComponentOrbitRepresentative d θ o).1) : G)
  simp only [layerTargetOrbitShiftedDefectAutomorphism_apply_coe]
  have hδ :=
    congrArg
      (fun z : targetInertiaGroup d θ ↦
        (((z : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G))
      (layerTargetOrbitShiftedTransporterDefect_mul d θ a b K)
  change
    (((layerTargetOrbitShiftedTransporterDefect d θ a K :
        targetInertiaGroup d θ) : d.ambientIntermediate) : G) *
      (((layerTargetOrbitShiftedTransporterDefect d θ b (a⁻¹ • K) :
        targetInertiaGroup d θ) : d.ambientIntermediate) : G) =
      (((layerTargetOrbitShiftedTransporterDefect d θ (a * b) K :
        targetInertiaGroup d θ) : d.ambientIntermediate) : G)
    at hδ
  rw [← hδ]
  group

/-- The ambient element underlying a matched target-inertia element fixes
the original layer character. -/
theorem targetInertiaAmbient_smul_layerCharacter_eq
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (a : targetInertiaGroup d θ) :
    (((a : d.ambientIntermediate) : G)) • θ = θ := by
  apply Subtype.ext
  rw [← inertiaEmbedding_apply_coe
    (d := d) (hcoordinate := hcoordinate) (θ := θ)]
  exact
    (IrreducibleCharacter.mem_inertia_iff
      (layer G) θ.1 (inertiaEmbedding d hcoordinate θ a)).mp
      (inertiaEmbedding d hcoordinate θ a).2

/-- Every shifted transporter defect fixes the component character at its
selected orbit representative. -/
theorem layerTargetOrbitShiftedDefectAutomorphism_smul_character
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) a K •
        ComponentOrbitLocalData.coordinateLayerCharacter θ
          (layerTargetComponentOrbitRepresentative d θ o) =
      ComponentOrbitLocalData.coordinateLayerCharacter θ
        (layerTargetComponentOrbitRepresentative d θ o) := by
  let δ :=
    layerTargetOrbitShiftedTransporterDefect d θ a K
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  let g : G :=
    (((δ : targetInertiaGroup d θ) : d.ambientIntermediate) : G)
  let n : Subgroup.normalizer (R.1 : Set G) :=
    ⟨g, by
      rw [← component_stabilizer_eq_normalizer G R,
        MulAction.mem_stabilizer_iff]
      exact
        layerTargetOrbitShiftedTransporterDefect_smul_representative
          d θ a K⟩
  have hgθ : g • θ = θ :=
    targetInertiaAmbient_smul_layerCharacter_eq
      (d := d) (θ := θ) hcoordinate δ
  exact
    LayerComponentLocalData.layerCoordinatePPrimeCharacter_fixed
      θ R n hgθ

/-- Every shifted transporter defect preserves the coherent intermediate
subgroup at its selected orbit representative. -/
theorem layerTargetOrbitShiftedDefectAutomorphism_intermediate_invariant
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    (d.data
        (layerTargetComponentOrbitRepresentative d θ o)).toEquivariant.intermediate.map
        (layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) a K).toMonoidHom =
      (d.data
        (layerTargetComponentOrbitRepresentative d θ o)).toEquivariant.intermediate := by
  let δ :=
    layerTargetOrbitShiftedTransporterDefect d θ a K
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  let g : G :=
    (((δ : targetInertiaGroup d θ) : d.ambientIntermediate) : G)
  let n : Subgroup.normalizer (R.1 : Set G) :=
    ⟨g, by
      rw [← component_stabilizer_eq_normalizer G R,
        MulAction.mem_stabilizer_iff]
      exact
        layerTargetOrbitShiftedTransporterDefect_smul_representative
          d θ a K⟩
  have hgIntermediate : g ∈ d.ambientIntermediate :=
    ((δ : targetInertiaGroup d θ) : d.ambientIntermediate).2
  have hgNormalizer :
      g ∈ Subgroup.normalizer
        (d.ambientComponentLocal : Set G) := by
    apply
      (sup_le Subgroup.le_normalizer
        (layerSylowAmbientNormalizer_le_normalizer_componentLocal
          G d.intermediate Q d.isConjugationEquivariantUnder))
      hgIntermediate
  exact
    map_coordinateSubgroup_componentNormalizerAction
      G d.intermediate d.center_le_intermediate R n hgNormalizer

/-- On an inertia element centralizing the source normal copy, every shifted
transporter defect acts trivially on its representative component. -/
theorem layerTargetOrbitShiftedDefectAutomorphism_eq_one_of_mem_centralizer
    {hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder}
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (ha :
      inertiaEmbedding d hcoordinate θ a ∈
        Subgroup.centralizer
          ((sourceTriple θ).normalSubgroup :
            Set (sourceInertiaGroup θ)))
    (K : LayerTargetOrbitCoordinate d θ o) :
    layerTargetOrbitShiftedDefectAutomorphism
        (d := d) (θ := θ) a K =
      1 := by
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  let t :=
    layerTargetComponentTransporter d θ K.1
  let g : G := (((a : targetInertiaGroup d θ) :
    d.ambientIntermediate) : G)
  have hg :
      g ∈ Subgroup.centralizer (layer G : Set G) :=
    targetInertiaAmbient_mem_centralizer_layer
      d θ hcoordinate a ha
  have hfixed :
      a • K = K :=
    targetInertia_smul_orbitCoordinate_eq_of_mem_centralizer
      d θ hcoordinate a ha K
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change
    ((layerTargetOrbitShiftedDefectAutomorphism
      (d := d) (θ := θ) a K x : R.1) : G) =
        (x : G)
  rw [layerTargetOrbitShiftedDefectAutomorphism_apply_coe]
  have hδ :=
    congrArg
      (fun z : targetInertiaGroup d θ ↦
        (((z : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G))
      (layerTargetOrbitShiftedTransporterDefect_eq_conjugate_of_fixed
        d θ a K hfixed)
  change
    (((layerTargetOrbitShiftedTransporterDefect d θ a K :
        targetInertiaGroup d θ) : d.ambientIntermediate) : G) =
      (((t : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G)⁻¹ *
        g *
      (((t : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G)
    at hδ
  rw [hδ]
  exact
    conjugate_centralizer_conjugate_eq
      (layer G) g
      (((t : targetInertiaGroup d θ) :
        d.ambientIntermediate) : G)
      (x : G) hg (R.2.le_layer x.2)

/-- A semidirect representative of every shifted transporter defect at one
target-inertia component orbit.

The representative is taken in the target coordinate group.  Its canonical
image in the source coordinate group is required to induce exactly the
ambient automorphism of the representative component.  No multiplicativity
of the chosen representatives is assumed. -/
structure CanonicalOrbitSemidirectSection
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ) where
  /-- A target coordinate semidirect representative. -/
  element :
    targetInertiaGroup d θ →
      LayerTargetOrbitCoordinate d θ o →
        d.coordinateIntermediateGroup θ
          (layerTargetComponentOrbitRepresentative d θ o)
  /-- The canonical source image induces the selected defect
  automorphism. -/
  inducedAction :
    ∀ (a : targetInertiaGroup d θ)
      (K : LayerTargetOrbitCoordinate d θ o),
      semidirectNormalAction
          (PPrimeCharacterStabilizer.ambientAction
            (P := D.coordinate
              (layerTargetComponentOrbitRepresentative d θ o))
            (χ := ComponentOrbitLocalData.coordinateLayerCharacter
              θ
              (layerTargetComponentOrbitRepresentative d θ o)))
          (d.coordinateEmbedding θ
            (layerTargetComponentOrbitRepresentative d θ o)
            (element a K)) =
        layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) a K

/-- The canonical coordinate semidirect section.  Both invariance inputs to
the Sylow-conjugacy construction are theorems for shifted transporter
defects, so no local transport hypothesis remains. -/
def canonicalOrbitSemidirectSection
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ) :
    CanonicalOrbitSemidirectSection d θ o where
  element a K :=
    Classical.choose
      (EquivariantLocalCorrespondence.exists_semidirectRepresentative_inducing
          (d.data
            (layerTargetComponentOrbitRepresentative d θ o)).toEquivariant
          (ComponentOrbitLocalData.coordinateLayerCharacter θ
            (layerTargetComponentOrbitRepresentative d θ o))
          (layerTargetOrbitShiftedDefectAutomorphism
            (d := d) (θ := θ) a K)
          (layerTargetOrbitShiftedDefectAutomorphism_intermediate_invariant
            (d := d) (θ := θ) a K)
          (layerTargetOrbitShiftedDefectAutomorphism_smul_character
            (d := d) (θ := θ) hcoordinate a K))
  inducedAction a K :=
    Classical.choose_spec
      (EquivariantLocalCorrespondence.exists_semidirectRepresentative_inducing
          (d.data
            (layerTargetComponentOrbitRepresentative d θ o)).toEquivariant
          (ComponentOrbitLocalData.coordinateLayerCharacter θ
            (layerTargetComponentOrbitRepresentative d θ o))
          (layerTargetOrbitShiftedDefectAutomorphism
            (d := d) (θ := θ) a K)
          (layerTargetOrbitShiftedDefectAutomorphism_intermediate_invariant
            (d := d) (θ := θ) a K)
          (layerTargetOrbitShiftedDefectAutomorphism_smul_character
            (d := d) (θ := θ) hcoordinate a K))

/-- Source representation space at the selected component of one target
inertia orbit. -/
abbrev semidirectOrbitSourceSpace
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ) :=
  (d.coordinateAmbientLift θ
    (layerTargetComponentOrbitRepresentative d θ o)).space

/-- Target representation space at the selected component of one target
inertia orbit. -/
abbrev semidirectOrbitTargetSpace
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (o : LayerTargetComponentOrbit d θ) :=
  (d.coordinateIntermediateLift θ
    (layerTargetComponentOrbitRepresentative d θ o)).space

noncomputable instance semidirectOrbitSourceSpaceAddCommGroup
    (o : LayerTargetComponentOrbit d θ) :
    AddCommGroup (semidirectOrbitSourceSpace d θ o) :=
  (d.coordinateAmbientLift θ
    (layerTargetComponentOrbitRepresentative d θ o)).addCommGroup

noncomputable instance semidirectOrbitSourceSpaceModule
    (o : LayerTargetComponentOrbit d θ) :
    Module ℂ (semidirectOrbitSourceSpace d θ o) :=
  (d.coordinateAmbientLift θ
    (layerTargetComponentOrbitRepresentative d θ o)).module

noncomputable instance semidirectOrbitTargetSpaceAddCommGroup
    (o : LayerTargetComponentOrbit d θ) :
    AddCommGroup (semidirectOrbitTargetSpace d θ o) :=
  (d.coordinateIntermediateLift θ
    (layerTargetComponentOrbitRepresentative d θ o)).addCommGroup

noncomputable instance semidirectOrbitTargetSpaceModule
    (o : LayerTargetComponentOrbit d θ) :
    Module ℂ (semidirectOrbitTargetSpace d θ o) :=
  (d.coordinateIntermediateLift θ
    (layerTargetComponentOrbitRepresentative d θ o)).module

namespace CanonicalOrbitSemidirectSection

variable {o : LayerTargetComponentOrbit d θ}

@[instance_reducible]
private def orbitTargetCoordinateGroupInstance :
    Group
      (d.coordinateIntermediateGroup θ
        (layerTargetComponentOrbitRepresentative d θ o)) := by
  dsimp only [ComponentOrbitLocalData.coordinateIntermediateGroup]
  infer_instance

/-- The source coordinate representative canonically paired with the chosen
target representative. -/
def sourceElement
    (S : CanonicalOrbitSemidirectSection d θ o)
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    ComponentOrbitLocalData.coordinateAmbientGroup
      (D := D) θ
      (layerTargetComponentOrbitRepresentative d θ o) :=
  d.coordinateEmbedding θ
    (layerTargetComponentOrbitRepresentative d θ o)
    (S.element a K)

/-- Failure of the chosen target semidirect representatives to be
multiplicative. -/
def multiplicationDefect
    (S : CanonicalOrbitSemidirectSection d θ o)
    (a b : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    d.coordinateIntermediateGroup θ
      (layerTargetComponentOrbitRepresentative d θ o) :=
  letI := orbitTargetCoordinateGroupInstance
    (d := d) (θ := θ) (o := o)
  S.element a K * S.element b (a⁻¹ • K) *
    (S.element (a * b) K)⁻¹

/-- The source image of the multiplication defect induces the trivial
automorphism of the representative component. -/
theorem source_multiplicationDefect_action_eq_one
    (S : CanonicalOrbitSemidirectSection d θ o)
    (a b : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    semidirectNormalAction
        (PPrimeCharacterStabilizer.ambientAction
          (P := D.coordinate
            (layerTargetComponentOrbitRepresentative d θ o))
          (χ := ComponentOrbitLocalData.coordinateLayerCharacter
            θ (layerTargetComponentOrbitRepresentative d θ o)))
        (d.coordinateEmbedding θ
          (layerTargetComponentOrbitRepresentative d θ o)
          (S.multiplicationDefect a b K)) =
      1 := by
  simp only [multiplicationDefect, map_mul, map_inv,
    CanonicalOrbitSemidirectSection.inducedAction]
  rw [layerTargetOrbitShiftedDefectAutomorphism_mul]
  simp

/-- Consequently the source image of the multiplication defect centralizes
the canonical normal copy of the representative component. -/
theorem source_multiplicationDefect_mem_centralizer
    (S : CanonicalOrbitSemidirectSection d θ o)
    (a b : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    d.coordinateEmbedding θ
          (layerTargetComponentOrbitRepresentative d θ o)
          (S.multiplicationDefect a b K) ∈
      Subgroup.centralizer
        ((ComponentOrbitLocalData.coordinateAmbientTriple
            (D := D) θ
            (layerTargetComponentOrbitRepresentative d θ o)).normalSubgroup :
          Set (ComponentOrbitLocalData.coordinateAmbientGroup
            (D := D) θ
            (layerTargetComponentOrbitRepresentative d θ o))) :=
  mem_centralizer_semidirectNormalSubgroup_of_action_eq_one
    (PPrimeCharacterStabilizer.ambientAction
      (P := D.coordinate
        (layerTargetComponentOrbitRepresentative d θ o))
      (χ := ComponentOrbitLocalData.coordinateLayerCharacter
        θ (layerTargetComponentOrbitRepresentative d θ o)))
    _
    (S.source_multiplicationDefect_action_eq_one a b K)

/-- Source projective operator attached to a chosen semidirect
representative. -/
def sourceTransport
    (S : CanonicalOrbitSemidirectSection d θ o)
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    semidirectOrbitSourceSpace d θ o ≃ₗ[ℂ]
      semidirectOrbitSourceSpace d θ o :=
  (d.coordinateAmbientLift θ
    (layerTargetComponentOrbitRepresentative d θ o)).projective.operator
      (S.sourceElement a K)

/-- Target projective operator attached to the same chosen semidirect
representative. -/
def targetTransport
    (S : CanonicalOrbitSemidirectSection d θ o)
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    semidirectOrbitTargetSpace d θ o ≃ₗ[ℂ]
      semidirectOrbitTargetSpace d θ o :=
  (d.coordinateIntermediateLift θ
    (layerTargetComponentOrbitRepresentative d θ o)).projective.operator
      (S.element a K)

/-- On a global centralizer element, the paired transports supplied by a
semidirect section act by one common coordinate scalar. -/
theorem exists_common_scalar_of_mem_centralizer
    {hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder}
    (S : CanonicalOrbitSemidirectSection d θ o)
    (a : targetInertiaGroup d θ)
    (ha :
      inertiaEmbedding d hcoordinate θ a ∈
        Subgroup.centralizer
          ((sourceTriple θ).normalSubgroup :
            Set (sourceInertiaGroup θ)))
    (K : LayerTargetOrbitCoordinate d θ o) :
    ∃ c : ℂˣ,
      S.sourceTransport a K =
          scalarLinearEquiv ℂ
            (semidirectOrbitSourceSpace d θ o) c ∧
        S.targetTransport a K =
          scalarLinearEquiv ℂ
            (semidirectOrbitTargetSpace d θ o) c := by
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  let z := S.element a K
  have haction :
      semidirectNormalAction
          (PPrimeCharacterStabilizer.ambientAction
            (P := D.coordinate R)
            (χ := ComponentOrbitLocalData.coordinateLayerCharacter θ R))
          (d.coordinateEmbedding θ R z) =
        1 := by
    calc
      semidirectNormalAction
          (PPrimeCharacterStabilizer.ambientAction
            (P := D.coordinate R)
            (χ := ComponentOrbitLocalData.coordinateLayerCharacter θ R))
          (d.coordinateEmbedding θ R z) =
        layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) a K := by
            simpa only [R, z] using S.inducedAction a K
      _ = 1 :=
        layerTargetOrbitShiftedDefectAutomorphism_eq_one_of_mem_centralizer
          (d := d) (θ := θ) a ha K
  have hz :
      d.coordinateEmbedding θ R z ∈
        Subgroup.centralizer
          ((ComponentOrbitLocalData.coordinateAmbientTriple
              (D := D) θ R).normalSubgroup :
            Set (ComponentOrbitLocalData.coordinateAmbientGroup
              (D := D) θ R)) :=
    mem_centralizer_semidirectNormalSubgroup_of_action_eq_one
      (PPrimeCharacterStabilizer.ambientAction
        (P := D.coordinate R)
        (χ := ComponentOrbitLocalData.coordinateLayerCharacter θ R))
      _ haction
  obtain ⟨c, hs, ht⟩ :=
    d.coordinateProjective_scalar_agreement θ R z hz
  exact ⟨c, by
    simpa only [sourceTransport, sourceElement, R, z] using hs, by
    simpa only [targetTransport, R, z] using ht⟩

/-- The two projective coordinate operators obtained from a semidirect
section have one common multiplication scalar. -/
theorem exists_common_mul
    (S : CanonicalOrbitSemidirectSection d θ o)
    (a b : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    ∃ c : ℂˣ,
      S.sourceTransport a K *
          S.sourceTransport b (a⁻¹ • K) =
        scalarLinearEquiv ℂ (semidirectOrbitSourceSpace d θ o) c *
          S.sourceTransport (a * b) K ∧
      S.targetTransport a K *
          S.targetTransport b (a⁻¹ • K) =
        scalarLinearEquiv ℂ (semidirectOrbitTargetSpace d θ o) c *
          S.targetTransport (a * b) K := by
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  let Ls := d.coordinateAmbientLift θ R
  let Lt := d.coordinateIntermediateLift θ R
  let x := S.element a K
  let y := S.element b (a⁻¹ • K)
  let t := S.element (a * b) K
  let z := S.multiplicationDefect a b K
  have hxy : x * y = z * t := by
    simp only [z, multiplicationDefect, x, y, t]
    group
  obtain ⟨c, hsourceScalar, htargetScalar⟩ :=
    d.coordinateProjective_scalar_agreement θ R z
      (S.source_multiplicationDefect_mem_centralizer a b K)
  have hcommon :=
    ProjectiveRepresentation.exists_common_operator_mul
      Ls.projective Lt.projective
      (d.coordinateEmbedding θ R)
      (d.coordinateProjective_factor_agreement θ R)
      x y z t hxy c hsourceScalar htargetScalar
  simpa only [sourceTransport, targetTransport, sourceElement,
    x, y, t, Ls, Lt, R] using hcommon

/-- Semidirect sections and the complete component witness construct paired
source/target coordinate transports with one common projective
multiplication scalar. -/
def pairedTransport
    (S : CanonicalOrbitSemidirectSection d θ o) :
    PairedFiniteTensorPermutationTransport
      (K := ℂ) (A := targetInertiaGroup d θ)
      (ι := LayerTargetOrbitCoordinate d θ o)
      (V := semidirectOrbitSourceSpace d θ o)
      (W := semidirectOrbitTargetSpace d θ o) := by
  exact
    { sourceTransport := S.sourceTransport
      targetTransport := S.targetTransport
      common_mul := S.exists_common_mul }

end CanonicalOrbitSemidirectSection

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
