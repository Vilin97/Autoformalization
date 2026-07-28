/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerTargetProjectiveAssembly

/-!
# Canonical coordinates for the layer tensor-permutation construction

The target inertia group acts on the finite set of components by ambient
conjugation.  Its orbits and the components in each orbit are therefore the
canonical outer and inner indices for the tensor-permutation construction.

This file constructs those finite index types and their permutation actions.
No projective representation or choice of coordinate transporter is used.
-/

noncomputable section

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
  (d : ComponentOrbitLocalData D)
  (θ : PPrimeIrreducibleCharacter (layer G) p)

/-- Orbits of components under the matched target inertia group. -/
abbrev LayerTargetComponentOrbit :=
  MulAction.orbitRel.Quotient
    (targetInertiaGroup d θ) (ComponentIndex G)

/-- The target-inertia orbit containing a component. -/
def layerTargetComponentOrbitOf
    (K : ComponentIndex G) :
    LayerTargetComponentOrbit d θ :=
  Quotient.mk'' K

/-- The representative selected for a target-inertia component orbit. -/
def layerTargetComponentOrbitRepresentative
    (o : LayerTargetComponentOrbit d θ) :
    ComponentIndex G :=
  Quotient.out o

@[simp]
theorem layerTargetComponentOrbitOf_representative
    (o : LayerTargetComponentOrbit d θ) :
    layerTargetComponentOrbitOf d θ
        (layerTargetComponentOrbitRepresentative d θ o) =
      o :=
  Quotient.out_eq' o

@[simp]
theorem layerTargetComponentOrbitOf_smul
    (a : targetInertiaGroup d θ)
    (K : ComponentIndex G) :
    layerTargetComponentOrbitOf d θ (a • K) =
      layerTargetComponentOrbitOf d θ K :=
  Quotient.sound (MulAction.mem_orbit K a)

/-- Components belonging to one target-inertia orbit. -/
abbrev LayerTargetOrbitCoordinate
    (o : LayerTargetComponentOrbit d θ) :=
  {K : ComponentIndex G //
    layerTargetComponentOrbitOf d θ K = o}

noncomputable instance layerTargetComponentOrbitFintype :
    Fintype (LayerTargetComponentOrbit d θ) :=
  Fintype.ofFinite _

noncomputable instance layerTargetOrbitCoordinateFintype
    (o : LayerTargetComponentOrbit d θ) :
    Fintype (LayerTargetOrbitCoordinate d θ o) :=
  Fintype.ofFinite _

/-- The target inertia group permutes the components inside each one of its
orbits. -/
instance layerTargetOrbitCoordinateMulAction
    (o : LayerTargetComponentOrbit d θ) :
    MulAction (targetInertiaGroup d θ)
      (LayerTargetOrbitCoordinate d θ o) where
  smul a K :=
    ⟨a • K.1, by
      rw [layerTargetComponentOrbitOf_smul, K.2]⟩
  one_smul K := by
    apply Subtype.ext
    exact one_smul _ _
  mul_smul a b K := by
    apply Subtype.ext
    exact mul_smul _ _ _

@[simp]
theorem layerTargetOrbitCoordinate_smul_val
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    (a • K).1 = a • K.1 :=
  rfl

/-- The selected component representative, regarded as a coordinate in its
own orbit. -/
def layerTargetOrbitRepresentativeCoordinate
    (o : LayerTargetComponentOrbit d θ) :
    LayerTargetOrbitCoordinate d θ o :=
  ⟨layerTargetComponentOrbitRepresentative d θ o,
    layerTargetComponentOrbitOf_representative d θ o⟩

/-- Decomposing the component set into its target-inertia orbits loses no
coordinates. -/
def layerTargetOrbitCoordinateSigmaEquiv :
    (Σ o : LayerTargetComponentOrbit d θ,
      LayerTargetOrbitCoordinate d θ o) ≃
      ComponentIndex G where
  toFun x := x.2.1
  invFun K :=
    ⟨layerTargetComponentOrbitOf d θ K, ⟨K, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨o, ⟨K, hK⟩⟩
    subst o
    rfl
  right_inv _ := rfl

/-! ### Selected transporters and their stabilizer defect -/

/-- A selected target-inertia element carrying the representative of the
orbit of `K` to `K`. -/
def layerTargetComponentTransporter
    (K : ComponentIndex G) :
    targetInertiaGroup d θ :=
  OrbitExtension.transporter
    (targetInertiaGroup d θ) (ComponentIndex G) K

@[simp]
theorem layerTargetComponentTransporter_smul_representative
    (K : ComponentIndex G) :
    layerTargetComponentTransporter d θ K •
        layerTargetComponentOrbitRepresentative d θ
          (layerTargetComponentOrbitOf d θ K) =
      K :=
  OrbitExtension.transporter_smul_representative
    (targetInertiaGroup d θ) (ComponentIndex G) K

/-- The defect between the selected transporter to `a • K` and the
transporter obtained by first going to `K` and then applying `a`.

It lies in the stabilizer of the selected orbit representative; this is the
exact local group on which coherent intertwiner choices must be controlled.
-/
def layerTargetOrbitTransporterDefect
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    targetInertiaGroup d θ :=
  (layerTargetComponentTransporter d θ (a • K.1))⁻¹ *
    a * layerTargetComponentTransporter d θ K.1

@[simp]
theorem layerTargetOrbitTransporterDefect_smul_representative
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    layerTargetOrbitTransporterDefect d θ a K •
        layerTargetComponentOrbitRepresentative d θ o =
      layerTargetComponentOrbitRepresentative d θ o := by
  let tK :=
    layerTargetComponentTransporter d θ K.1
  let taK :=
    layerTargetComponentTransporter d θ (a • K.1)
  have hK :
      tK • layerTargetComponentOrbitRepresentative d θ o =
        K.1 := by
    simpa only [tK, K.2] using
      layerTargetComponentTransporter_smul_representative
        d θ K.1
  have haK :
      taK • layerTargetComponentOrbitRepresentative d θ o =
        a • K.1 := by
    have horbit :
        layerTargetComponentOrbitOf d θ (a • K.1) = o := by
      rw [layerTargetComponentOrbitOf_smul, K.2]
    simpa only [taK, horbit] using
      layerTargetComponentTransporter_smul_representative
        d θ (a • K.1)
  calc
    layerTargetOrbitTransporterDefect d θ a K •
          layerTargetComponentOrbitRepresentative d θ o =
        taK⁻¹ •
          (a •
            (tK •
              layerTargetComponentOrbitRepresentative d θ o)) := by
        simp only [layerTargetOrbitTransporterDefect, taK, tK,
          mul_smul]
    _ = taK⁻¹ • (a • K.1) := by rw [hK]
    _ = taK⁻¹ •
        (taK •
          layerTargetComponentOrbitRepresentative d θ o) := by
      rw [haK]
    _ = layerTargetComponentOrbitRepresentative d θ o :=
      inv_smul_smul _ _

/-- The transporter defect with the coordinate convention used by a
tensor-permutation operator: the operator at output coordinate `K` compares
the selected transports to `a⁻¹ • K` and to `K`. -/
def layerTargetOrbitShiftedTransporterDefect
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    targetInertiaGroup d θ :=
  layerTargetOrbitTransporterDefect d θ a (a⁻¹ • K)

@[simp]
theorem layerTargetOrbitShiftedTransporterDefect_smul_representative
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    layerTargetOrbitShiftedTransporterDefect d θ a K •
        layerTargetComponentOrbitRepresentative d θ o =
      layerTargetComponentOrbitRepresentative d θ o :=
  layerTargetOrbitTransporterDefect_smul_representative
    d θ a (a⁻¹ • K)

/-- Shifted transporter defects compose in exactly the order required by
the coordinate transport law
`T(a,K) T(b,a⁻¹ • K) = T(ab,K)`. -/
theorem layerTargetOrbitShiftedTransporterDefect_mul
    {o : LayerTargetComponentOrbit d θ}
    (a b : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    layerTargetOrbitShiftedTransporterDefect d θ a K *
        layerTargetOrbitShiftedTransporterDefect d θ b (a⁻¹ • K) =
      layerTargetOrbitShiftedTransporterDefect d θ (a * b) K := by
  simp only [layerTargetOrbitShiftedTransporterDefect,
    layerTargetOrbitTransporterDefect,
    layerTargetOrbitCoordinate_smul_val, smul_inv_smul]
  group
  rw [mul_smul]

/-- If `a` fixes the output coordinate, its shifted defect is the conjugate
of `a` by the selected transporter to that coordinate. -/
theorem layerTargetOrbitShiftedTransporterDefect_eq_conjugate_of_fixed
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o)
    (hfixed : a • K = K) :
    layerTargetOrbitShiftedTransporterDefect d θ a K =
      (layerTargetComponentTransporter d θ K.1)⁻¹ *
        a * layerTargetComponentTransporter d θ K.1 := by
  have hinv : a⁻¹ • K = K := by
    calc
      a⁻¹ • K = a⁻¹ • (a • K) := by rw [hfixed]
      _ = K := inv_smul_smul a K
  have hfixedVal : a • K.1 = K.1 :=
    congrArg Subtype.val hfixed
  simp only [layerTargetOrbitShiftedTransporterDefect,
    layerTargetOrbitTransporterDefect,
    hinv, hfixedVal]

/-! ### Centralizer elements fix all component coordinates -/

/-- If the image of a target-inertia element centralizes the normal copy in
the source inertia triple, then its ambient element centralizes the layer. -/
theorem targetInertiaAmbient_mem_centralizer_layer
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (a : targetInertiaGroup d θ)
    (ha :
      inertiaEmbedding d hcoordinate θ a ∈
        Subgroup.centralizer
          ((sourceTriple θ).normalSubgroup :
            Set (sourceInertiaGroup θ))) :
    (((a : d.ambientIntermediate) : G)) ∈
      Subgroup.centralizer (layer G : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  let xL : layer G := ⟨x, hx⟩
  let xI : sourceInertiaGroup θ :=
    IrreducibleCharacter.inertiaInclusion
      (layer G) θ.1 xL
  let xN : (sourceTriple θ).normalSubgroup :=
    ⟨xI, hx⟩
  have hcomm :=
    Subgroup.mem_centralizer_iff.mp ha xN xN.2
  have hcommAmbient :=
    congrArg
      (fun y : sourceInertiaGroup θ => (y : G))
      hcomm
  change
    x * ((inertiaEmbedding d hcoordinate θ a :
        sourceInertiaGroup θ) : G) =
      ((inertiaEmbedding d hcoordinate θ a :
        sourceInertiaGroup θ) : G) * x
    at hcommAmbient
  simpa only [inertiaEmbedding_apply_coe] using hcommAmbient

/-- A target-inertia element centralizing the source normal copy fixes every
component under the canonical conjugation action. -/
theorem targetInertia_smul_component_eq_of_mem_centralizer
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (a : targetInertiaGroup d θ)
    (ha :
      inertiaEmbedding d hcoordinate θ a ∈
        Subgroup.centralizer
          ((sourceTriple θ).normalSubgroup :
            Set (sourceInertiaGroup θ)))
    (K : ComponentIndex G) :
    a • K = K := by
  let g : G := ((a : d.ambientIntermediate) : G)
  have hg :
      g ∈ Subgroup.centralizer (layer G : Set G) :=
    targetInertiaAmbient_mem_centralizer_layer
      d θ hcoordinate a ha
  apply Subtype.ext
  change
    K.1.map (MulAut.conj g).toMonoidHom = K.1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hcomm :
        (y : G) * g = g * (y : G) :=
      Subgroup.mem_centralizer_iff.mp hg
        (y : G) (K.2.le_layer hy)
    have hconj :
        g * (y : G) * g⁻¹ = (y : G) := by
      rw [← hcomm]
      simp
    change g * (y : G) * g⁻¹ ∈ K.1
    rw [hconj]
    exact hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    have hcomm :
        x * g = g * x :=
      Subgroup.mem_centralizer_iff.mp hg
        x (K.2.le_layer hx)
    change g * x * g⁻¹ = x
    rw [← hcomm]
    simp

/-- The preceding fixed-component statement restricted to one canonical
orbit coordinate. -/
theorem targetInertia_smul_orbitCoordinate_eq_of_mem_centralizer
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (a : targetInertiaGroup d θ)
    (ha :
      inertiaEmbedding d hcoordinate θ a ∈
        Subgroup.centralizer
          ((sourceTriple θ).normalSubgroup :
            Set (sourceInertiaGroup θ)))
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o) :
    a • K = K := by
  apply Subtype.ext
  exact
    targetInertia_smul_component_eq_of_mem_centralizer
      d θ hcoordinate a ha K.1

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
