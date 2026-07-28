/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.LayerIntermediateNormalizerInvariant
import McKayConjecture.GroupTheory.LayerSylowNormalizerAction
import McKayConjecture.GroupTheory.ComponentStabilizer
import McKayConjecture.InductiveMcKay.EquivariantTransport
import McKayConjecture.InductiveMcKay.LayerComponentLocalData

/-!
# Coherent local data on component orbits

Local inductive-McKay data may be chosen on one component in each orbit of
the ambient normalizer of a layer Sylow subgroup.  Transport along ambient
conjugation then propagates its intermediate subgroup around that orbit.
The automorphism-invariance built into the full local datum makes the result
independent of the chosen transporter.

This file first isolates the elementary orbit-extension construction.  It is
then applied to component intermediates, viewed inside the ambient group so
that the dependent carrier types of conjugate components do not enter the
choice-independence argument.
-/

noncomputable section

open scoped Pointwise

universe u v w

namespace McKayConjecture
namespace InductiveMcKay

/-! ### Equivariant extension from orbit representatives -/

namespace OrbitExtension

variable (A : Type u) [Group A]
variable (X : Type v) [MulAction A X]

/-- The set of orbits of `A` on `X`. -/
abbrev Orbit :=
  MulAction.orbitRel.Quotient A X

/-- The representative selected by `Quotient.out`. -/
def representative (q : Orbit A X) : X :=
  Quotient.out q

/-- The orbit containing `x`. -/
def orbitOf (x : X) : Orbit A X :=
  Quotient.mk'' x

@[simp]
theorem orbitOf_smul (g : A) (x : X) :
    orbitOf A X (g • x) = orbitOf A X x :=
  Quotient.sound (MulAction.mem_orbit x g)

/-- Every point is reached from the selected representative of its orbit. -/
theorem exists_smul_representative_eq (x : X) :
    ∃ g : A, g • representative A X (orbitOf A X x) = x := by
  apply MulAction.mem_orbit_iff.mp
  exact Quotient.exact
    (Quotient.out_eq'
      (orbitOf A X x)).symm

/-- A selected transporter from the orbit representative to `x`. -/
def transporter (x : X) : A :=
  Classical.choose
    (exists_smul_representative_eq A X x)

@[simp]
theorem transporter_smul_representative (x : X) :
    transporter A X x •
        representative A X (orbitOf A X x) =
      x :=
  Classical.choose_spec
    (exists_smul_representative_eq A X x)

variable (Y : Type w) [MulAction A Y]

/-- Extend stabilizer-fixed values on selected orbit representatives to all
of `X`. -/
def extend (y : Orbit A X → Y) (x : X) : Y :=
  transporter A X x • y (orbitOf A X x)

/-- The orbit extension is equivariant.  Choice independence is exactly the
assumption that every representative value is fixed by its stabilizer. -/
theorem extend_smul
    (y : Orbit A X → Y)
    (hy : ∀ (q : Orbit A X) (s : A),
      s • representative A X q =
          representative A X q →
        s • y q = y q)
    (g : A) (x : X) :
    extend A X Y y (g • x) =
      g • extend A X Y y x := by
  let q : Orbit A X := orbitOf A X x
  have hq :
      orbitOf A X (g • x) = q :=
    orbitOf_smul A X g x
  let a : A := transporter A X x
  let b : A := transporter A X (g • x)
  let s : A := b⁻¹ * g * a
  have hs :
      s • representative A X q =
        representative A X q := by
    calc
      s • representative A X q =
          b⁻¹ •
            (g • (a • representative A X q)) := by
        simp only [s, mul_smul]
      _ = b⁻¹ • (g • x) := by
        rw [transporter_smul_representative]
      _ = b⁻¹ •
          (b • representative A X
            (orbitOf A X (g • x))) := by
        rw [transporter_smul_representative]
      _ = representative A X
          (orbitOf A X (g • x)) := by
        rw [inv_smul_smul]
      _ = representative A X q := by
        rw [hq]
  have hfixed : s • y q = y q :=
    hy q s hs
  change
    b • y (orbitOf A X (g • x)) =
      g • (a • y q)
  rw [hq]
  have hfixed' :=
    congrArg (fun z : Y ↦ b • z) hfixed
  have hfixed'' :
      (b * s) • y q = b • y q := by
    simpa only [mul_smul] using hfixed'
  have hmul : b * s = g * a := by
    simp only [s, ← mul_assoc, mul_inv_cancel,
      one_mul]
  calc
    b • y q = (b * s) • y q :=
      hfixed''.symm
    _ = (g * a) • y q := by rw [hmul]
    _ = g • (a • y q) := mul_smul _ _ _

end OrbitExtension

/-! ### Stabilizer-fixed representative intermediates -/

open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}

private local instance componentOrbitAmbientSubgroupMulAction :
    MulAction
      (LayerSylowAmbientNormalizer G Q)
      (Subgroup G) :=
  MulAction.compHom
    (Subgroup G)
    ((MulAut.conj : G →* MulAut G).comp
      (LayerSylowAmbientNormalizer G Q).subtype)

omit [Finite G] [Fact p.Prime] in
private theorem ambientSubgroup_smul_def
    (g : LayerSylowAmbientNormalizer G Q)
    (N : Subgroup G) :
    g • N =
      N.map (MulAut.conj g.1).toMonoidHom :=
  rfl

/-- Component orbits under the ambient normalizer of the selected layer
Sylow subgroup. -/
abbrev LayerComponentOrbit :=
  OrbitExtension.Orbit
    (LayerSylowAmbientNormalizer G Q)
    (ComponentIndex G)

/-- The component selected as representative of an ambient-normalizer
orbit. -/
abbrev layerComponentOrbitRepresentative
    (q : LayerComponentOrbit (G := G) (Q := Q)) :
    ComponentIndex G :=
  OrbitExtension.representative
    (LayerSylowAmbientNormalizer G Q)
    (ComponentIndex G) q

/-- A full local datum chosen once on each component orbit. -/
def layerComponentOrbitRepresentativeData
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (q : LayerComponentOrbit (G := G) (Q := Q)) :
    LocalInductiveMcKayData
      (D.coordinate
        (layerComponentOrbitRepresentative q)) :=
  Classical.choice
    (hdata (layerComponentOrbitRepresentative q))

/-- The representative intermediate, embedded in the ambient group. -/
def layerComponentOrbitRepresentativeIntermediate
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (q : LayerComponentOrbit (G := G) (Q := Q)) :
    Subgroup G :=
  ((layerComponentOrbitRepresentativeData D hdata q).intermediate).map
    (layerComponentOrbitRepresentative q).1.subtype

/-- An ambient-normalizer element fixing a component acts on that
component by an automorphism. -/
def componentOrbitStabilizerAutomorphism
    (K : ComponentIndex G)
    (g : LayerSylowAmbientNormalizer G Q)
    (hg : g.1 • K = K) :
    MulAut K.1 :=
  componentNormalizerAction G K
    ⟨g.1, by
      rw [← component_stabilizer_eq_normalizer G K,
        MulAction.mem_stabilizer_iff]
      exact hg⟩

omit [Finite G] [Fact p.Prime] in
@[simp]
theorem componentOrbitStabilizerAutomorphism_apply_coe
    (K : ComponentIndex G)
    (g : LayerSylowAmbientNormalizer G Q)
    (hg : g.1 • K = K)
    (x : K.1) :
    ((componentOrbitStabilizerAutomorphism
        (G := G) K g hg x : K.1) : G) =
      g.1 * (x : G) * g.1⁻¹ :=
  rfl

/-- The automorphism induced by an orbit stabilizer also stabilizes the
chosen coordinate Sylow subgroup. -/
theorem componentOrbitStabilizerAutomorphism_mem
    (D : LayerSylowCoordinateData G p Q)
    (K : ComponentIndex G)
    (g : LayerSylowAmbientNormalizer G Q)
    (hg : g.1 • K = K) :
    componentOrbitStabilizerAutomorphism
        (G := G) K g hg ∈
      SylowAutStabilizer (D.coordinate K) := by
  rw [SylowAutStabilizer.mem_iff]
  apply Sylow.ext
  have hcoordinate :=
    GroupTheory.LayerSylowCoordinateData.componentConjugate_coordinate_eq_of_mem_ambient_normalizer
      (G := G) D g.1 g.2 K
  have hcoordinateAmbient :=
    congrArg
      (fun P : Sylow p (g.1 • K).1 ↦
        (P : Subgroup (g.1 • K).1).map
          (g.1 • K).1.subtype)
      hcoordinate
  have hindexAmbient :=
    congrArg
      (fun L : ComponentIndex G ↦
        (D.coordinate L : Subgroup L.1).map
          L.1.subtype)
      hg
  change
    (D.coordinate K : Subgroup K.1).map
        (componentOrbitStabilizerAutomorphism
          (G := G) K g hg).toMonoidHom =
      (D.coordinate K : Subgroup K.1)
  apply Subgroup.map_injective K.1.subtype_injective
  calc
    ((D.coordinate K : Subgroup K.1).map
          (componentOrbitStabilizerAutomorphism
            (G := G) K g hg).toMonoidHom).map
          K.1.subtype =
        (D.coordinate K : Subgroup K.1).map
          (K.1.subtype.comp
            (componentOrbitStabilizerAutomorphism
              (G := G) K g hg).toMonoidHom) := by
      rw [Subgroup.map_map]
    _ =
        (D.coordinate K : Subgroup K.1).map
          ((MulAut.conj g.1).toMonoidHom.comp
            K.1.subtype) := by
      congr 1
    _ =
        (D.coordinate K : Subgroup K.1).map
          ((g.1 • K).1.subtype.comp
            (componentConjugationEquiv
              G g.1 K).toMonoidHom) := by
      rw [component_subtype_comp_componentConjugationEquiv]
    _ =
        ((D.coordinate K : Subgroup K.1).map
          (componentConjugationEquiv
            G g.1 K).toMonoidHom).map
              (g.1 • K).1.subtype := by
      rw [Subgroup.map_map]
    _ =
        (componentConjugateSylow
          G g.1 K (D.coordinate K) :
            Subgroup (g.1 • K).1).map
              (g.1 • K).1.subtype :=
      rfl
    _ =
        (D.coordinate (g.1 • K) :
          Subgroup (g.1 • K).1).map
            (g.1 • K).1.subtype :=
      hcoordinateAmbient
    _ =
        (D.coordinate K : Subgroup K.1).map
          K.1.subtype :=
      hindexAmbient

/-- The embedded representative intermediate is fixed by every
ambient-normalizer element stabilizing the representative component. -/
theorem layerComponentOrbitRepresentativeIntermediate_fixed
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (q : LayerComponentOrbit (G := G) (Q := Q))
    (g : LayerSylowAmbientNormalizer G Q)
    (hg :
      g.1 • layerComponentOrbitRepresentative q =
        layerComponentOrbitRepresentative q) :
    g • layerComponentOrbitRepresentativeIntermediate
        D hdata q =
      layerComponentOrbitRepresentativeIntermediate
        D hdata q := by
  let K : ComponentIndex G :=
    layerComponentOrbitRepresentative q
  let d : LocalInductiveMcKayData (D.coordinate K) :=
    layerComponentOrbitRepresentativeData D hdata q
  let a : SylowAutStabilizer (D.coordinate K) :=
    ⟨componentOrbitStabilizerAutomorphism
        (G := G) K g hg,
      componentOrbitStabilizerAutomorphism_mem
        D K g hg⟩
  have hinvariant :
      d.intermediate.map a.1.toMonoidHom =
        d.intermediate :=
    d.intermediate_invariant a
  rw [ambientSubgroup_smul_def]
  change
    (d.intermediate.map K.1.subtype).map
        (MulAut.conj g.1).toMonoidHom =
      d.intermediate.map K.1.subtype
  calc
    (d.intermediate.map K.1.subtype).map
          (MulAut.conj g.1).toMonoidHom =
        d.intermediate.map
          ((MulAut.conj g.1).toMonoidHom.comp
            K.1.subtype) := by
      rw [Subgroup.map_map]
    _ =
        d.intermediate.map
          (K.1.subtype.comp a.1.toMonoidHom) := by
      congr 1
    _ =
        (d.intermediate.map a.1.toMonoidHom).map
          K.1.subtype := by
      rw [Subgroup.map_map]
    _ = d.intermediate.map K.1.subtype := by
      rw [hinvariant]

/-! ### The coherent ambient family -/

/-- Propagate the representative intermediates around their component
orbits by ambient conjugation. -/
def coherentComponentAmbientIntermediate
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (K : ComponentIndex G) :
    Subgroup G :=
  OrbitExtension.extend
    (LayerSylowAmbientNormalizer G Q)
    (ComponentIndex G)
    (Subgroup G)
    (layerComponentOrbitRepresentativeIntermediate
      D hdata)
    K

/-- The propagated ambient intermediate family is equivariant under the
ambient normalizer. -/
theorem coherentComponentAmbientIntermediate_smul
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (g : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G) :
    coherentComponentAmbientIntermediate
        D hdata (g.1 • K) =
      g • coherentComponentAmbientIntermediate
        D hdata K :=
  OrbitExtension.extend_smul
    (LayerSylowAmbientNormalizer G Q)
    (ComponentIndex G)
    (Subgroup G)
    (layerComponentOrbitRepresentativeIntermediate
      D hdata)
    (layerComponentOrbitRepresentativeIntermediate_fixed
      D hdata)
    g K

/-! ### Exact transported local data -/

omit [Finite G] [Fact p.Prime] in
/-- The selected orbit transporter carries the representative component
exactly to `K`, stated for the ambient `G`-action. -/
theorem layerComponentOrbitTransporter_smul_representative
    (K : ComponentIndex G) :
    (OrbitExtension.transporter
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) K).1 •
        layerComponentOrbitRepresentative
          (OrbitExtension.orbitOf
            (LayerSylowAmbientNormalizer G Q)
            (ComponentIndex G) K) =
      K :=
  OrbitExtension.transporter_smul_representative
    (LayerSylowAmbientNormalizer G Q)
    (ComponentIndex G) K

/-- The canonical carrier equivalence from the representative of the orbit
of `K` to `K`, using the selected orbit transporter. -/
def layerComponentOrbitTransportEquiv
    (K : ComponentIndex G) :
    (layerComponentOrbitRepresentative
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)).1 ≃*
      K.1 :=
  (componentConjugationEquiv G
      (OrbitExtension.transporter
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) K).1
      (layerComponentOrbitRepresentative
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K))).trans
    (MulEquiv.subgroupCongr
      (congrArg Subtype.val
        (layerComponentOrbitTransporter_smul_representative
          (G := G) (Q := Q) K)))

omit [Finite G] [Fact p.Prime] in
@[simp]
theorem layerComponentOrbitTransportEquiv_apply_coe
    (K : ComponentIndex G)
    (x :
      (layerComponentOrbitRepresentative
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)).1) :
    ((layerComponentOrbitTransportEquiv
        (G := G) (Q := Q) K x : K.1) : G) =
      (OrbitExtension.transporter
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K).1 *
        (x : G) *
        (OrbitExtension.transporter
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K).1⁻¹ := by
  simp only [layerComponentOrbitTransportEquiv,
    MulEquiv.trans_apply,
    MulEquiv.subgroupCongr_apply,
    componentConjugationEquiv_apply_coe]

/-- Transport along the selected component equivalence takes the
representative coordinate Sylow subgroup exactly to the coordinate at
`K`. -/
theorem layerComponentOrbitTransport_coordinate
    (D : LayerSylowCoordinateData G p Q)
    (K : ComponentIndex G) :
    McKayConjecture.Sylow.transport
        (layerComponentOrbitTransportEquiv
          (G := G) (Q := Q) K)
        (D.coordinate
          (layerComponentOrbitRepresentative
            (OrbitExtension.orbitOf
              (LayerSylowAmbientNormalizer G Q)
              (ComponentIndex G) K))) =
      D.coordinate K := by
  let q : LayerComponentOrbit (G := G) (Q := Q) :=
    OrbitExtension.orbitOf
      (LayerSylowAmbientNormalizer G Q)
      (ComponentIndex G) K
  let R : ComponentIndex G :=
    layerComponentOrbitRepresentative q
  let g : LayerSylowAmbientNormalizer G Q :=
    OrbitExtension.transporter
      (LayerSylowAmbientNormalizer G Q)
      (ComponentIndex G) K
  have hg : g.1 • R = K :=
    layerComponentOrbitTransporter_smul_representative
      (G := G) (Q := Q) K
  have hcoordinate :=
    GroupTheory.LayerSylowCoordinateData.componentConjugate_coordinate_eq_of_mem_ambient_normalizer
      (G := G) D g.1 g.2 R
  have hcoordinateAmbient :=
    congrArg
      (fun P : Sylow p (g.1 • R).1 ↦
        (P : Subgroup (g.1 • R).1).map
          (g.1 • R).1.subtype)
      hcoordinate
  have hindexAmbient :=
    congrArg
      (fun L : ComponentIndex G ↦
        (D.coordinate L : Subgroup L.1).map
          L.1.subtype)
      hg
  apply Sylow.ext
  rw [McKayConjecture.Sylow.coe_transport]
  change
    (D.coordinate R : Subgroup R.1).map
        (layerComponentOrbitTransportEquiv
          (G := G) (Q := Q) K).toMonoidHom =
      (D.coordinate K : Subgroup K.1)
  apply Subgroup.map_injective K.1.subtype_injective
  calc
    ((D.coordinate R : Subgroup R.1).map
          (layerComponentOrbitTransportEquiv
            (G := G) (Q := Q) K).toMonoidHom).map
          K.1.subtype =
        (D.coordinate R : Subgroup R.1).map
          (K.1.subtype.comp
            (layerComponentOrbitTransportEquiv
              (G := G) (Q := Q) K).toMonoidHom) := by
      rw [Subgroup.map_map]
    _ =
        (D.coordinate R : Subgroup R.1).map
          ((MulAut.conj g.1).toMonoidHom.comp
            R.1.subtype) := by
      congr 1
    _ =
        (D.coordinate R : Subgroup R.1).map
          ((g.1 • R).1.subtype.comp
            (componentConjugationEquiv
              G g.1 R).toMonoidHom) := by
      rw [component_subtype_comp_componentConjugationEquiv]
    _ =
        ((D.coordinate R : Subgroup R.1).map
          (componentConjugationEquiv
            G g.1 R).toMonoidHom).map
              (g.1 • R).1.subtype := by
      rw [Subgroup.map_map]
    _ =
        (componentConjugateSylow
          G g.1 R (D.coordinate R) :
            Subgroup (g.1 • R).1).map
              (g.1 • R).1.subtype :=
      rfl
    _ =
        (D.coordinate (g.1 • R) :
          Subgroup (g.1 • R).1).map
            (g.1 • R).1.subtype :=
      hcoordinateAmbient
    _ =
        (D.coordinate K : Subgroup K.1).map
          K.1.subtype :=
      hindexAmbient

/-- Cast the Sylow index of a full local datum without changing its
ambient group. -/
def LocalInductiveMcKayData.cast
    {X : Type u} [Group X] [Finite X]
    {P R : Sylow p X}
    (h : P = R)
    (d : LocalInductiveMcKayData P) :
    LocalInductiveMcKayData R :=
  h ▸ d

omit [Fact p.Prime] in
@[simp]
theorem LocalInductiveMcKayData.cast_intermediate
    {X : Type u} [Group X] [Finite X]
    {P R : Sylow p X}
    (h : P = R)
    (d : LocalInductiveMcKayData P) :
    (LocalInductiveMcKayData.cast h d).intermediate =
      d.intermediate := by
  cases h
  rfl

/-- Full local data at `K`, obtained by transporting the datum selected at
the representative of its component orbit. -/
def coherentComponentLocalData
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (K : ComponentIndex G) :
    LocalInductiveMcKayData (D.coordinate K) :=
  LocalInductiveMcKayData.cast
    (layerComponentOrbitTransport_coordinate D K)
    (LocalInductiveMcKayData.transport
      (layerComponentOrbitTransportEquiv
        (G := G) (Q := Q) K)
      (D.coordinate
        (layerComponentOrbitRepresentative
          (OrbitExtension.orbitOf
            (LayerSylowAmbientNormalizer G Q)
            (ComponentIndex G) K)))
      (layerComponentOrbitRepresentativeData
        D hdata
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)))

@[simp]
theorem coherentComponentLocalData_intermediate
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (K : ComponentIndex G) :
    (coherentComponentLocalData D hdata K).intermediate =
      (layerComponentOrbitRepresentativeData
        D hdata
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)).intermediate.map
        (layerComponentOrbitTransportEquiv
          (G := G) (Q := Q) K).toMonoidHom := by
  rw [coherentComponentLocalData,
    LocalInductiveMcKayData.cast_intermediate]
  rfl

/-- Embedding the transported intermediate at `K` into `G` recovers the
ambient orbit extension. -/
theorem map_coherentComponentLocalData_intermediate
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (K : ComponentIndex G) :
    ((coherentComponentLocalData D hdata K).intermediate).map
        K.1.subtype =
      coherentComponentAmbientIntermediate D hdata K := by
  let q : LayerComponentOrbit (G := G) (Q := Q) :=
    OrbitExtension.orbitOf
      (LayerSylowAmbientNormalizer G Q)
      (ComponentIndex G) K
  let R : ComponentIndex G :=
    layerComponentOrbitRepresentative q
  let g : LayerSylowAmbientNormalizer G Q :=
    OrbitExtension.transporter
      (LayerSylowAmbientNormalizer G Q)
      (ComponentIndex G) K
  let d : LocalInductiveMcKayData (D.coordinate R) :=
    layerComponentOrbitRepresentativeData D hdata q
  rw [coherentComponentLocalData_intermediate]
  change
    (d.intermediate.map
      (layerComponentOrbitTransportEquiv
        (G := G) (Q := Q) K).toMonoidHom).map
          K.1.subtype =
      g • d.intermediate.map R.1.subtype
  rw [ambientSubgroup_smul_def]
  calc
    (d.intermediate.map
          (layerComponentOrbitTransportEquiv
            (G := G) (Q := Q) K).toMonoidHom).map
          K.1.subtype =
        d.intermediate.map
          (K.1.subtype.comp
            (layerComponentOrbitTransportEquiv
              (G := G) (Q := Q) K).toMonoidHom) := by
      rw [Subgroup.map_map]
    _ =
        d.intermediate.map
          ((MulAut.conj g.1).toMonoidHom.comp
            R.1.subtype) := by
      congr 1
    _ =
        (d.intermediate.map R.1.subtype).map
          (MulAut.conj g.1).toMonoidHom := by
      rw [Subgroup.map_map]

/-! ### The coherent component-local family -/

/-- The intermediate subgroup extracted from the coherently transported
full local datum. -/
abbrev coherentComponentIntermediate
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (K : ComponentIndex G) :
    Subgroup K.1 :=
  (coherentComponentLocalData D hdata K).intermediate

/-- The coherently transported intermediates form an exactly
conjugation-equivariant component-local family under the ambient
normalizer of `Q`. -/
theorem coherentComponentIntermediate_equivariant
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K))) :
    ComponentLocalFamily.IsConjugationEquivariantUnder
      G (LayerSylowAmbientNormalizer G Q)
      (coherentComponentIntermediate D hdata) := by
  intro g K
  apply
    Subgroup.map_injective
      (g.1 • K).1.subtype_injective
  calc
    (componentConjugateSubgroup G g.1 K
          (coherentComponentIntermediate
            D hdata K)).map
          (g.1 • K).1.subtype =
        ((coherentComponentIntermediate
            D hdata K).map K.1.subtype).map
          (MulAut.conj g.1).toMonoidHom := by
      rw [componentConjugateSubgroup,
        Subgroup.map_map, Subgroup.map_map,
        component_subtype_comp_componentConjugationEquiv]
    _ =
        (coherentComponentAmbientIntermediate
          D hdata K).map
            (MulAut.conj g.1).toMonoidHom := by
      rw [map_coherentComponentLocalData_intermediate]
    _ =
        g • coherentComponentAmbientIntermediate
          D hdata K := by
      rw [ambientSubgroup_smul_def]
    _ =
        coherentComponentAmbientIntermediate
          D hdata (g.1 • K) :=
      (coherentComponentAmbientIntermediate_smul
        D hdata g K).symm
    _ =
        (coherentComponentIntermediate
          D hdata (g.1 • K)).map
            (g.1 • K).1.subtype :=
      (map_coherentComponentLocalData_intermediate
        D hdata (g.1 • K)).symm

/-- Full local inductive-McKay data on all component coordinates, chosen
coherently on ambient-normalizer orbits. -/
structure ComponentOrbitLocalData
    (D : LayerSylowCoordinateData G p Q) where
  /-- The full local datum in each component. -/
  data :
    ∀ K : ComponentIndex G,
      LocalInductiveMcKayData (D.coordinate K)
  /-- Exact conjugation-equivariance of the intermediate subgroups under
  the ambient normalizer of the selected layer Sylow subgroup. -/
  intermediate_equivariant :
    ComponentLocalFamily.IsConjugationEquivariantUnder
      G (LayerSylowAmbientNormalizer G Q)
      (fun K ↦ (data K).intermediate)

namespace ComponentOrbitLocalData

variable {D : LayerSylowCoordinateData G p Q}

/-- Construct coherent orbit data from pointwise existence of full local
data. -/
def ofNonempty
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K))) :
    ComponentOrbitLocalData D where
  data := coherentComponentLocalData D hdata
  intermediate_equivariant :=
    coherentComponentIntermediate_equivariant D hdata

/-- Construct coherent component-orbit data from the quasisimple
inductive-McKay hypothesis. -/
def ofQuasisimpleHypothesis
    (h : QuasisimpleInductiveMcKayHypothesis.{0} p) :
    ComponentOrbitLocalData D :=
  ofNonempty
    (fun K ↦
      h K.1 K.2.isQuasisimple (D.coordinate K))

/-- The coherent intermediate subgroup in each component. -/
abbrev intermediate
    (d : ComponentOrbitLocalData D)
    (K : ComponentIndex G) :
    Subgroup K.1 :=
  (d.data K).intermediate

/-- The coherent intermediate family is equivariant under the ambient
normalizer. -/
theorem isConjugationEquivariantUnder
    (d : ComponentOrbitLocalData D) :
    ComponentLocalFamily.IsConjugationEquivariantUnder
      G (LayerSylowAmbientNormalizer G Q)
      d.intermediate :=
  d.intermediate_equivariant

/-- The coordinate Sylow normalizer lies in the coherent intermediate. -/
theorem normalizer_le_intermediate
    (d : ComponentOrbitLocalData D)
    (K : ComponentIndex G) :
    Subgroup.normalizer
        (D.coordinate K : Set K.1) ≤
      d.intermediate K :=
  (d.data K).normalizer_le

/-- The center of each component lies in its coherent intermediate. -/
theorem center_le_intermediate
    (d : ComponentOrbitLocalData D)
    (K : ComponentIndex G) :
    Subgroup.center K.1 ≤
      d.intermediate K :=
  (Subgroup.center_le_normalizer
      (D.coordinate K : Set K.1)).trans
    (d.normalizer_le_intermediate K)

/-- The coordinate Sylow subgroup lies in its coherent intermediate. -/
theorem coordinate_le_intermediate
    (d : ComponentOrbitLocalData D)
    (K : ComponentIndex G) :
    (D.coordinate K : Subgroup K.1) ≤
      d.intermediate K :=
  Subgroup.le_normalizer.trans
    (d.normalizer_le_intermediate K)

/-- A proper coordinate Sylow normalizer forces the corresponding coherent
intermediate to be proper. -/
theorem intermediate_lt_top_of_normalizer_lt_top
    (d : ComponentOrbitLocalData D)
    (K : ComponentIndex G)
    (hK :
      Subgroup.normalizer
        (D.coordinate K : Set K.1) < ⊤) :
    d.intermediate K < ⊤ :=
  (d.data K).proper_of_normalizer_ne_top hK.ne

/-- If `Q` is noncentral in the layer, at least one coherent component
intermediate is proper. -/
theorem exists_intermediate_lt_top
    (d : ComponentOrbitLocalData D)
    (hQnoncentral :
      ¬(Q : Subgroup (layer G)) ≤
        Subgroup.center (layer G)) :
    ∃ K : ComponentIndex G,
      d.intermediate K < ⊤ := by
  obtain ⟨K, _hKcentral, hnormalizer⟩ :=
    D.exists_coordinate_normalizer_lt_top
      hQnoncentral
  exact
    ⟨K,
      d.intermediate_lt_top_of_normalizer_lt_top
        K hnormalizer⟩

/-- Ambient noncentrality supplies a proper coherent coordinate under the
standard center-image hypothesis. -/
theorem exists_intermediate_lt_top_of_map_not_le_center
    (d : ComponentOrbitLocalData D)
    (hcenterImage :
      (Subgroup.center (layer G)).map
          (layer G).subtype ≤
        Subgroup.center G)
    (hQambient :
      ¬(Q : Subgroup (layer G)).map
          (layer G).subtype ≤
        Subgroup.center G) :
    ∃ K : ComponentIndex G,
      d.intermediate K < ⊤ :=
  d.exists_intermediate_lt_top
    (D.not_le_center_layer_of_map_not_le_center
      hcenterImage hQambient)

/-- The componentwise `p'`-character correspondence retained from the full
transported local datum. -/
abbrev correspondence
    (d : ComponentOrbitLocalData D)
    (K : ComponentIndex G) :
    PPrimeIrreducibleCharacter K.1 p ≃
      PPrimeIrreducibleCharacter
        (d.intermediate K) p :=
  (d.data K).correspondence

end ComponentOrbitLocalData

end InductiveMcKay
end McKayConjecture
