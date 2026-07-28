/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerComponentCorrespondenceEquivariance
import McKayConjecture.InductiveMcKay.LayerIntermediateReduction

/-!
# Transport of coherent component correspondences

The orbit construction of `ComponentOrbitLocalData` chooses a full local
datum at one representative of each component orbit and transports it to
all coordinates.  Two selected transporters to conjugate coordinates need
not be equal.  Their quotient fixes the orbit representative, so it induces
an automorphism stabilizing the representative coordinate Sylow subgroup.
Equivariance of the representative local correspondence under this
stabilizer proves the exact cross-component pullback square required by
`LayerComponentLocalData.IsCoordinateCorrespondenceEquivariant`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}
variable {D : LayerSylowCoordinateData G p Q}

/-! ### Comparing selected orbit transporters -/

/-- The quotient of the selected transporter to `a • K` by the composite
of `a` with the selected transporter to `K`. -/
def componentOrbitTransporterDifference
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G) :
    LayerSylowAmbientNormalizer G Q :=
  (OrbitExtension.transporter
      (LayerSylowAmbientNormalizer G Q)
      (ComponentIndex G) (a.1 • K))⁻¹ *
    a *
    OrbitExtension.transporter
      (LayerSylowAmbientNormalizer G Q)
      (ComponentIndex G) K

omit [Finite G] [Fact p.Prime] in
/-- The transporter difference fixes the selected representative of the
orbit of `K`. -/
theorem componentOrbitTransporterDifference_smul_representative
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G) :
    (componentOrbitTransporterDifference
        (G := G) a K).1 •
        layerComponentOrbitRepresentative
          (OrbitExtension.orbitOf
            (LayerSylowAmbientNormalizer G Q)
            (ComponentIndex G) K) =
      layerComponentOrbitRepresentative
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K) := by
  let R : ComponentIndex G :=
    layerComponentOrbitRepresentative
      (OrbitExtension.orbitOf
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) K)
  let u : LayerSylowAmbientNormalizer G Q :=
    OrbitExtension.transporter
      (LayerSylowAmbientNormalizer G Q)
      (ComponentIndex G) K
  let v : LayerSylowAmbientNormalizer G Q :=
    OrbitExtension.transporter
      (LayerSylowAmbientNormalizer G Q)
      (ComponentIndex G) (a.1 • K)
  have hu : u.1 • R = K :=
    layerComponentOrbitTransporter_smul_representative
      (G := G) (Q := Q) K
  have hv :
      v.1 • R = a.1 • K := by
    have hv' :=
      layerComponentOrbitTransporter_smul_representative
        (G := G) (Q := Q) (a.1 • K)
    have hq :
        OrbitExtension.orbitOf
            (LayerSylowAmbientNormalizer G Q)
            (ComponentIndex G) (a.1 • K) =
          OrbitExtension.orbitOf
            (LayerSylowAmbientNormalizer G Q)
            (ComponentIndex G) K :=
      OrbitExtension.orbitOf_smul
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) a K
    rw [hq] at hv'
    simpa only [v, R] using hv'
  change (v⁻¹ * a * u).1 • R = R
  calc
    (v⁻¹ * a * u).1 • R =
        v.1⁻¹ • (a.1 • (u.1 • R)) := by
      simp only [Subgroup.coe_mul,
        Subgroup.coe_inv, mul_smul]
    _ = v.1⁻¹ • (a.1 • K) := by rw [hu]
    _ = v.1⁻¹ • (v.1 • R) := by rw [hv]
    _ = R := inv_smul_smul v.1 R

/-- The transporter difference induces a coordinate-Sylow-stabilizing
automorphism of the representative component. -/
def componentOrbitRepresentativeStabilizer
    (D : LayerSylowCoordinateData G p Q)
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G) :
    SylowAutStabilizer
      (D.coordinate
        (layerComponentOrbitRepresentative
          (OrbitExtension.orbitOf
            (LayerSylowAmbientNormalizer G Q)
            (ComponentIndex G) K))) :=
  ⟨componentOrbitStabilizerAutomorphism
      (G := G)
      (layerComponentOrbitRepresentative
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K))
      (componentOrbitTransporterDifference
        (G := G) a K)
      (componentOrbitTransporterDifference_smul_representative
        (G := G) a K),
    componentOrbitStabilizerAutomorphism_mem
      D
      (layerComponentOrbitRepresentative
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K))
      (componentOrbitTransporterDifference
        (G := G) a K)
      (componentOrbitTransporterDifference_smul_representative
        (G := G) a K)⟩

/-- Reindex the selected representative along the equality of the orbits of
`K` and `a • K`.  On ambient elements this equivalence is the identity. -/
def layerComponentOrbitRepresentativeReindexEquiv
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G) :
    (layerComponentOrbitRepresentative
      (OrbitExtension.orbitOf
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) K)).1 ≃*
      (layerComponentOrbitRepresentative
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) (a.1 • K))).1 :=
  MulEquiv.subgroupCongr
    (congrArg
      (fun q : LayerComponentOrbit (G := G) (Q := Q) ↦
        (layerComponentOrbitRepresentative q).1)
      (OrbitExtension.orbitOf_smul
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) a K).symm)

omit [Finite G] [Fact p.Prime] in
@[simp]
theorem layerComponentOrbitRepresentativeReindexEquiv_apply_coe
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G)
    (x :
      (layerComponentOrbitRepresentative
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)).1) :
    ((layerComponentOrbitRepresentativeReindexEquiv
      (G := G) a K x :
        (layerComponentOrbitRepresentative
          (OrbitExtension.orbitOf
            (LayerSylowAmbientNormalizer G Q)
            (ComponentIndex G) (a.1 • K))).1) : G) =
      (x : G) :=
  rfl

/-- Composition of the selected transport to `K` with conjugation by `a`
equals the representative stabilizer automorphism followed by the selected
transport to `a • K`. -/
theorem layerComponentOrbitTransportEquiv_trans_conjugation
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G) :
    (layerComponentOrbitTransportEquiv
        (G := G) (Q := Q) K).trans
      (componentConjugationEquiv G a.1 K) =
      ((componentOrbitRepresentativeStabilizer
        (G := G) D a K).1).trans
        ((layerComponentOrbitRepresentativeReindexEquiv
          (G := G) a K).trans
          (layerComponentOrbitTransportEquiv
            (G := G) (Q := Q) (a.1 • K))) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  simp only [MulEquiv.trans_apply,
    layerComponentOrbitTransportEquiv_apply_coe,
    componentConjugationEquiv_apply_coe,
    componentOrbitRepresentativeStabilizer,
    componentOrbitStabilizerAutomorphism_apply_coe,
    layerComponentOrbitRepresentativeReindexEquiv_apply_coe,
    componentOrbitTransporterDifference]
  simp [mul_assoc]

/-! ### Representative-to-coordinate intermediate transport -/

/-- A dependent cast of representative intermediates does not change the
underlying ambient element. -/
theorem layerComponentOrbitRepresentativeIntermediateCast_apply_coe_ambient
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    {q r : LayerComponentOrbit (G := G) (Q := Q)}
    (h : q = r)
    (x :
      (layerComponentOrbitRepresentativeData
        D hdata q).intermediate) :
    ((↑(MulEquiv.cast
        (M := fun s : LayerComponentOrbit (G := G) (Q := Q) ↦
          (layerComponentOrbitRepresentativeData
            D hdata s).intermediate)
        h x) :
      (layerComponentOrbitRepresentative r).1) : G) =
      ((↑x : (layerComponentOrbitRepresentative q).1) : G) := by
  cases h
  rfl

/-- Dependent casts of an orbit representative and of its intermediate
commute with the representative local correspondence. -/
theorem layerComponentOrbitRepresentativeData_correspondence_cast
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    {q r : LayerComponentOrbit (G := G) (Q := Q)}
    (h : q = r)
    (χ : PPrimeIrreducibleCharacter
      (layerComponentOrbitRepresentative r).1 p) :
    (layerComponentOrbitRepresentativeData
      D hdata q).correspondence
        (IrreducibleCharacter.pPrimeComapEquiv p
          (MulEquiv.subgroupCongr
            (congrArg
              (fun s : LayerComponentOrbit (G := G) (Q := Q) ↦
                (layerComponentOrbitRepresentative s).1)
              h)) χ) =
      IrreducibleCharacter.pPrimeComapEquiv p
        (MulEquiv.cast
          (M := fun s : LayerComponentOrbit (G := G) (Q := Q) ↦
            (layerComponentOrbitRepresentativeData
              D hdata s).intermediate)
          h)
        ((layerComponentOrbitRepresentativeData
          D hdata r).correspondence χ) := by
  cases h
  rfl

/-- Reindex the representative intermediate along the equality of the
orbits of `K` and `a • K`. -/
def layerComponentOrbitRepresentativeIntermediateReindexEquiv
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G) :
    (layerComponentOrbitRepresentativeData
      D hdata
      (OrbitExtension.orbitOf
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) K)).intermediate ≃*
      (layerComponentOrbitRepresentativeData
        D hdata
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) (a.1 • K))).intermediate :=
  MulEquiv.cast
    (M := fun q : LayerComponentOrbit (G := G) (Q := Q) ↦
      (layerComponentOrbitRepresentativeData D hdata q).intermediate)
    (OrbitExtension.orbitOf_smul
      (LayerSylowAmbientNormalizer G Q)
      (ComponentIndex G) a K).symm

@[simp]
theorem layerComponentOrbitRepresentativeIntermediateReindexEquiv_apply_coe_ambient
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G)
    (x :
      (layerComponentOrbitRepresentativeData
        D hdata
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)).intermediate) :
    ((↑(layerComponentOrbitRepresentativeIntermediateReindexEquiv
        D hdata a K x) :
      (layerComponentOrbitRepresentative
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) (a.1 • K))).1) : G) =
      ((↑x :
        (layerComponentOrbitRepresentative
          (OrbitExtension.orbitOf
            (LayerSylowAmbientNormalizer G Q)
            (ComponentIndex G) K)).1) : G) := by
  exact
    layerComponentOrbitRepresentativeIntermediateCast_apply_coe_ambient
      D hdata
      (OrbitExtension.orbitOf_smul
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) a K).symm
      x

/-- The transporter difference restricts to an automorphism of the
representative intermediate subgroup. -/
def componentOrbitRepresentativeIntermediateStabilizer
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G) :
    MulAut
      (layerComponentOrbitRepresentativeData
        D hdata
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)).intermediate :=
  SylowAutStabilizer.intermediateRestrictionHom
    (D.coordinate
      (layerComponentOrbitRepresentative
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)))
    (layerComponentOrbitRepresentativeData
      D hdata
      (OrbitExtension.orbitOf
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) K)).intermediate
    (layerComponentOrbitRepresentativeData
      D hdata
      (OrbitExtension.orbitOf
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) K)).intermediate_invariant
    (componentOrbitRepresentativeStabilizer
      (G := G) D a K)

@[simp]
theorem componentOrbitRepresentativeIntermediateStabilizer_apply_coe_ambient
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G)
    (x :
      (layerComponentOrbitRepresentativeData
        D hdata
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)).intermediate) :
    ((((componentOrbitRepresentativeIntermediateStabilizer
        D hdata a K) x :
      (layerComponentOrbitRepresentativeData
        D hdata
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)).intermediate) :
      (layerComponentOrbitRepresentative
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)).1) : G) =
      (componentOrbitTransporterDifference (G := G) a K).1 *
        (((x :
          (layerComponentOrbitRepresentativeData
            D hdata
            (OrbitExtension.orbitOf
              (LayerSylowAmbientNormalizer G Q)
              (ComponentIndex G) K)).intermediate) :
          (layerComponentOrbitRepresentative
            (OrbitExtension.orbitOf
              (LayerSylowAmbientNormalizer G Q)
              (ComponentIndex G) K)).1) : G) *
        (componentOrbitTransporterDifference (G := G) a K).1⁻¹ := by
  rfl

/-- Equivariance of the representative correspondence, written as pullback
along the transporter-difference automorphism and its restriction. -/
theorem layerComponentOrbitRepresentativeData_correspondence_comap_stabilizer
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G)
    (χ : PPrimeIrreducibleCharacter
      (layerComponentOrbitRepresentative
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)).1 p) :
    (layerComponentOrbitRepresentativeData
      D hdata
      (OrbitExtension.orbitOf
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) K)).correspondence
        (IrreducibleCharacter.pPrimeComapEquiv p
          (componentOrbitRepresentativeStabilizer
            (G := G) D a K).1 χ) =
      IrreducibleCharacter.pPrimeComapEquiv p
        (componentOrbitRepresentativeIntermediateStabilizer
          D hdata a K)
        ((layerComponentOrbitRepresentativeData
          D hdata
          (OrbitExtension.orbitOf
            (LayerSylowAmbientNormalizer G Q)
            (ComponentIndex G) K)).correspondence χ) := by
  let d :=
    layerComponentOrbitRepresentativeData
      D hdata
      (OrbitExtension.orbitOf
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) K)
  let b :=
    componentOrbitRepresentativeStabilizer
      (G := G) D a K
  letI : MulAction
      (SylowAutStabilizer
        (D.coordinate
          (layerComponentOrbitRepresentative
            (OrbitExtension.orbitOf
              (LayerSylowAmbientNormalizer G Q)
              (ComponentIndex G) K))))
      (PPrimeIrreducibleCharacter d.intermediate p) :=
    d.toEquivariant.intermediateCharacterMulAction
  change d.correspondence (b⁻¹ • χ) =
    b⁻¹ • d.correspondence χ
  exact d.toEquivariant.map_smul b⁻¹ χ

/-- Reindexing the orbit representative commutes with its local
correspondence. -/
theorem layerComponentOrbitRepresentativeData_correspondence_reindex
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G)
    (χ : PPrimeIrreducibleCharacter
      (layerComponentOrbitRepresentative
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) (a.1 • K))).1 p) :
    (layerComponentOrbitRepresentativeData
      D hdata
      (OrbitExtension.orbitOf
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) K)).correspondence
        (IrreducibleCharacter.pPrimeComapEquiv p
          (layerComponentOrbitRepresentativeReindexEquiv
            (G := G) a K) χ) =
      IrreducibleCharacter.pPrimeComapEquiv p
        (layerComponentOrbitRepresentativeIntermediateReindexEquiv
          D hdata a K)
        ((layerComponentOrbitRepresentativeData
          D hdata
          (OrbitExtension.orbitOf
            (LayerSylowAmbientNormalizer G Q)
            (ComponentIndex G) (a.1 • K))).correspondence χ) := by
  exact
    layerComponentOrbitRepresentativeData_correspondence_cast
      D hdata
      (OrbitExtension.orbitOf_smul
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) a K).symm
      χ

/-- The canonical equivalence from the representative intermediate to
the intermediate of the coherently transported datum at `K`. -/
def coherentComponentIntermediateEquiv
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (K : ComponentIndex G) :
    (layerComponentOrbitRepresentativeData
      D hdata
      (OrbitExtension.orbitOf
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) K)).intermediate ≃*
      (coherentComponentLocalData D hdata K).intermediate :=
  (LocalCorrespondence.intermediateEquiv
      (layerComponentOrbitTransportEquiv
        (G := G) (Q := Q) K)
      (layerComponentOrbitRepresentativeData
        D hdata
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)).toLocal).trans
    (MulEquiv.subgroupCongr
      (LocalInductiveMcKayData.cast_intermediate
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
              (ComponentIndex G) K)))).symm)

@[simp]
theorem coherentComponentIntermediateEquiv_apply_coe
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (K : ComponentIndex G)
    (x :
      (layerComponentOrbitRepresentativeData
        D hdata
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)).intermediate) :
    ((coherentComponentIntermediateEquiv
        D hdata K x :
      (coherentComponentLocalData
        D hdata K).intermediate) :
        K.1) =
      layerComponentOrbitTransportEquiv
        (G := G) (Q := Q) K x :=
  rfl

/-- On ambient elements, representative-to-coordinate intermediate
transport is conjugation by the selected orbit transporter. -/
@[simp]
theorem coherentComponentIntermediateEquiv_apply_coe_ambient
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (K : ComponentIndex G)
    (x :
      (layerComponentOrbitRepresentativeData
        D hdata
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K)).intermediate) :
    (((coherentComponentIntermediateEquiv
        D hdata K x :
      (coherentComponentLocalData
        D hdata K).intermediate) :
        K.1) : G) =
      (OrbitExtension.transporter
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K).1 *
        ((x :
          (layerComponentOrbitRepresentativeData
            D hdata
            (OrbitExtension.orbitOf
              (LayerSylowAmbientNormalizer G Q)
              (ComponentIndex G) K)).intermediate) :
          (layerComponentOrbitRepresentative
            (OrbitExtension.orbitOf
              (LayerSylowAmbientNormalizer G Q)
              (ComponentIndex G) K)).1) *
        (OrbitExtension.transporter
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K).1⁻¹ := by
  rw [coherentComponentIntermediateEquiv_apply_coe,
    layerComponentOrbitTransportEquiv_apply_coe]

/-- Pullback along two composable group equivalences is pullback along their
composite. -/
@[simp]
theorem IrreducibleCharacter.pPrimeComapEquiv_trans_apply
    {X Y Z : Type} [Group X] [Group Y] [Group Z]
    (q : ℕ) (e : X ≃* Y) (f : Y ≃* Z)
    (χ : PPrimeIrreducibleCharacter Z q) :
    IrreducibleCharacter.pPrimeComapEquiv q e
        (IrreducibleCharacter.pPrimeComapEquiv q f χ) =
      IrreducibleCharacter.pPrimeComapEquiv q (e.trans f) χ := by
  apply Subtype.ext
  exact IrreducibleCharacter.comap_trans f e χ.1

/-- The canonical representative-to-coordinate intermediate equivalences
intertwine the restricted conjugation map with the transporter-difference
automorphism, the orbit reindexing cast, and the selected transport to the
conjugate coordinate. -/
theorem coherentComponentIntermediateEquiv_trans_relativeConjugation
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G) :
    (coherentComponentIntermediateEquiv D hdata K).trans
        ((ComponentOrbitLocalData.ofNonempty hdata).toLayerComponentLocalData
          |>.relativeIntermediateConjugationEquiv
            (ComponentOrbitLocalData.ofNonempty hdata
              |>.isConjugationEquivariantUnder)
            a K) =
      (componentOrbitRepresentativeIntermediateStabilizer
        D hdata a K).trans
        ((layerComponentOrbitRepresentativeIntermediateReindexEquiv
          D hdata a K).trans
          (coherentComponentIntermediateEquiv
            D hdata (a.1 • K))) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change
    (a : G) *
        (((coherentComponentIntermediateEquiv
          D hdata K x :
        (coherentComponentLocalData
          D hdata K).intermediate) : K.1) : G) *
        (a : G)⁻¹ =
      (((coherentComponentIntermediateEquiv
        D hdata (a.1 • K)
        (layerComponentOrbitRepresentativeIntermediateReindexEquiv
          D hdata a K
          (componentOrbitRepresentativeIntermediateStabilizer
            D hdata a K x)) :
        (coherentComponentLocalData
          D hdata (a.1 • K)).intermediate) :
        (a.1 • K).1) : G)
  rw [coherentComponentIntermediateEquiv_apply_coe_ambient,
    coherentComponentIntermediateEquiv_apply_coe_ambient,
    layerComponentOrbitRepresentativeIntermediateReindexEquiv_apply_coe_ambient,
    componentOrbitRepresentativeIntermediateStabilizer_apply_coe_ambient]
  simp [componentOrbitTransporterDifference, mul_assoc]

/-- Pullback-oriented form of the intermediate transport square. -/
theorem coherentComponentIntermediatePullbackEquiv
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (a : LayerSylowAmbientNormalizer G Q)
    (K : ComponentIndex G) :
    (coherentComponentIntermediateEquiv D hdata K).symm.trans
        ((componentOrbitRepresentativeIntermediateStabilizer
          D hdata a K).trans
          (layerComponentOrbitRepresentativeIntermediateReindexEquiv
            D hdata a K)) =
      ((ComponentOrbitLocalData.ofNonempty hdata).toLayerComponentLocalData
        |>.relativeIntermediateConjugationEquiv
          (ComponentOrbitLocalData.ofNonempty hdata
            |>.isConjugationEquivariantUnder)
          a K).trans
        (coherentComponentIntermediateEquiv
          D hdata (a.1 • K)).symm := by
  let jK := coherentComponentIntermediateEquiv D hdata K
  let jL :=
    coherentComponentIntermediateEquiv D hdata (a.1 • K)
  let α :=
    componentOrbitRepresentativeIntermediateStabilizer
      D hdata a K
  let r :=
    layerComponentOrbitRepresentativeIntermediateReindexEquiv
      D hdata a K
  let c :=
    (ComponentOrbitLocalData.ofNonempty hdata).toLayerComponentLocalData
      |>.relativeIntermediateConjugationEquiv
        (ComponentOrbitLocalData.ofNonempty hdata
          |>.isConjugationEquivariantUnder)
        a K
  have htransport : jK.trans c = α.trans (r.trans jL) :=
    coherentComponentIntermediateEquiv_trans_relativeConjugation
      D hdata a K
  apply MulEquiv.ext
  intro x
  have hx :=
    DFunLike.congr_fun htransport (jK.symm x)
  change
    c (jK (jK.symm x)) =
      jL (r (α (jK.symm x))) at hx
  rw [jK.apply_symm_apply] at hx
  have hx' := congrArg jL.symm hx
  rw [jL.symm_apply_apply] at hx'
  exact hx'.symm

omit [Fact p.Prime] in
/-- Casting the Sylow index of full local data transports the target
character along the induced equality of intermediate subgroups. -/
theorem LocalInductiveMcKayData.cast_correspondence_apply
    {X : Type} [Group X] [Finite X]
    {P R : Sylow p X}
    (h : P = R)
    (d : LocalInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter X p) :
    (LocalInductiveMcKayData.cast h d).correspondence χ =
      IrreducibleCharacter.pPrimeComapEquiv p
        (MulEquiv.subgroupCongr
          (LocalInductiveMcKayData.cast_intermediate h d))
        (d.correspondence χ) := by
  cases h
  rfl

omit [Fact p.Prime] in
/-- Pointwise form of correspondence transport for full local data. -/
@[simp]
theorem LocalInductiveMcKayData.transport_correspondence_apply
    {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    {P : Sylow p X}
    (e : X ≃* Y)
    (d : LocalInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter Y p) :
    (LocalInductiveMcKayData.transport e P d).correspondence χ =
      IrreducibleCharacter.pPrimeComapEquiv p
        (LocalCorrespondence.intermediateEquiv
          e d.toLocal).symm
        (d.correspondence
          (IrreducibleCharacter.pPrimeComapEquiv p e χ)) :=
  rfl

omit [Fact p.Prime] in
/-- A cast following transport has the canonical representative-to-target
correspondence formula. -/
theorem LocalInductiveMcKayData.cast_transport_correspondence_apply
    {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    {P : Sylow p X} {R : Sylow p Y}
    (e : X ≃* Y)
    (h : McKayConjecture.Sylow.transport e P = R)
    (d : LocalInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter Y p) :
    (LocalInductiveMcKayData.cast h
      (LocalInductiveMcKayData.transport e P d)).correspondence χ =
      IrreducibleCharacter.pPrimeComapEquiv p
        ((LocalCorrespondence.intermediateEquiv
          e d.toLocal).trans
          (MulEquiv.subgroupCongr
            (LocalInductiveMcKayData.cast_intermediate h
              (LocalInductiveMcKayData.transport e P d)).symm)).symm
        (d.correspondence
          (IrreducibleCharacter.pPrimeComapEquiv p e χ)) := by
  rw [LocalInductiveMcKayData.cast_correspondence_apply,
    LocalInductiveMcKayData.transport_correspondence_apply]
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  rfl

/-- The correspondence in a coherently transported coordinate is obtained
by pulling to the representative, applying its correspondence, and pulling
the result forward to the coordinate intermediate. -/
theorem coherentComponentLocalData_correspondence_apply
    (D : LayerSylowCoordinateData G p Q)
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K)))
    (K : ComponentIndex G)
    (χ : PPrimeIrreducibleCharacter K.1 p) :
    (coherentComponentLocalData D hdata K).correspondence χ =
      IrreducibleCharacter.pPrimeComapEquiv p
        (coherentComponentIntermediateEquiv D hdata K).symm
        ((layerComponentOrbitRepresentativeData
          D hdata
          (OrbitExtension.orbitOf
            (LayerSylowAmbientNormalizer G Q)
            (ComponentIndex G) K)).correspondence
          (IrreducibleCharacter.pPrimeComapEquiv p
            (layerComponentOrbitTransportEquiv
              (G := G) (Q := Q) K) χ)) := by
  exact
    LocalInductiveMcKayData.cast_transport_correspondence_apply
      (e := layerComponentOrbitTransportEquiv
        (G := G) (Q := Q) K)
      (h := layerComponentOrbitTransport_coordinate D K)
      (d := layerComponentOrbitRepresentativeData
        D hdata
        (OrbitExtension.orbitOf
          (LayerSylowAmbientNormalizer G Q)
          (ComponentIndex G) K))
      χ

/-! ### Exact cross-component correspondence law -/

/-- The orbit-coherent local data constructed from pointwise existence
satisfies the exact coordinate correspondence law required for the layer
assembly. -/
theorem ComponentOrbitLocalData.ofNonempty_isCoordinateCorrespondenceEquivariant
    (hdata : ∀ K : ComponentIndex G,
      Nonempty
        (LocalInductiveMcKayData (D.coordinate K))) :
    (ComponentOrbitLocalData.ofNonempty hdata).toLayerComponentLocalData
      |>.IsCoordinateCorrespondenceEquivariant
        (ComponentOrbitLocalData.ofNonempty hdata
          |>.isConjugationEquivariantUnder) := by
  intro a K χ
  change
    (coherentComponentLocalData D hdata K).correspondence
        (IrreducibleCharacter.pPrimeComapEquiv p
          (componentConjugationEquiv G a.1 K) χ) =
      IrreducibleCharacter.pPrimeComapEquiv p
        ((ComponentOrbitLocalData.ofNonempty hdata).toLayerComponentLocalData
          |>.relativeIntermediateConjugationEquiv
            (ComponentOrbitLocalData.ofNonempty hdata
              |>.isConjugationEquivariantUnder)
            a K)
        ((coherentComponentLocalData
          D hdata (a.1 • K)).correspondence χ)
  rw [coherentComponentLocalData_correspondence_apply,
    coherentComponentLocalData_correspondence_apply]
  let dK :=
    layerComponentOrbitRepresentativeData
      D hdata
      (OrbitExtension.orbitOf
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) K)
  let dL :=
    layerComponentOrbitRepresentativeData
      D hdata
      (OrbitExtension.orbitOf
        (LayerSylowAmbientNormalizer G Q)
        (ComponentIndex G) (a.1 • K))
  let eK :=
    layerComponentOrbitTransportEquiv
      (G := G) (Q := Q) K
  let eL :=
    layerComponentOrbitTransportEquiv
      (G := G) (Q := Q) (a.1 • K)
  let c := componentConjugationEquiv G a.1 K
  let b :=
    componentOrbitRepresentativeStabilizer
      (G := G) D a K
  let r :=
    layerComponentOrbitRepresentativeReindexEquiv
      (G := G) a K
  let α :=
    componentOrbitRepresentativeIntermediateStabilizer
      D hdata a K
  let rM :=
    layerComponentOrbitRepresentativeIntermediateReindexEquiv
      D hdata a K
  let jK :=
    coherentComponentIntermediateEquiv D hdata K
  let jL :=
    coherentComponentIntermediateEquiv D hdata (a.1 • K)
  let rel :
      (coherentComponentLocalData D hdata K).intermediate ≃*
        (coherentComponentLocalData
          D hdata (a.1 • K)).intermediate :=
    (ComponentOrbitLocalData.ofNonempty hdata).toLayerComponentLocalData
      |>.relativeIntermediateConjugationEquiv
        (ComponentOrbitLocalData.ofNonempty hdata
          |>.isConjugationEquivariantUnder)
        a K
  let η :=
    IrreducibleCharacter.pPrimeComapEquiv p eL χ
  let ζ :=
    IrreducibleCharacter.pPrimeComapEquiv p r η
  let ψ := dL.correspondence η
  change
    IrreducibleCharacter.pPrimeComapEquiv p jK.symm
        (dK.correspondence
          (IrreducibleCharacter.pPrimeComapEquiv p eK
            (IrreducibleCharacter.pPrimeComapEquiv p c χ))) =
      IrreducibleCharacter.pPrimeComapEquiv p rel
        (IrreducibleCharacter.pPrimeComapEquiv p jL.symm ψ)
  have hsourceEquiv :
      eK.trans c = b.1.trans (r.trans eL) :=
    layerComponentOrbitTransportEquiv_trans_conjugation
      (D := D) a K
  have hsourceCharacter :
      IrreducibleCharacter.pPrimeComapEquiv p eK
          (IrreducibleCharacter.pPrimeComapEquiv p c χ) =
        IrreducibleCharacter.pPrimeComapEquiv p b.1 ζ := by
    calc
      IrreducibleCharacter.pPrimeComapEquiv p eK
          (IrreducibleCharacter.pPrimeComapEquiv p c χ) =
          IrreducibleCharacter.pPrimeComapEquiv p
            (eK.trans c) χ :=
        IrreducibleCharacter.pPrimeComapEquiv_trans_apply
          p eK c χ
      _ =
          IrreducibleCharacter.pPrimeComapEquiv p
            (b.1.trans (r.trans eL)) χ :=
        congrArg
          (fun f ↦
            IrreducibleCharacter.pPrimeComapEquiv p f χ)
          hsourceEquiv
      _ =
          IrreducibleCharacter.pPrimeComapEquiv p b.1
            (IrreducibleCharacter.pPrimeComapEquiv p
              (r.trans eL) χ) :=
        (IrreducibleCharacter.pPrimeComapEquiv_trans_apply
          p b.1 (r.trans eL) χ).symm
      _ =
          IrreducibleCharacter.pPrimeComapEquiv p b.1
            (IrreducibleCharacter.pPrimeComapEquiv p r
              (IrreducibleCharacter.pPrimeComapEquiv p eL χ)) := by
        exact congrArg
          (IrreducibleCharacter.pPrimeComapEquiv p b.1)
          (IrreducibleCharacter.pPrimeComapEquiv_trans_apply
            p r eL χ).symm
      _ =
          IrreducibleCharacter.pPrimeComapEquiv p b.1 ζ :=
        rfl
  have hstabilizer :
      dK.correspondence
          (IrreducibleCharacter.pPrimeComapEquiv p b.1 ζ) =
        IrreducibleCharacter.pPrimeComapEquiv p α
          (dK.correspondence ζ) :=
    layerComponentOrbitRepresentativeData_correspondence_comap_stabilizer
      D hdata a K ζ
  have hreindex :
      dK.correspondence ζ =
        IrreducibleCharacter.pPrimeComapEquiv p rM ψ :=
    layerComponentOrbitRepresentativeData_correspondence_reindex
      D hdata a K η
  have htargetEquiv :
      jK.symm.trans (α.trans rM) =
        rel.trans jL.symm :=
    coherentComponentIntermediatePullbackEquiv
      D hdata a K
  have htargetCharacter :
      IrreducibleCharacter.pPrimeComapEquiv p
          (jK.symm.trans (α.trans rM)) ψ =
        IrreducibleCharacter.pPrimeComapEquiv p
          (rel.trans jL.symm) ψ :=
    congrArg
      (fun f ↦
        IrreducibleCharacter.pPrimeComapEquiv p f ψ)
      htargetEquiv
  calc
    IrreducibleCharacter.pPrimeComapEquiv p jK.symm
        (dK.correspondence
          (IrreducibleCharacter.pPrimeComapEquiv p eK
            (IrreducibleCharacter.pPrimeComapEquiv p c χ))) =
        IrreducibleCharacter.pPrimeComapEquiv p jK.symm
          (dK.correspondence
            (IrreducibleCharacter.pPrimeComapEquiv p b.1 ζ)) :=
      congrArg
        (fun θ ↦
          IrreducibleCharacter.pPrimeComapEquiv p jK.symm
            (dK.correspondence θ))
        hsourceCharacter
    _ =
        IrreducibleCharacter.pPrimeComapEquiv p jK.symm
          (IrreducibleCharacter.pPrimeComapEquiv p α
            (dK.correspondence ζ)) :=
      congrArg
        (IrreducibleCharacter.pPrimeComapEquiv p jK.symm)
        hstabilizer
    _ =
        IrreducibleCharacter.pPrimeComapEquiv p jK.symm
          (IrreducibleCharacter.pPrimeComapEquiv p α
            (IrreducibleCharacter.pPrimeComapEquiv p rM ψ)) :=
      congrArg
        (fun θ ↦
          IrreducibleCharacter.pPrimeComapEquiv p jK.symm
            (IrreducibleCharacter.pPrimeComapEquiv p α θ))
        hreindex
    _ =
        IrreducibleCharacter.pPrimeComapEquiv p jK.symm
          (IrreducibleCharacter.pPrimeComapEquiv p
            (α.trans rM) ψ) := by
      exact congrArg
        (IrreducibleCharacter.pPrimeComapEquiv p jK.symm)
        (IrreducibleCharacter.pPrimeComapEquiv_trans_apply
          p α rM ψ)
    _ =
        IrreducibleCharacter.pPrimeComapEquiv p
          (jK.symm.trans (α.trans rM)) ψ :=
      IrreducibleCharacter.pPrimeComapEquiv_trans_apply
        p jK.symm (α.trans rM) ψ
    _ =
        IrreducibleCharacter.pPrimeComapEquiv p rel
          (IrreducibleCharacter.pPrimeComapEquiv p jL.symm ψ) :=
      htargetCharacter.trans
        (IrreducibleCharacter.pPrimeComapEquiv_trans_apply
          p rel jL.symm ψ).symm

/-- The orbit-coherent local data supplied by the quasisimple
inductive-McKay hypothesis satisfies the exact coordinate correspondence
law. -/
theorem ComponentOrbitLocalData.ofQuasisimpleHypothesis_isCoordinateCorrespondenceEquivariant
    (h : QuasisimpleInductiveMcKayHypothesis.{0} p) :
    (ComponentOrbitLocalData.ofQuasisimpleHypothesis
      (D := D) h).toLayerComponentLocalData
      |>.IsCoordinateCorrespondenceEquivariant
        (ComponentOrbitLocalData.ofQuasisimpleHypothesis
          (D := D) h
          |>.isConjugationEquivariantUnder) := by
  simpa only [ComponentOrbitLocalData.ofQuasisimpleHypothesis] using
    (ComponentOrbitLocalData.ofNonempty_isCoordinateCorrespondenceEquivariant
      (D := D)
      (fun K ↦
        h K.1 K.2.isQuasisimple (D.coordinate K)))

end InductiveMcKay
end McKayConjecture
