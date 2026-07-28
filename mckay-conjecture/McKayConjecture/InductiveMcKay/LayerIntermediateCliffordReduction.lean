/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerIntermediateAction
import McKayConjecture.InductiveMcKay.LayerIntermediateCorrespondence
import McKayConjecture.InductiveMcKay.MatchedCentralTripleCliffordAssembly

/-!
# Clifford reduction through the layer intermediate

Fix a Sylow subgroup `P` of `G`, use the canonical layer Sylow subgroup
`Q = P ∩ E(G)`, and choose coherent component-orbit local data `d`.
The componentwise correspondence already gives

`Irr_{p'}(E(G)) ≃ Irr_{p'}(C_d)`,

where `C_d` is the component-local normal subgroup internal to the layer
intermediate `H_d`.

Two substantive layer assertions are still required:

* the displayed correspondence is equivariant for the full `H_d`-action;
* every exactly matched pair of inertia triples carries a complete central
  witness.

`LayerIntermediateCliffordReductionData` records exactly these assertions.
All remaining steps are formal: the layer and `H_d` generate `G`, matched
central-triple Clifford assembly gives `Irr_{p'}(G) ≃ Irr_{p'}(H_d)`, and
the minimal-counterexample structure supplies the containment and properness
needed to package this equivalence as a `LocalCorrespondence`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open CliffordPartition
open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {P : Sylow p G}
variable
  {D :
    LayerSylowCoordinateData G p
      (layerSylowIntersection P)}

noncomputable local instance layerIntermediateCliffordReductionFintypeG :
    Fintype G :=
  Fintype.ofFinite G

noncomputable local instance
    layerIntermediateCliffordReductionFintypeIntermediate
    (d : ComponentOrbitLocalData D) :
    Fintype d.ambientIntermediate :=
  Fintype.ofFinite d.ambientIntermediate

/-- The two genuine character-theoretic hypotheses in the layer-intermediate
reduction.

The first field uses ordinary conjugation actions of the full layer
intermediate, not merely its layer-Sylow normalizer.  The second field is
indexed by the exact matched character, so no witness at an independently
chosen orbit representative is requested. -/
structure LayerIntermediateCliffordReductionData
    (d : ComponentOrbitLocalData D) where
  /-- Full layer-intermediate equivariance of the component-local character
  correspondence. -/
  characterEquiv_smul :
    ∀ (h : d.ambientIntermediate)
      (θ : PPrimeIrreducibleCharacter (layer G) p),
      d.intermediateComponentLocalPPrimeCharacterEquiv (h • θ) =
        h • d.intermediateComponentLocalPPrimeCharacterEquiv θ
  /-- Complete central witnesses for every exactly matched layer character. -/
  centralWitness :
    ∀ θ : PPrimeIrreducibleCharacter (layer G) p,
      CompleteCentralIsomorphismWitness
        (ofInertia (layer G) θ.1)
        (ofInertia d.intermediateComponentLocal
          (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1)

namespace LayerIntermediateCliffordReductionData

variable {d : ComponentOrbitLocalData D}

/-- Convert the two explicit layer hypotheses into the exact matched
central-triple Clifford assembly input.  The generation hypothesis is the
already-proved layer Frattini equality. -/
def toMatchedCentralTripleCliffordAssemblyData
    (r : LayerIntermediateCliffordReductionData d) :
    MatchedCentralTripleCliffordAssemblyData
      (layer G) d.ambientIntermediate
        d.intermediateComponentLocal p where
  sup_eq_top := d.layer_sup_ambientIntermediate_eq_top
  characterEquiv :=
    d.intermediateComponentLocalPPrimeCharacterEquiv
  characterEquiv_smul := r.characterEquiv_smul
  centralWitness := r.centralWitness

@[simp]
theorem toMatchedCentralTripleCliffordAssemblyData_characterEquiv
    (r : LayerIntermediateCliffordReductionData d) :
    r.toMatchedCentralTripleCliffordAssemblyData.characterEquiv =
      d.intermediateComponentLocalPPrimeCharacterEquiv :=
  rfl

@[simp]
theorem toMatchedCentralTripleCliffordAssemblyData_sup_eq_top
    (r : LayerIntermediateCliffordReductionData d) :
    r.toMatchedCentralTripleCliffordAssemblyData.sup_eq_top =
      d.layer_sup_ambientIntermediate_eq_top :=
  rfl

/-- The global prime-to-`p` character equivalence obtained by Clifford
assembly through the layer intermediate. -/
def assembledPPrimeEquiv
    (r : LayerIntermediateCliffordReductionData d) :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter d.ambientIntermediate p :=
  r.toMatchedCentralTripleCliffordAssemblyData.assembledPPrimeEquiv

/-- The assembled equivalence has the active-orbit law induced by the
component-local layer correspondence. -/
@[simp]
theorem activeOrbitIndex_assembledPPrimeEquiv
    (r : LayerIntermediateCliffordReductionData d)
    (χ : PPrimeIrreducibleCharacter G p) :
    activeOrbitIndex d.intermediateComponentLocal
        (r.assembledPPrimeEquiv χ) =
      r.toMatchedCentralTripleCliffordAssemblyData.activeOrbitEquiv
        (activeOrbitIndex (layer G) χ) :=
  r.toMatchedCentralTripleCliffordAssemblyData
    |>.activeOrbitIndex_assembledPPrimeEquiv χ

/-- Expanded active-orbit law, identifying the target orbit with the image
of the chosen source representative. -/
@[simp]
theorem activeOrbitIndex_assembledPPrimeEquiv_coe
    (r : LayerIntermediateCliffordReductionData d)
    (χ : PPrimeIrreducibleCharacter G p) :
    (activeOrbitIndex d.intermediateComponentLocal
      (r.assembledPPrimeEquiv χ)).1 =
        (Quotient.mk''
          (d.intermediateComponentLocalPPrimeCharacterEquiv
            ((activeOrbitIndex (layer G) χ).pPrimeOut
              (layer G))).1 :
            OrbitSpace d.intermediateComponentLocal) :=
  r.toMatchedCentralTripleCliffordAssemblyData
    |>.activeOrbitIndex_assembledPPrimeEquiv_coe χ

/-- In a minimal counterexample, the layer-intermediate correspondence is
an exact local correspondence at `P`.

Normalizer containment is unconditional for the canonical intersection;
minimal-counterexample structure supplies properness of the layer
intermediate. -/
def toLocalCorrespondence
    (r : LayerIntermediateCliffordReductionData d)
    (h : MinimalCounterexampleStructure P) :
    LocalCorrespondence P where
  intermediate := d.ambientIntermediate
  normalizer_le := d.sylowNormalizer_le_ambientIntermediate
  proper_of_normalizer_ne_top := fun _ ↦
    d.ambientIntermediate_lt_top_of_minimalCounterexample h
  correspondence := r.assembledPPrimeEquiv

@[simp]
theorem toLocalCorrespondence_intermediate
    (r : LayerIntermediateCliffordReductionData d)
    (h : MinimalCounterexampleStructure P) :
    (r.toLocalCorrespondence h).intermediate =
      d.ambientIntermediate :=
  rfl

@[simp]
theorem toLocalCorrespondence_correspondence_apply
    (r : LayerIntermediateCliffordReductionData d)
    (h : MinimalCounterexampleStructure P)
    (χ : PPrimeIrreducibleCharacter G p) :
    (r.toLocalCorrespondence h).correspondence χ =
      r.assembledPPrimeEquiv χ :=
  rfl

end LayerIntermediateCliffordReductionData

end InductiveMcKay
end McKayConjecture
