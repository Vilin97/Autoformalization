/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordInductionCentralScalar
import McKayConjecture.CharacterTriple.InertiaCentralCharacterScalar
import McKayConjecture.InductiveMcKay.MatchedCentralTripleCliffordAssembly
import McKayConjecture.InductiveMcKay.MatchedInertiaRestriction

/-!
# Central scalars in matched central-triple Clifford assembly

A central character-triple witness used in a Clifford assembly must use the
canonical inclusion of the matched target inertia group into the source
inertia group in order to compare values at the same ambient central
element.  Under exactly that coherence condition, the central-triple
correspondence and the two Clifford-induction steps preserve normalized
central values.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open CliffordCorrespondence
open CliffordEquivalence
open CliffordPartition

variable {G : Type} [Group G] [Finite G]
variable (N H : Subgroup G) [N.Normal]
variable (M : Subgroup H) [M.Normal]

noncomputable local instance
    matchedCentralTripleCentralScalarAssemblyFintypeG :
    Fintype G :=
  Fintype.ofFinite G

noncomputable local instance
    matchedCentralTripleCentralScalarAssemblyFintypeH :
    Fintype H :=
  Fintype.ofFinite H

namespace IrreducibleCharacter

/-- Every ambient-central element belongs to the inertia group of every
character of a normal subgroup. -/
theorem mem_inertia_of_mem_center
    {A : Type} [Group A]
    (K : Subgroup A) [K.Normal]
    (η : IrreducibleCharacter K)
    (z : A) (hz : z ∈ Subgroup.center A) :
    z ∈ IrreducibleCharacter.inertia K η := by
  rw [IrreducibleCharacter.mem_inertia_iff]
  apply IrreducibleCharacter.ext
  funext k
  rw [IrreducibleCharacter.conjBy_values]
  apply congrArg η.values
  apply Subtype.ext
  simp only [MulAut.conjNormal_symm_apply]
  calc
    z⁻¹ * (k : A) * z =
        z⁻¹ * ((k : A) * z) := by rw [mul_assoc]
    _ = z⁻¹ * (z * (k : A)) := by
      rw [(Subgroup.mem_center_iff.mp hz (k : A)).symm]
    _ = (k : A) := by simp

end IrreducibleCharacter

namespace MatchedCentralTripleCliffordAssemblyData

variable {N H M}
variable {p : ℕ} [Fact p.Prime]

/-- Coherence needed for central-scalar preservation: each stored central
witness uses the canonical target-to-source inertia embedding determined by
the matched character equivalence. -/
def UsesCanonicalInertiaEmbeddings
    (d : MatchedCentralTripleCliffordAssemblyData N H M p) : Prop :=
  ∀ θ : PPrimeIrreducibleCharacter N p,
    by
      let C := d.centralWitness θ
      letI := C.leftAddCommGroup
      letI := C.leftModule
      letI := C.leftModuleFinite
      letI := C.leftNontrivial
      letI := C.rightAddCommGroup
      letI := C.rightModule
      letI := C.rightModuleFinite
      letI := C.rightNontrivial
      exact
        C.witness.embedding =
          d.inertiaEmbedding θ

/-- The assembled matched central-triple Clifford correspondence preserves
the normalized value of every ambient-central element contained in the
target subgroup. -/
theorem assembledPPrimeEquiv_central_cross
    (d : MatchedCentralTripleCliffordAssemblyData N H M p)
    (hcanonical : d.UsesCanonicalInertiaEmbeddings)
    (χ : PPrimeIrreducibleCharacter G p)
    (z : G)
    (hzcentral : z ∈ Subgroup.center G)
    (hzH : z ∈ H) :
    χ.1.values z *
        ((d.assembledPPrimeEquiv χ).1.degree : ℂ) =
      (d.assembledPPrimeEquiv χ).1.values ⟨z, hzH⟩ *
        (χ.1.degree : ℂ) := by
  let q := activeOrbitIndex N χ
  let θ := q.pPrimeOut N
  let φ := d.characterEquiv θ
  let sourceBlock :=
    (pPrimeActiveOrbitBlockSigmaEquiv N p χ).2
  let α :=
    (activeOrbitCliffordEquiv
      N (Fact.out : p.Prime) q).symm sourceBlock
  let C := d.centralWitness θ
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  let β :=
    C.witness.pPrimeInertiaEquiv
      N θ.1 M φ.1 (Fact.out : p.Prime)
        θ.2 φ.2 α
  let zH : H := ⟨z, hzH⟩
  have hzSource :
      z ∈ IrreducibleCharacter.inertia N θ.1 :=
    IrreducibleCharacter.mem_inertia_of_mem_center
      N θ.1 z hzcentral
  let zSource :
      IrreducibleCharacter.inertia N θ.1 :=
    ⟨z, hzSource⟩
  have hzTarget :
      zH ∈ IrreducibleCharacter.inertia M φ.1 :=
    MatchedInertiaRestriction.mem_target_inertia_of_mem_source_inertia
      N H M d.characterEquiv d.characterEquiv_smul
        θ zH hzSource
  let zTarget :
      IrreducibleCharacter.inertia M φ.1 :=
    ⟨zH, hzTarget⟩
  have hzHcentral :
      zH ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hzcentral (h : G)
  have hcanonicalθ :
      C.witness.embedding = d.inertiaEmbedding θ :=
    hcanonical θ
  have hembedding :
      C.witness.embedding zTarget = zSource := by
    rw [hcanonicalθ]
    apply Subtype.ext
    rfl
  have hzCentralizer :
      C.witness.embedding zTarget ∈
        Subgroup.centralizer
          ((ofInertia N θ.1).normalSubgroup :
            Set (IrreducibleCharacter.inertia N θ.1)) := by
    rw [hembedding, Subgroup.mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hzcentral (x : G)
  have hsourceBlock :
      activeOrbitCliffordEquiv
          N (Fact.out : p.Prime) q α =
        sourceBlock :=
    (activeOrbitCliffordEquiv
      N (Fact.out : p.Prime) q).apply_symm_apply sourceBlock
  have hsourceCharacter :
      (induceOverInertiaOrbit N θ.1 α.1).1 = χ.1 := by
    exact congrArg
      (fun x : PPrimeOrbitBlock N p q.1 ↦ x.1.1)
      hsourceBlock
  have htargetCharacter :
      (d.assembledPPrimeEquiv χ).1 =
        (induceOverInertiaOrbit M φ.1 β.1).1 := by
    have hdecompose :=
      d.toActivePPrimeOrbitwiseCorrespondence
        |>.decompose_assemble χ
    have hassembledBlock :=
      congrArg
        (fun x :
          Σ r : ActiveOrbit M p,
            PPrimeOrbitBlock M p r.1 ↦
          x.2.1.1)
        hdecompose
    have hblockInduced :
        (d.blockEquiv q sourceBlock).1.1 =
          (induceOverInertiaOrbit M φ.1 β.1).1 := by
      rfl
    exact hassembledBlock.trans hblockInduced
  have hsource :=
    induceOverInertiaOrbit_central_cross
      N θ.1 α.1 zSource hzcentral
  have hmiddle :=
    C.witness.pPrimeInertiaEquiv_matchedCentral_cross
      N M θ.1 φ.1 (Fact.out : p.Prime)
        θ.2 φ.2 α zTarget hzCentralizer
  have htarget :=
    induceOverInertiaOrbit_central_cross
      M φ.1 β.1 zTarget hzHcentral
  rw [hsourceCharacter] at hsource
  rw [← htargetCharacter] at htarget
  rw [hembedding] at hmiddle
  apply mul_right_cancel₀
    (mul_ne_zero
      (Nat.cast_ne_zero.mpr α.1.1.degree_ne_zero)
      (Nat.cast_ne_zero.mpr β.1.1.degree_ne_zero))
  calc
    (χ.1.values z *
          ((d.assembledPPrimeEquiv χ).1.degree : ℂ)) *
        ((α.1.1.degree : ℂ) * (β.1.1.degree : ℂ)) =
      ((χ.1.values z * (α.1.1.degree : ℂ)) *
          (β.1.1.degree : ℂ)) *
        ((d.assembledPPrimeEquiv χ).1.degree : ℂ) := by ring
    _ =
      ((α.1.1.values zSource * (χ.1.degree : ℂ)) *
          (β.1.1.degree : ℂ)) *
        ((d.assembledPPrimeEquiv χ).1.degree : ℂ) := by rw [hsource]
    _ =
      ((α.1.1.values zSource * (β.1.1.degree : ℂ)) *
          (χ.1.degree : ℂ)) *
        ((d.assembledPPrimeEquiv χ).1.degree : ℂ) := by ring
    _ =
      ((β.1.1.values zTarget * (α.1.1.degree : ℂ)) *
          (χ.1.degree : ℂ)) *
        ((d.assembledPPrimeEquiv χ).1.degree : ℂ) := by rw [hmiddle]
    _ =
      ((β.1.1.values zTarget *
          ((d.assembledPPrimeEquiv χ).1.degree : ℂ)) *
          (α.1.1.degree : ℂ)) *
        (χ.1.degree : ℂ) := by ring
    _ =
      (((d.assembledPPrimeEquiv χ).1.values zH *
          (β.1.1.degree : ℂ)) *
          (α.1.1.degree : ℂ)) *
        (χ.1.degree : ℂ) := by rw [← htarget]
    _ =
      ((d.assembledPPrimeEquiv χ).1.values zH *
          (χ.1.degree : ℂ)) *
        ((α.1.1.degree : ℂ) * (β.1.1.degree : ℂ)) := by ring

end MatchedCentralTripleCliffordAssemblyData
end InductiveMcKay
end McKayConjecture
