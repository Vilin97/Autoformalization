/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InertiaFibreTransport
import McKayConjecture.Character.ActiveOrbitSylowFusion
import McKayConjecture.InductiveMcKay.AdaptedCliffordFibreAssembly
import McKayConjecture.InductiveMcKay.NormalSubgroupIntermediateRepresentatives

/-!
# Active-orbit assembly in Rossi's normalizer intermediate

Let `J = N Z(G)` and `H = J N_G(P)`.  This file turns a family of
prime-to-`p` inertia-fibre equivalences at every `P`-fixed character of `J`
into the active-orbit and global character equivalences required by Rossi's
Proposition 4.2.

The only orbit-theoretic input is the usual Sylow fusion-control statement:
two `P`-fixed characters in the same `G`-orbit have images in the same
`H`-orbit.  Keeping this implication explicit makes the separation between
the central-extension character argument and the Sylow conjugacy argument
transparent.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupIntermediateOrbitAssembly

open CliffordCorrespondence
open CliffordEquivalence
open CliffordPartition
open NormalSubgroupIntermediateInertia
open NormalSubgroupIntermediateRepresentatives

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G)
variable (N : Subgroup G) [N.Normal]

noncomputable local instance normalSubgroupIntermediateOrbitAssemblyFintypeG :
    Fintype G :=
  Fintype.ofFinite G

noncomputable local instance normalSubgroupIntermediateOrbitAssemblyFintypeH :
    Fintype (intermediate P N) :=
  Fintype.ofFinite (intermediate P N)

/-- The character-theoretic input at every `P`-fixed representative:
an equivalence between the source inertia fibre and the fibre over the
identity-transported character in `J N_G(P)`. -/
structure InertiaFibreData where
  fibreEquiv :
    ∀ (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
      (hP : (P : Subgroup G) ≤ sourceInertia N θ),
      PPrimeIrreducibleCharactersOverInertia
          (joinCenter N) θ.1 p ≃
        PPrimeIrreducibleCharactersOverInertia
          (internalJoinCenter P N)
          (internalCharacterEquiv P N θ).1 p

/-- Exact fusion-control implication needed to compare the two orbit
spaces. -/
def SylowFixedOrbitFusion : Prop :=
  ∀ (θ ψ : PPrimeIrreducibleCharacter (joinCenter N) p),
    (P : Subgroup G) ≤ sourceInertia N θ →
    (P : Subgroup G) ≤ sourceInertia N ψ →
    (Quotient.mk'' θ.1 : OrbitSpace (joinCenter N)) =
        Quotient.mk'' ψ.1 →
    (Quotient.mk'' (internalCharacterEquiv P N θ).1 :
        OrbitSpace (internalJoinCenter P N)) =
      Quotient.mk'' (internalCharacterEquiv P N ψ).1

/-- Sylow fixed-point fusion supplies the exact orbit implication for
Rossi's intermediate, since it contains `N_G(P)`. -/
theorem sylowFixedOrbitFusion :
    SylowFixedOrbitFusion P N := by
  intro θ ψ hθ hψ horbit
  exact
    CliffordPartition.internalNormalPPrimeEquiv_coe_quotient_mk_eq_of_sylow_fixed
      (joinCenter N)
      P
      (intermediate P N)
      (NormalSubgroupJoinCenterReduction.normalizer_le_normalizerIntermediate
        P N)
      (NormalSubgroupJoinCenterReduction.joinCenter_le_normalizerIntermediate
        P N)
      hθ hψ horbit

namespace InertiaFibreData

/-- Repackage the orbit block written using a chosen character into the
canonical `Quotient.out` presentation used by `PPrimeOrbitBlock`. -/
def orbitCharacterToBlock
    {A : Type} [Group A]
    (K : Subgroup A) [K.Normal]
    (θ : IrreducibleCharacter K) (p : ℕ) :
    PPrimeIrreducibleCharactersOverOrbit K θ p ≃
      PPrimeOrbitBlock K p
        (Quotient.mk'' θ : OrbitSpace K) :=
  pPrimeOrbitBlockEquivOfQuotientMkEq
    K
    (Quotient.out_eq'
      (Quotient.mk'' θ : OrbitSpace K)).symm
    p

/-- Send a source active orbit to the intermediate orbit of its
Sylow-adapted, identity-transported representative.  The fibre equivalence
proves that this target orbit is active. -/
def forwardOrbit
    (d : InertiaFibreData P N) :
    ActiveOrbit (joinCenter N) p →
      ActiveOrbit (internalJoinCenter P N) p :=
  fun q ↦
    ⟨Quotient.mk'' (forwardRepresentative P N q).1,
      ⟨orbitCharacterToBlock
        (internalJoinCenter P N)
        (forwardRepresentative P N q).1 p
        (cliffordPPrimeCorrespondence
            (internalJoinCenter P N)
            (forwardRepresentative P N q).1
            Fact.out
            (forwardInertiaIndex_isPPrime P N q)
            (d.fibreEquiv
              (sourceRepresentative P N q)
              (sylow_le_sourceInertia P N q)
              (sourceInertiaFibreElement P N q)))⟩⟩

@[simp]
theorem forwardOrbit_coe
    (d : InertiaFibreData P N)
    (q : ActiveOrbit (joinCenter N) p) :
    (forwardOrbit P N d q).1 =
      (Quotient.mk'' (forwardRepresentative P N q).1 :
        OrbitSpace (internalJoinCenter P N)) :=
  rfl

/-- Pull an intermediate active orbit back to the source orbit of a
Sylow-adapted representative.  The inverse fibre equivalence proves that
the source orbit is active. -/
def reverseOrbit
    (d : InertiaFibreData P N) :
    ActiveOrbit (internalJoinCenter P N) p →
      ActiveOrbit (joinCenter N) p :=
  fun r ↦ by
    let θ := reverseRepresentative P N r
    have hcharacter :
        (internalCharacterEquiv P N θ).1 =
          (targetRepresentative P N r).1 :=
      congrArg Subtype.val
        ((internalCharacterEquiv P N).apply_symm_apply
          (targetRepresentative P N r))
    let targetFibre :
        PPrimeIrreducibleCharactersOverInertia
          (internalJoinCenter P N)
          (internalCharacterEquiv P N θ).1 p :=
      pPrimeIrreducibleCharactersOverInertiaCongr
        (internalJoinCenter P N)
        hcharacter.symm p
        (targetInertiaFibreElement P N r)
    let sourceFibre :
        PPrimeIrreducibleCharactersOverInertia
          (joinCenter N) θ.1 p :=
      (d.fibreEquiv θ
        (sylow_le_reverseInertia P N r)).symm
        targetFibre
    exact
      ⟨Quotient.mk'' θ.1,
        ⟨orbitCharacterToBlock
          (joinCenter N) θ.1 p
          (cliffordPPrimeCorrespondence
            (joinCenter N) θ.1 Fact.out
            (reverseInertiaIndex_isPPrime P N r)
            sourceFibre)⟩⟩

@[simp]
theorem reverseOrbit_coe
    (d : InertiaFibreData P N)
    (r : ActiveOrbit (internalJoinCenter P N) p) :
    (reverseOrbit P N d r).1 =
      (Quotient.mk'' (reverseRepresentative P N r).1 :
        OrbitSpace (joinCenter N)) :=
  rfl

/-- Pulling back a forward orbit returns the original source orbit.  This
direction uses only equivariance and the inclusion `H ≤ G`. -/
theorem reverseOrbit_forwardOrbit
    (d : InertiaFibreData P N)
    (q : ActiveOrbit (joinCenter N) p) :
    reverseOrbit P N d (forwardOrbit P N d q) = q := by
  apply Subtype.ext
  rw [reverseOrbit_coe]
  have htarget :
      (Quotient.mk''
          (targetRepresentative P N (forwardOrbit P N d q)).1 :
        OrbitSpace (internalJoinCenter P N)) =
        Quotient.mk'' (forwardRepresentative P N q).1 := by
    calc
      (Quotient.mk''
          (targetRepresentative P N (forwardOrbit P N d q)).1 :
        OrbitSpace (internalJoinCenter P N)) =
          (forwardOrbit P N d q).1 :=
        targetRepresentative_orbit P N (forwardOrbit P N d q)
      _ = Quotient.mk'' (forwardRepresentative P N q).1 :=
        forwardOrbit_coe P N d q
  obtain ⟨h, hh⟩ := Quotient.exact htarget
  have hhPPrime :
      h • forwardRepresentative P N q =
        targetRepresentative P N (forwardOrbit P N d q) := by
    apply Subtype.ext
    exact hh
  have hsource :
      (((h : intermediate P N) : G) •
          sourceRepresentative P N q) =
        reverseRepresentative P N (forwardOrbit P N d q) := by
    apply (internalCharacterEquiv P N).injective
    rw [
      IrreducibleCharacter.internalNormalPPrimeEquiv_smul
        (joinCenter N) (intermediate P N)
        (NormalSubgroupJoinCenterReduction.joinCenter_le_normalizerIntermediate
          P N)
        p h
        (sourceRepresentative P N q)]
    change
      h • forwardRepresentative P N q =
        internalCharacterEquiv P N
          (reverseRepresentative P N (forwardOrbit P N d q))
    rw [(internalCharacterEquiv P N).apply_symm_apply]
    exact hhPPrime
  calc
    (Quotient.mk''
        (reverseRepresentative P N (forwardOrbit P N d q)).1 :
      OrbitSpace (joinCenter N)) =
        Quotient.mk''
          ((((h : intermediate P N) : G) •
            sourceRepresentative P N q).1) := by
      rw [hsource]
    _ = Quotient.mk'' (sourceRepresentative P N q).1 := by
      apply Quotient.sound
      exact
        MulAction.mem_orbit
          (sourceRepresentative P N q).1
          (((h : intermediate P N) : G))
    _ = q.1 :=
      sourceRepresentative_orbit P N q

/-- Fusion control gives the other inverse law. -/
theorem forwardOrbit_reverseOrbit
    (d : InertiaFibreData P N)
    (hfusion : SylowFixedOrbitFusion P N)
    (r : ActiveOrbit (internalJoinCenter P N) p) :
    forwardOrbit P N d (reverseOrbit P N d r) = r := by
  apply Subtype.ext
  rw [forwardOrbit_coe]
  let θ :=
    sourceRepresentative P N (reverseOrbit P N d r)
  let ψ :=
    reverseRepresentative P N r
  have horbit :
      (Quotient.mk'' θ.1 :
          OrbitSpace (joinCenter N)) =
        Quotient.mk'' ψ.1 := by
    calc
      (Quotient.mk'' θ.1 :
          OrbitSpace (joinCenter N)) =
          (reverseOrbit P N d r).1 :=
        sourceRepresentative_orbit P N (reverseOrbit P N d r)
      _ = Quotient.mk'' ψ.1 :=
        reverseOrbit_coe P N d r
  have htarget :=
    hfusion θ ψ
      (sylow_le_sourceInertia P N (reverseOrbit P N d r))
      (sylow_le_reverseInertia P N r)
      horbit
  have hcharacter :
      internalCharacterEquiv P N ψ =
        targetRepresentative P N r :=
    (internalCharacterEquiv P N).apply_symm_apply
      (targetRepresentative P N r)
  calc
    (Quotient.mk''
        (forwardRepresentative P N (reverseOrbit P N d r)).1 :
      OrbitSpace (internalJoinCenter P N)) =
        Quotient.mk'' (internalCharacterEquiv P N θ).1 :=
      rfl
    _ = Quotient.mk'' (internalCharacterEquiv P N ψ).1 :=
      htarget
    _ = Quotient.mk'' (targetRepresentative P N r).1 := by
      rw [hcharacter]
    _ = r.1 :=
      targetRepresentative_orbit P N r

/-- The active-orbit equivalence produced from fibre equivalences and Sylow
fusion control. -/
def activeOrbitEquiv
    (d : InertiaFibreData P N)
    (hfusion : SylowFixedOrbitFusion P N) :
    ActiveOrbit (joinCenter N) p ≃
      ActiveOrbit (internalJoinCenter P N) p where
  toFun := forwardOrbit P N d
  invFun := reverseOrbit P N d
  left_inv := reverseOrbit_forwardOrbit P N d
  right_inv := forwardOrbit_reverseOrbit P N d hfusion

@[simp]
theorem activeOrbitEquiv_apply_coe
    (d : InertiaFibreData P N)
    (hfusion : SylowFixedOrbitFusion P N)
    (q : ActiveOrbit (joinCenter N) p) :
    (activeOrbitEquiv P N d hfusion q).1 =
      (Quotient.mk'' (forwardRepresentative P N q).1 :
        OrbitSpace (internalJoinCenter P N)) :=
  rfl

/-- Package the orbit equivalence, adapted representatives, and inertia
fibre equivalences in the generic Clifford assembler. -/
def toAdaptedCliffordFibreAssemblyData
    (d : InertiaFibreData P N)
    (hfusion : SylowFixedOrbitFusion P N) :
    AdaptedCliffordFibreAssemblyData
      (joinCenter N) (internalJoinCenter P N) p where
  activeOrbitEquiv := activeOrbitEquiv P N d hfusion
  sourceRepresentative := sourceRepresentative P N
  sourceRepresentative_orbit :=
    sourceRepresentative_orbit P N
  sourceInertiaIndex_isPPrime := fun q ↦
    q.sylowRepresentative_inertia_index_isPPrime
      (joinCenter N) P
  targetRepresentative := forwardRepresentative P N
  targetRepresentative_orbit := fun q ↦ rfl
  targetInertiaIndex_isPPrime :=
    forwardInertiaIndex_isPPrime P N
  inertiaFibreEquiv := fun q ↦
    d.fibreEquiv
      (sourceRepresentative P N q)
      (sylow_le_sourceInertia P N q)

/-- The global prime-to-`p` character equivalence in Rossi's Proposition
4.2, assuming the family of inertia-fibre equivalences. -/
def assembledPPrimeEquiv
    (d : InertiaFibreData P N)
    (hfusion : SylowFixedOrbitFusion P N) :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter (intermediate P N) p :=
  (toAdaptedCliffordFibreAssemblyData
    P N d hfusion).assembledPPrimeEquiv

/-- The global equivalence with the fusion input discharged by Sylow
fixed-point fusion. -/
def assembledPPrimeEquivCanonical
    (d : InertiaFibreData P N) :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter (intermediate P N) p :=
  assembledPPrimeEquiv P N d
    (sylowFixedOrbitFusion P N)

end InertiaFibreData

end NormalSubgroupIntermediateOrbitAssembly
end InductiveMcKay
end McKayConjecture
