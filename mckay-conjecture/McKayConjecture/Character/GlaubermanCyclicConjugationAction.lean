/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionConjugation
import McKayConjecture.Character.GlaubermanActionSourceUniqueness
import McKayConjecture.Character.GlaubermanCyclicSourceUniqueness

/-!
# The cyclic trace as a strong conjugation-action correspondence

This file identifies the fixed-point coordinates used by the cyclic
ambient trace with the fixed points of the abstract conjugation action.
The source uniqueness and injectivity proved from the cyclic trace then
feed directly into the generic strong-correspondence constructor.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable (K P : Subgroup G) [K.Normal]
variable [IsCyclic P]
variable {p : ℕ} [Fact p.Prime]

local instance cyclicConjugationMulDistribMulAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K P

/-- Equality of the cyclic and whole-subgroup centralizers, regarded as
an explicit group isomorphism with unchanged underlying elements. -/
def cyclicFixedPointsEquivCoprimeFixedPoints :
    cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G) ≃*
      coprimeFixedPoints K P where
  toFun c :=
    ⟨c.1, by
      rw [← cyclicFixedPoints_cyclicSubgroupGenerator K P]
      exact c.2⟩
  invFun c :=
    ⟨c.1, by
      rw [cyclicFixedPoints_cyclicSubgroupGenerator K P]
      exact c.2⟩
  left_inv c := by
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Subtype.ext
    rfl
  map_mul' c d := by
    apply Subtype.ext
    rfl

/-- The fixed points of the conjugation action are the cyclic
fixed-point subgroup for the selected generator. -/
def subgroupConjugationFixedPointsEquivCyclic :
    FixedPoints.subgroup P K ≃*
      cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G) :=
  (subgroupConjugationFixedPointsEquiv K P).trans
    (cyclicFixedPointsEquivCoprimeFixedPoints K P).symm

@[simp]
theorem subgroupConjugationFixedPointsEquivCyclic_apply_coe
    (c : FixedPoints.subgroup P K) :
    ((subgroupConjugationFixedPointsEquivCyclic
      K P c :
        cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G)) : G) =
      ((c : K) : G) :=
  rfl

/-- Restriction multiplicity agrees in the cyclic ambient and abstract
conjugation fixed-point coordinates. -/
theorem restrictionMultiplicity_subgroupConjugationFixedPointsEquivCyclic
    (ψ :
      IrreducibleCharacter
        (cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G)))
    (θ : IrreducibleCharacter K) :
    restrictionMultiplicity
        (actionFixedPointsInclusion P K)
        (ψ.comap
          (subgroupConjugationFixedPointsEquivCyclic
            K P))
        θ =
      restrictionMultiplicity
        (cyclicFixedPointsInclusion K
          ((cyclicSubgroupGenerator P : P) : G))
        ψ θ := by
  let eC :=
    subgroupConjugationFixedPointsEquivCyclic K P
  have hcomm :
      (MulEquiv.refl K).toMonoidHom.comp
          (actionFixedPointsInclusion P K) =
        (cyclicFixedPointsInclusion K
          ((cyclicSubgroupGenerator P : P) : G)).comp
          eC.toMonoidHom := by
    ext c
    rfl
  simpa using
    restrictionMultiplicity_comap_equiv
      (MulEquiv.refl K) eC
      (cyclicFixedPointsInclusion K
        ((cyclicSubgroupGenerator P : P) : G))
      (actionFixedPointsInclusion P K)
      hcomm ψ θ

/-- The single-coefficient cyclic trace shape gives full source
uniqueness in abstract conjugation-action coordinates. -/
theorem existsUnique_actionRestrictionMultiplicity_isPPrime_of_cyclicTraceShape
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (hshape :
      CyclicTraceSingleCoefficientShape
        K P hK hP hgenerate)
    (θa :
      ActionInvariantPPrimeIrreducibleCharacter P K p) :
    ∃! φ :
        IrreducibleCharacter (FixedPoints.subgroup P K),
      HasPPrimeRestrictionMultiplicityIrreducible
        P K θa φ := by
  let eSource :=
    pInvariantCharacterEquivActionInvariant
      (p := p) K P
  let θ :=
    eSource.symm θa
  let eC :=
    subgroupConjugationFixedPointsEquivCyclic K P
  let eIrr :=
    IrreducibleCharacter.comapEquiv eC
  obtain ⟨ψ, hψ, hunique⟩ :=
    cyclicTrace_existsUnique_restrictionMultiplicity_isPPrime
      K P hK hP hgenerate hshape θ
  refine ⟨eIrr ψ, ?_, ?_⟩
  · change
      ¬p ∣
        restrictionMultiplicity
          (actionFixedPointsInclusion P K)
          (ψ.comap eC) θa.1.1
    rw [
      restrictionMultiplicity_subgroupConjugationFixedPointsEquivCyclic]
    exact hψ
  · intro φ hφ
    have hback :
        (eIrr.symm φ).comap eC = φ := by
      change eIrr (eIrr.symm φ) = φ
      exact eIrr.apply_symm_apply φ
    have hφcyclic :
        ¬p ∣
          restrictionMultiplicity
            (cyclicFixedPointsInclusion K
              ((cyclicSubgroupGenerator P : P) : G))
            (eIrr.symm φ) θ.1.1 := by
      rw [←
        restrictionMultiplicity_subgroupConjugationFixedPointsEquivCyclic
          K P]
      rw [hback]
      exact hφ
    have heq : eIrr.symm φ = ψ :=
      hunique (eIrr.symm φ) hφcyclic
    calc
      φ = eIrr (eIrr.symm φ) :=
        (eIrr.apply_symm_apply φ).symm
      _ = eIrr ψ := congrArg eIrr heq

/-- Under the cyclic trace shape, the full source-unique
correspondent in conjugation coordinates is injective. -/
theorem sourceUniqueCorrespondent_conjugation_injective_of_cyclicTraceShape
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (hshape :
      CyclicTraceSingleCoefficientShape
        K P hK hP hgenerate) :
    Function.Injective
      (sourceUniqueCorrespondent P K
        (existsUnique_actionRestrictionMultiplicity_isPPrime_of_cyclicTraceShape
          K P hK hP hgenerate hshape)) := by
  let eSource :=
    pInvariantCharacterEquivActionInvariant
      (p := p) K P
  let eC :=
    subgroupConjugationFixedPointsEquivCyclic K P
  let eIrr :=
    IrreducibleCharacter.comapEquiv eC
  let hsource :=
    existsUnique_actionRestrictionMultiplicity_isPPrime_of_cyclicTraceShape
      K P hK hP hgenerate hshape
  intro θa ηa heq
  let θ := eSource.symm θa
  let η := eSource.symm ηa
  let ψθ :=
    cyclicTraceCorrespondent
      K P hK hP hgenerate hshape θ
  let ψη :=
    cyclicTraceCorrespondent
      K P hK hP hgenerate hshape η
  have hψθ :
      HasPPrimeRestrictionMultiplicityIrreducible
        P K θa (eIrr ψθ) := by
    change
      ¬p ∣
        restrictionMultiplicity
          (actionFixedPointsInclusion P K)
          (ψθ.comap eC) θa.1.1
    rw [
      restrictionMultiplicity_subgroupConjugationFixedPointsEquivCyclic]
    exact
      not_dvd_restrictionMultiplicity_of_cyclicCoefficient_isOfFinOrder
        K P hK hP hgenerate θ ψθ
        (ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ)
          ψθ.toClassFunction)
        rfl
        (Classical.choose_spec (hshape θ)).1
  have hψη :
      HasPPrimeRestrictionMultiplicityIrreducible
        P K ηa (eIrr ψη) := by
    change
      ¬p ∣
        restrictionMultiplicity
          (actionFixedPointsInclusion P K)
          (ψη.comap eC) ηa.1.1
    rw [
      restrictionMultiplicity_subgroupConjugationFixedPointsEquivCyclic]
    exact
      not_dvd_restrictionMultiplicity_of_cyclicCoefficient_isOfFinOrder
        K P hK hP hgenerate η ψη
        (ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate η)
          ψη.toClassFunction)
        rfl
        (Classical.choose_spec (hshape η)).1
  have hchooseθ :
      eIrr ψθ =
        sourceUniqueCorrespondent P K hsource θa :=
    (hsource θa).unique hψθ
      (sourceUniqueCorrespondent_multiplicity_isPPrime
        P K hsource θa)
  have hchooseη :
      eIrr ψη =
        sourceUniqueCorrespondent P K hsource ηa :=
    (hsource ηa).unique hψη
      (sourceUniqueCorrespondent_multiplicity_isPPrime
        P K hsource ηa)
  have htargets : ψθ = ψη := by
    apply eIrr.injective
    calc
      eIrr ψθ =
          sourceUniqueCorrespondent P K hsource θa :=
        hchooseθ
      _ =
          sourceUniqueCorrespondent P K hsource ηa :=
        heq
      _ = eIrr ψη := hchooseη.symm
  have hambient : θ = η :=
    cyclicTraceCorrespondent_injective
      K P hK hP hgenerate hshape htargets
  exact eSource.symm.injective hambient

/-- The cyclic trace shape constructs the strong correspondence for the
abstract conjugation action. -/
def strongConjugationActionGlaubermanCorrespondenceOfCyclicTraceShape
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (hshape :
      CyclicTraceSingleCoefficientShape
        K P hK hP hgenerate) :
    StrongActionGlaubermanCorrespondence P K p :=
  strongActionGlaubermanCorrespondenceOfSourceUniqueness
    P K hP hK
    (existsUnique_actionRestrictionMultiplicity_isPPrime_of_cyclicTraceShape
      K P hK hP hgenerate hshape)
    (sourceUniqueCorrespondent_conjugation_injective_of_cyclicTraceShape
      K P hK hP hgenerate hshape)

/-- Strong cyclic Glauberman correspondence for an ambient conjugation
action, with the trace shape discharged by Kronecker's theorem. -/
def strongCyclicConjugationActionGlaubermanCorrespondence
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤) :
    StrongActionGlaubermanCorrespondence P K p :=
  strongConjugationActionGlaubermanCorrespondenceOfCyclicTraceShape
    K P hK hP hgenerate
    (cyclicTraceSingleCoefficientShape
      K P hK hP hgenerate)

end McKayConjecture
