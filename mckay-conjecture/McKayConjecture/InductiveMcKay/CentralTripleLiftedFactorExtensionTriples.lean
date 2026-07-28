/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralCharacterExtension
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorNormalLift
import McKayConjecture.InductiveMcKay.CentralTripleLiftedFactorCorrespondence
import McKayConjecture.InductiveMcKay.CompleteCentralIsomorphismExtension

/-!
# Character triples on the two lifted factor extensions

The lifted-factor formulation of Dade--Glauberman--Nagao uses two honest
factor extensions.  Their distinguished normal subgroups are the ranges of
the canonical lifts of the two original normal subgroups.  This file makes
those two lifted character triples explicit.

The canonical source factor-extension character is an exact extension of
the source lifted triple.  Therefore any complete central-isomorphism
witness between these lifted triples automatically sends it to an exact
extension of the target normal character.  This isolates the remaining
Proposition-4.5 task as the construction of that lifted complete witness
(and identification of its character image), rather than a separate
normal-restriction calculation.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace LiftedFactorCorrespondence

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}
variable
  (R : AssociatedProjectiveRepresentation T V P)
  (F : R.AssociatedFiniteFactorNormalization)
  (g : CentralRestrictionGroupData T U e)

/-! ## Source lifted triple -/

/-- The canonical source normal lift, as an equivalence onto its range. -/
def sourceNormalLiftEquiv :
    T.normalSubgroup ≃*
      (F.ambientNormalSubgroupLift R).range :=
  MonoidHom.ofInjective
    (F.ambientNormalSubgroupLift_injective R)

@[simp]
theorem sourceNormalLiftEquiv_apply_coe
    (n : T.normalSubgroup) :
    ((sourceNormalLiftEquiv R F n :
        (F.ambientNormalSubgroupLift R).range) :
      SourceFactorCentralExtensionGroup R F g) =
        F.ambientNormalSubgroupLift R n :=
  rfl

@[simp]
theorem sourceNormalLiftEquiv_apply_subtype
    (n : T.normalSubgroup) :
    (F.ambientNormalSubgroupLift R).range.subtype
        (sourceNormalLiftEquiv R F n) =
      F.ambientNormalSubgroupLift R n :=
  rfl

/-- The character triple on the source factor extension whose normal copy
is the canonical lift of `T.normalSubgroup`. -/
def sourceLiftedTriple :
    CharacterTriple
      (SourceFactorCentralExtensionGroup R F g) where
  normalSubgroup :=
    (F.ambientNormalSubgroupLift R).range
  isNormal := inferInstance
  character :=
    T.character.comap (sourceNormalLiftEquiv R F).symm
  isInvariant := by
    intro a x
    obtain ⟨n, rfl⟩ :=
      (sourceNormalLiftEquiv R F).surjective x
    have hconj :
        conjugateNormalElement
            (F.ambientNormalSubgroupLift R).range inferInstance a
            (sourceNormalLiftEquiv R F n) =
          sourceNormalLiftEquiv R F
            (F.ambientNormalConjugate R a n) := by
      apply Subtype.ext
      exact F.conjugate_ambientNormalSubgroupLift R a n
    rw [hconj]
    simp only
      [IrreducibleCharacter.comap_values,
        MulEquiv.symm_apply_apply]
    exact
      T.isInvariant
        (CharacterTriple.FactorSet.CentralExtensionGroup.base
          F.factorSet (F.factorSet_isNormalized R) a)
        n

/-- The canonical honest source factor-extension character extends the
source lifted triple character. -/
theorem sourceCharacter_isExtension_sourceLiftedTriple :
    IrreducibleCharacter.IsExtensionAlong
      (sourceLiftedTriple R F g).normalSubgroup.subtype
      (sourceLiftedTriple R F g).character
      (sourceCharacter R F g) := by
  intro x
  obtain ⟨n, rfl⟩ :=
    (sourceNormalLiftEquiv R F).surjective x
  change
    (F.ambientFactorCentralExtensionCharacter R).values
        ((F.ambientNormalSubgroupLift R).range.subtype
          (sourceNormalLiftEquiv R F n)) =
      T.character.values
        ((sourceNormalLiftEquiv R F).symm
          (sourceNormalLiftEquiv R F n))
  simpa only
      [sourceNormalLiftEquiv_apply_subtype,
        MulEquiv.symm_apply_apply] using
    F.ambientFactorCentralExtensionCharacter_isExtensionAlong_normalLift
      R n

/-! ## Target lifted triple -/

/-- The target normal lift is injective. -/
theorem targetNormalLift_injective :
    Function.Injective (targetNormalLift R F g) := by
  intro x y hxy
  apply Subtype.ext
  have hbase :=
    congrArg
      (CharacterTriple.FactorSet.CentralExtensionGroup.base
        (targetFactorSet R F g)
        (targetFactorSet_isNormalized R F g))
      hxy
  exact hbase

/-- The canonical target normal lift, as an equivalence onto its range. -/
def targetNormalLiftEquiv :
    U.normalSubgroup ≃*
      (targetNormalLift R F g).range :=
  MonoidHom.ofInjective
    (targetNormalLift_injective R F g)

@[simp]
theorem targetNormalLiftEquiv_apply_coe
    (m : U.normalSubgroup) :
    ((targetNormalLiftEquiv R F g m :
        (targetNormalLift R F g).range) :
      TargetFactorCentralExtensionGroup R F g) =
        targetNormalLift R F g m :=
  rfl

@[simp]
theorem targetNormalLiftEquiv_apply_subtype
    (m : U.normalSubgroup) :
    (targetNormalLift R F g).range.subtype
        (targetNormalLiftEquiv R F g m) =
      targetNormalLift R F g m :=
  rfl

@[simp]
theorem targetNormalLift_base
    (m : U.normalSubgroup) :
    CharacterTriple.FactorSet.CentralExtensionGroup.base
        (targetFactorSet R F g)
        (targetFactorSet_isNormalized R F g)
        (targetNormalLift R F g m) =
      (m : B) :=
  rfl

@[simp]
theorem targetNormalLift_coefficient
    (m : U.normalSubgroup) :
    CharacterTriple.FactorSet.CentralExtensionGroup.coefficient
        (targetFactorSet R F g)
        (targetFactorSet_isNormalized R F g)
        (targetNormalLift R F g m) =
      1 :=
  rfl

/-- Conjugation of a target normal element by the base coordinate of a
target factor-extension element. -/
def targetNormalConjugate
    (a : TargetFactorCentralExtensionGroup R F g)
    (m : U.normalSubgroup) :
    U.normalSubgroup :=
  ⟨CharacterTriple.FactorSet.CentralExtensionGroup.base
        (targetFactorSet R F g)
        (targetFactorSet_isNormalized R F g) a *
      (m : B) *
      (CharacterTriple.FactorSet.CentralExtensionGroup.base
        (targetFactorSet R F g)
        (targetFactorSet_isNormalized R F g) a)⁻¹,
    (inferInstance : U.normalSubgroup.Normal).conj_mem
      m m.property
      (CharacterTriple.FactorSet.CentralExtensionGroup.base
        (targetFactorSet R F g)
        (targetFactorSet_isNormalized R F g) a)⟩

@[simp]
theorem targetNormalConjugate_coe
    (a : TargetFactorCentralExtensionGroup R F g)
    (m : U.normalSubgroup) :
    (targetNormalConjugate R F g a m : B) =
      CharacterTriple.FactorSet.CentralExtensionGroup.base
          (targetFactorSet R F g)
          (targetFactorSet_isNormalized R F g) a *
        (m : B) *
        (CharacterTriple.FactorSet.CentralExtensionGroup.base
          (targetFactorSet R F g)
          (targetFactorSet_isNormalized R F g) a)⁻¹ :=
  rfl

/-- Moving a target normal lift past an arbitrary extension element
conjugates it by the base coordinate. -/
theorem mul_targetNormalLift
    (a : TargetFactorCentralExtensionGroup R F g)
    (m : U.normalSubgroup) :
    a * targetNormalLift R F g m =
      targetNormalLift R F g
          (targetNormalConjugate R F g a m) *
        a := by
  apply CharacterTriple.FactorSet.CentralExtensionGroup.ext
  · simp [targetNormalConjugate, mul_assoc]
  · simp only
      [CharacterTriple.FactorSet.CentralExtensionGroup.coefficient_mul,
        targetNormalLift_base, targetNormalLift_coefficient, mul_one]
    rw [
      targetFactorSet_normal_right R F g
        (CharacterTriple.FactorSet.CentralExtensionGroup.base
          (targetFactorSet R F g)
          (targetFactorSet_isNormalized R F g) a) m,
      targetFactorSet_normal_left R F g
        (targetNormalConjugate R F g a m)
        (CharacterTriple.FactorSet.CentralExtensionGroup.base
          (targetFactorSet R F g)
          (targetFactorSet_isNormalized R F g) a)]

/-- Conjugation in the target factor extension restricts to ordinary
conjugation on the canonical target normal lift. -/
theorem conjugate_targetNormalLift
    (a : TargetFactorCentralExtensionGroup R F g)
    (m : U.normalSubgroup) :
    a * targetNormalLift R F g m * a⁻¹ =
      targetNormalLift R F g
        (targetNormalConjugate R F g a m) := by
  rw [mul_targetNormalLift R F g a m]
  simp

/-- The range of the target normal lift is normal in the target factor
extension. -/
instance targetNormalLift_range_normal :
    (targetNormalLift R F g).range.Normal where
  conj_mem := by
    intro y hy a
    obtain ⟨m, rfl⟩ := hy
    refine ⟨targetNormalConjugate R F g a m, ?_⟩
    exact (conjugate_targetNormalLift R F g a m).symm

/-- The character triple on the target factor extension whose normal copy
is the canonical lift of `U.normalSubgroup`. -/
def targetLiftedTriple :
    CharacterTriple
      (TargetFactorCentralExtensionGroup R F g) where
  normalSubgroup :=
    (targetNormalLift R F g).range
  isNormal := inferInstance
  character :=
    U.character.comap (targetNormalLiftEquiv R F g).symm
  isInvariant := by
    intro a x
    obtain ⟨m, rfl⟩ :=
      (targetNormalLiftEquiv R F g).surjective x
    have hconj :
        conjugateNormalElement
            (targetNormalLift R F g).range inferInstance a
            (targetNormalLiftEquiv R F g m) =
          targetNormalLiftEquiv R F g
            (targetNormalConjugate R F g a m) := by
      apply Subtype.ext
      exact conjugate_targetNormalLift R F g a m
    rw [hconj]
    simp only
      [IrreducibleCharacter.comap_values,
        MulEquiv.symm_apply_apply]
    exact
      U.isInvariant
        (CharacterTriple.FactorSet.CentralExtensionGroup.base
          (targetFactorSet R F g)
          (targetFactorSet_isNormalized R F g) a)
        m

/-- Extension along the range inclusion of the target lift is equivalent to
extension along the original target normal-lift homomorphism. -/
theorem isExtension_targetLiftedTriple_iff
    (ψ :
      IrreducibleCharacter
        (TargetFactorCentralExtensionGroup R F g)) :
    IrreducibleCharacter.IsExtensionAlong
        (targetLiftedTriple R F g).normalSubgroup.subtype
        (targetLiftedTriple R F g).character ψ ↔
      IrreducibleCharacter.IsExtensionAlong
        (targetNormalLift R F g) U.character ψ := by
  constructor
  · intro h m
    have hm := h (targetNormalLiftEquiv R F g m)
    change
      ψ.values
          ((targetNormalLift R F g).range.subtype
            (targetNormalLiftEquiv R F g m)) =
        U.character.values
          ((targetNormalLiftEquiv R F g).symm
            (targetNormalLiftEquiv R F g m)) at hm
    rw [targetNormalLiftEquiv_apply_subtype R F g m,
      MulEquiv.symm_apply_apply] at hm
    exact hm
  · intro h x
    obtain ⟨m, rfl⟩ :=
      (targetNormalLiftEquiv R F g).surjective x
    change
      ψ.values
          ((targetNormalLift R F g).range.subtype
            (targetNormalLiftEquiv R F g m)) =
        U.character.values
          ((targetNormalLiftEquiv R F g).symm
            (targetNormalLiftEquiv R F g m))
    rw [targetNormalLiftEquiv_apply_subtype R F g m,
      MulEquiv.symm_apply_apply]
    exact h m

/-! ## Exact extension transport through a lifted central witness -/

/-- The target character obtained by applying a complete central-isomorphism
witness between the two lifted triples to the canonical source extension. -/
def liftedExtensionImage
    (C :
      CompleteCentralIsomorphismWitness
        (sourceLiftedTriple R F g)
        (targetLiftedTriple R F g)) :
    IrreducibleCharacter
      (TargetFactorCentralExtensionGroup R F g) :=
  C.extensionImage
    (sourceCharacter R F g)
    (sourceCharacter_isExtension_sourceLiftedTriple R F g)

/-- A complete central-isomorphism witness between the concrete lifted
factor-extension triples automatically supplies the exact target-normal
restriction required by `ImageData`. -/
theorem liftedExtensionImage_extendsTargetNormalCharacter
    (C :
      CompleteCentralIsomorphismWitness
        (sourceLiftedTriple R F g)
        (targetLiftedTriple R F g)) :
    IrreducibleCharacter.IsExtensionAlong
      (targetNormalLift R F g) U.character
      (liftedExtensionImage R F g C) := by
  rw [← isExtension_targetLiftedTriple_iff R F g]
  exact
    C.extensionImage_isExtension
      (sourceCharacter R F g)
      (sourceCharacter_isExtension_sourceLiftedTriple R F g)

/-- The precise compatibility needed to transfer the extension theorem to a
previously constructed target character: that character is the central
extension image for some complete witness between the concrete lifted
triples.

This is intentionally weaker than `ImageData`: it contains neither a
coefficient-character assertion nor normalized centralizer values. -/
def IsLiftedExtensionImage
    (ψ :
      IrreducibleCharacter
        (TargetFactorCentralExtensionGroup R F g)) : Prop :=
  ∃ C :
      CompleteCentralIsomorphismWitness
        (sourceLiftedTriple R F g)
        (targetLiftedTriple R F g),
    liftedExtensionImage R F g C = ψ

/-- Identification as a lifted central-extension image is enough to prove
the exact target-normal restriction. -/
theorem IsLiftedExtensionImage.extendsTargetNormalCharacter
    {ψ :
      IrreducibleCharacter
        (TargetFactorCentralExtensionGroup R F g)}
    (hψ : IsLiftedExtensionImage R F g ψ) :
    IrreducibleCharacter.IsExtensionAlong
      (targetNormalLift R F g) U.character ψ := by
  obtain ⟨C, rfl⟩ := hψ
  exact liftedExtensionImage_extendsTargetNormalCharacter R F g C

/-- Package a complete lifted witness into `ImageData` once the two
independent coefficient and normalized-value assertions have been verified.
The target-normal restriction is supplied automatically. -/
def ImageData.ofLiftedCompleteCentralWitness
    (C :
      CompleteCentralIsomorphismWitness
        (sourceLiftedTriple R F g)
        (targetLiftedTriple R F g))
    (hcoeff :
      FactorSet.CentralExtensionGroup.HasCoefficientCharacter
        (targetFactorSet R F g)
        (targetFactorSet_isNormalized R F g)
        (coefficientHom R F g)
        (liftedExtensionImage R F g C))
    (hvalues :
      ∀ b : B,
        e b ∈
            Subgroup.centralizer
              (T.normalSubgroup : Set A) →
          (sourceCharacter R F g).values
                (FactorSet.CentralExtensionGroup.baseLift
                  F.factorSet (F.factorSet_isNormalized R) (e b)) *
              ((liftedExtensionImage R F g C).degree : ℂ) =
            (liftedExtensionImage R F g C).values
                (FactorSet.CentralExtensionGroup.baseLift
                  (targetFactorSet R F g)
                  (targetFactorSet_isNormalized R F g) b) *
              ((sourceCharacter R F g).degree : ℂ)) :
    ImageData R F g where
  targetCharacter := liftedExtensionImage R F g C
  coefficientCharacter := hcoeff
  extendsTargetNormalCharacter :=
    liftedExtensionImage_extendsTargetNormalCharacter R F g C
  normalizedBaseLiftValues := hvalues

end LiftedFactorCorrespondence
end InductiveMcKay
end McKayConjecture
