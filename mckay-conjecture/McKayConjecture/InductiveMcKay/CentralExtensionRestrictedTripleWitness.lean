/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.Transitivity
import McKayConjecture.InductiveMcKay.CentralExtensionTripleRestriction

/-!
# Restriction of an upstairs central triple witness

This file proves that a central-isomorphism witness for the full upstairs
character stabilizer restricts to the copy of the downstairs stabilizer
selected by a coherent automorphism lift.

The proof restricts the two associated projective representations literally.
All four subgroup conditions are reverified on the pullback semidirect
groups.  Thus restriction introduces no new representation-theoretic
hypothesis and no character-bijection hypothesis.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace InductiveMcKay
namespace SylowAutomorphismLift

open GroupTheory
open CharacterTriple

variable {A : Type u} {Q : Type v}
variable [Group A] [Group Q] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable {E : GroupTheory.CentralExtension A Q} {S : Sylow p Q}
variable
  (L : SylowAutomorphismLift E S)
  (d : LocalInductiveMcKayData (E.sylowLift S))
  (χ : PPrimeIrreducibleCharacter Q p)

variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]

private abbrev oldAmbientTriple
    (E : CentralExtension A Q) (S : Sylow p Q)
    (χ : PPrimeIrreducibleCharacter Q p) :=
  EquivariantLocalCorrespondence.ambientTriple
    (P := E.sylowLift S)
    (inflatedCharacter E χ)

private abbrev oldIntermediateTriple
    (d : LocalInductiveMcKayData (E.sylowLift S))
    (χ : PPrimeIrreducibleCharacter Q p) :=
  d.toEquivariant.intermediateTriple
    (inflatedCharacter E χ)

private abbrev oldEmbedding
    (d : LocalInductiveMcKayData (E.sylowLift S))
    (χ : PPrimeIrreducibleCharacter Q p) :=
  d.toEquivariant.semidirectEmbedding
    (inflatedCharacter E χ)

/-- Membership in the ambient pullback is exactly membership of the right
coordinate in the selected stabilizer range. -/
theorem mem_ambientLiftPullback_iff
    (a :
      A ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer
          (E.sylowLift S) (inflatedCharacter E χ)) :
    a ∈ ambientLiftPullback L χ ↔
      a.right ∈ characterStabilizerLiftRange L χ :=
  Iff.rfl

/-- Membership in the intermediate pullback has the same coordinatewise
description. -/
theorem mem_intermediateLiftPullback_iff
    (a :
      d.toEquivariant.intermediate ⋊[
        d.toEquivariant.stabilizerIntermediateAction
          (inflatedCharacter E χ)]
        PPrimeCharacterStabilizer
          (E.sylowLift S) (inflatedCharacter E χ)) :
    a ∈ intermediateLiftPullback L d χ ↔
      a.right ∈ characterStabilizerLiftRange L χ :=
  Iff.rfl

/-- The restricted embedding preserves the right coordinate. -/
@[simp]
theorem restrictedSemidirectEmbedding_right
    (b : intermediateLiftPullback L d χ) :
    ((restrictedSemidirectEmbedding L d χ b :
      ambientLiftPullback L χ) :
      A ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer
          (E.sylowLift S) (inflatedCharacter E χ)).right =
      b.1.right :=
  rfl

/-- Restrict a full upstairs witness to the lifted downstairs character
stabilizer. -/
def restrictCentralIsomorphismWitness
    (C : CentralIsomorphismWitness
      (oldAmbientTriple E S χ)
      (oldIntermediateTriple d χ) V W)
    (hC : C.embedding = oldEmbedding d χ) :
    CentralIsomorphismWitness
      (restrictedAmbientTriple L χ)
      (restrictedIntermediateTriple L d χ) V W where
  leftProjective :=
    C.leftProjective.comap
      (ambientLiftPullback L χ).subtype
  leftAssociated :=
    C.leftAssociated.restrictTo
      (ambientLiftPullback L χ)
      (ambientNormal_le_liftPullback L χ)
  rightProjective :=
    C.rightProjective.comap
      (intermediateLiftPullback L d χ).subtype
  rightAssociated :=
    C.rightAssociated.restrictTo
      (intermediateLiftPullback L d χ)
      (intermediateNormal_le_liftPullback L d χ)
  embedding := restrictedSemidirectEmbedding L d χ
  embedding_injective :=
    restrictedSemidirectEmbedding_injective L d χ
  centralizer_le := by
    intro a ha
    have haOld :
        (a.1 :
          A ⋊[PPrimeCharacterStabilizer.ambientAction]
            PPrimeCharacterStabilizer
              (E.sylowLift S) (inflatedCharacter E χ)) ∈
          Subgroup.centralizer
            ((oldAmbientTriple E S χ).normalSubgroup :
              Set
                (A ⋊[
                  PPrimeCharacterStabilizer.ambientAction]
                  PPrimeCharacterStabilizer
                    (E.sylowLift S)
                    (inflatedCharacter E χ))) := by
      rw [Subgroup.mem_centralizer_iff] at ha ⊢
      intro x hx
      let xPullback : ambientLiftPullback L χ :=
        ⟨x, ambientNormal_le_liftPullback L χ hx⟩
      have hxRestricted :
          xPullback ∈
            (restrictedAmbientTriple L χ).normalSubgroup :=
        hx
      exact congrArg Subtype.val (ha xPullback hxRestricted)
    obtain ⟨b, hb⟩ := C.centralizer_le haOld
    have hbPullback :
        b ∈ intermediateLiftPullback L d χ := by
      rw [mem_intermediateLiftPullback_iff L d χ]
      have hright :=
        congrArg SemidirectProduct.right hb
      rw [hC] at hright
      change b.right = a.1.right at hright
      rw [hright]
      exact a.property
    let bPullback : intermediateLiftPullback L d χ :=
      ⟨b, hbPullback⟩
    refine ⟨bPullback, ?_⟩
    apply Subtype.ext
    change oldEmbedding d χ b = a.1
    rw [← hC]
    exact hb
  ambient_eq_product := by
    intro a
    obtain ⟨x, b, hxb⟩ := C.ambient_eq_product a.1
    have hbPullback :
        b ∈ intermediateLiftPullback L d χ := by
      rw [mem_intermediateLiftPullback_iff L d χ]
      have hxRight :
          (x :
            A ⋊[PPrimeCharacterStabilizer.ambientAction]
              PPrimeCharacterStabilizer
                (E.sylowLift S)
                (inflatedCharacter E χ)).right = 1 := by
        obtain ⟨xA, hxA⟩ := x.property
        rw [← hxA]
        rfl
      have hright :=
        congrArg SemidirectProduct.right hxb
      rw [hC] at hright
      have hright' : b.right = a.1.right := by
        simpa [hxRight] using hright
      rw [hright']
      exact a.property
    let xPullback : ambientLiftPullback L χ :=
      ⟨x, ambientNormal_le_liftPullback L χ x.property⟩
    let xRestricted :
        (restrictedAmbientTriple L χ).normalSubgroup :=
      ⟨xPullback, x.property⟩
    let bPullback : intermediateLiftPullback L d χ :=
      ⟨b, hbPullback⟩
    refine ⟨xRestricted, bPullback, ?_⟩
    apply Subtype.ext
    change
      (x : _) *
          oldEmbedding d χ b =
        a.1
    rw [← hC]
    exact hxb
  intersection_eq := by
    ext a
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := ha.2
      have hbOldNormal :
          b.1 ∈
            (oldIntermediateTriple d χ).normalSubgroup := by
        apply C.mem_rightNormal_of_embedding_mem_leftNormal
        rw [hC]
        have hcoe :=
          congrArg Subtype.val hb
        rw [restrictedSemidirectEmbedding_coe] at hcoe
        rw [hcoe]
        exact ha.1
      exact ⟨b, hbOldNormal, hb⟩
    · rintro ⟨b, hb, hba⟩
      refine ⟨?_, ⟨b, hba⟩⟩
      · have hbImage :
            oldEmbedding d χ b.1 ∈
              (oldAmbientTriple E S χ).normalSubgroup := by
          rw [← hC]
          exact C.embedding_rightNormal_mem_leftNormal
            ⟨b.1, hb⟩
        have hcoe :=
          congrArg Subtype.val hba
        rw [restrictedSemidirectEmbedding_coe] at hcoe
        change
          a.1 ∈
            (oldAmbientTriple E S χ).normalSubgroup
        rw [← hcoe]
        exact hbImage
  factor_agreement := by
    intro b c
    simpa [hC] using C.factor_agreement b.1 c.1
  scalar_agreement := by
    intro b hb
    have hbOld :
        C.embedding b.1 ∈
          Subgroup.centralizer
            ((oldAmbientTriple E S χ).normalSubgroup :
              Set
                (A ⋊[
                  PPrimeCharacterStabilizer.ambientAction]
                  PPrimeCharacterStabilizer
                    (E.sylowLift S)
                    (inflatedCharacter E χ))) := by
      rw [Subgroup.mem_centralizer_iff] at hb ⊢
      intro x hx
      let xPullback : ambientLiftPullback L χ :=
        ⟨x, ambientNormal_le_liftPullback L χ hx⟩
      have hxRestricted :
          xPullback ∈
            (restrictedAmbientTriple L χ).normalSubgroup :=
        hx
      have hcomm := hb xPullback hxRestricted
      have hcoe := congrArg Subtype.val hcomm
      simpa [hC] using hcoe
    simpa [hC] using C.scalar_agreement b.1 hbOld

end SylowAutomorphismLift
end InductiveMcKay
end McKayConjecture
