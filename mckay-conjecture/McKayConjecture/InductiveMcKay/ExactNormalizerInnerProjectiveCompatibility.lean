/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.InnerSemidirectProjective
import McKayConjecture.InductiveMcKay.ExactNormalizerProjectiveTableData

/-!
# Projective compatibility from inner normalizer lifts

Suppose every automorphism in the inertia group of a character is
conjugation by a chosen element of the exact Sylow normalizer.  The same
normalized lift then constructs associated projective representations on
both canonical semidirect products.  If the two matched characters have
the same scalar action on central normalizer elements, their factor sets
and centralizer scalars agree literally.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} {P : Sylow p G}

namespace EquivariantMcKayEquiv

/-- A normalized exact-normalizer lift of an inner character stabilizer,
together with matching central scalar actions, proves the projective
clause for that row. -/
theorem tripleCompatible_of_innerNormalizerLift
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p)
    (lift : PPrimeCharacterStabilizer P χ → SylowNormalizer P)
    (lift_one : lift 1 = 1)
    (lift_spec :
      ∀ a : PPrimeCharacterStabilizer P χ,
        PPrimeCharacterStabilizer.ambientAction a =
          MulAut.conj (lift a).1)
    (centralUnit : G → ℂˣ)
    (ambient_central_action :
      ∀ z : G, z ∈ Subgroup.center G →
        AssociatedExistence.realizationAction χ.1 z =
          scalarLinearEquiv ℂ χ.1.realization
            (centralUnit z))
    (local_central_action :
      ∀ z : SylowNormalizer P,
        z ∈ Subgroup.center (SylowNormalizer P) →
          AssociatedExistence.realizationAction (e χ).1 z =
            scalarLinearEquiv ℂ (e χ).1.realization
              (centralUnit z.1)) :
    e.toExactNormalizerLocalCorrespondence.TripleCompatible χ := by
  let d := e.toExactNormalizerLocalCorrespondence
  let liftAmbient :
      PPrimeCharacterStabilizer P χ → G :=
    fun a => (lift a).1
  have liftAmbient_one : liftAmbient 1 = 1 := by
    change (lift 1).1 = 1
    rw [lift_one]
    rfl
  have liftLocal_spec :
      ∀ a : PPrimeCharacterStabilizer P χ,
        d.stabilizerIntermediateAction χ a =
          MulAut.conj (lift a) := by
    intro a
    apply DFunLike.ext _ _
    intro n
    apply Subtype.ext
    change
      PPrimeCharacterStabilizer.ambientAction a n.1 =
        (lift a).1 * n.1 * (lift a).1⁻¹
    rw [lift_spec a]
    rfl
  let localCentralUnit : SylowNormalizer P → ℂˣ :=
    fun z => centralUnit z.1
  let leftProjective :=
    InnerSemidirectProjective.projectiveRepresentation
      PPrimeCharacterStabilizer.ambientAction χ.1
      liftAmbient lift_spec centralUnit
      ambient_central_action
  let rightProjective :=
    InnerSemidirectProjective.projectiveRepresentation
      (d.stabilizerIntermediateAction χ) (d.localCharacter χ).1
      lift liftLocal_spec localCentralUnit
      local_central_action
  letI : Nontrivial χ.1.realization :=
    CliffordRestriction.nontrivial_of_simple χ.1.realization
  letI : Nontrivial (d.localCharacter χ).1.realization :=
    CliffordRestriction.nontrivial_of_simple
      (d.localCharacter χ).1.realization
  let leftAssociated :
      AssociatedProjectiveRepresentation
        (EquivariantLocalCorrespondence.ambientTriple
          (P := P) χ)
        χ.1.realization leftProjective :=
    InnerSemidirectProjective.associated
      PPrimeCharacterStabilizer.ambientAction χ.1
      PPrimeCharacterStabilizer.character_invariant
      liftAmbient liftAmbient_one lift_spec centralUnit
      ambient_central_action
  let rightAssociated :
      AssociatedProjectiveRepresentation
        (d.intermediateTriple χ)
        (d.localCharacter χ).1.realization rightProjective :=
    InnerSemidirectProjective.associated
      (d.stabilizerIntermediateAction χ) (d.localCharacter χ).1
      (d.localCharacter_invariant χ)
      lift lift_one liftLocal_spec localCentralUnit
      local_central_action
  apply
    (show
      EquivariantLocalCorrespondence.ProjectiveCompatibilityWitness
        d χ χ.1.realization (d.localCharacter χ).1.realization from
      {
        leftProjective := leftProjective
        leftAssociated := leftAssociated
        rightProjective := rightProjective
        rightAssociated := rightAssociated
        factorAgreement := by
          intro h k
          change
            centralUnit
                (InnerSemidirectProjective.defect
                  PPrimeCharacterStabilizer.ambientAction
                  liftAmbient
                  (d.semidirectEmbedding χ h)
                  (d.semidirectEmbedding χ k)) =
              centralUnit
                (InnerSemidirectProjective.defect
                  (d.stabilizerIntermediateAction χ)
                  lift h k).1
          congr 1
        scalarAgreement := by
          intro h hh
          let ambientWord : G :=
            InnerSemidirectProjective.word
              PPrimeCharacterStabilizer.ambientAction
              liftAmbient (d.semidirectEmbedding χ h)
          let localWord : SylowNormalizer P :=
            InnerSemidirectProjective.word
              (d.stabilizerIntermediateAction χ) lift h
          have word_coe : ambientWord = localWord.1 := by
            rfl
          have ambientWord_mem_center :
              ambientWord ∈ Subgroup.center G := by
            rw [Subgroup.mem_center_iff]
            intro x
            have hcomm :=
              (Subgroup.mem_centralizer_iff.mp hh)
                (SemidirectProduct.inl x)
                (show
                  SemidirectProduct.inl x ∈
                    (EquivariantLocalCorrespondence.ambientTriple
                      (P := P) χ).normalSubgroup from
                  ⟨x, rfl⟩)
            have hleft := congrArg SemidirectProduct.left hcomm
            have hleft' :
                x * h.left.1 =
                  h.left.1 *
                    PPrimeCharacterStabilizer.ambientAction
                      h.right x := by
              simpa using hleft
            have haction :
                PPrimeCharacterStabilizer.ambientAction
                    h.right x =
                  (lift h.right).1 * x *
                    (lift h.right).1⁻¹ := by
              rw [lift_spec h.right]
              rfl
            change x * ambientWord = ambientWord * x
            rw [word_coe]
            change
              x * (h.left.1 * (lift h.right).1) =
                (h.left.1 * (lift h.right).1) * x
            rw [← mul_assoc, hleft', haction]
            group
          have localWord_mem_center :
              localWord ∈
                Subgroup.center (SylowNormalizer P) := by
            rw [Subgroup.mem_center_iff]
            intro n
            apply Subtype.ext
            change
              n.1 * localWord.1 =
                localWord.1 * n.1
            rw [← word_coe]
            exact
              Subgroup.mem_center_iff.mp
                ambientWord_mem_center n.1
          refine
            ⟨centralUnit ambientWord,
              ambient_central_action
                ambientWord ambientWord_mem_center, ?_⟩
          change
            AssociatedExistence.realizationAction
                (d.localCharacter χ).1 localWord =
              scalarLinearEquiv ℂ
                (d.localCharacter χ).1.realization
                (centralUnit ambientWord)
          rw [word_coe]
          exact
            local_central_action
              localWord localWord_mem_center
      }).tripleCompatible

end EquivariantMcKayEquiv

end InductiveMcKay
end McKayConjecture
