/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CommonCentralCoverSemidirectProjective
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveTraceComparison
import McKayConjecture.InductiveMcKay.ExactNormalizerProjectiveTableData
import McKayConjecture.InductiveMcKay.InnerCharacterStabilizer

/-!
# Exact-normalizer compatibility from a common central cover

Suppose a group `L` covers the character stabilizer and embeds in an
overgroup `Ω` containing the ambient group.  The exact Sylow normalizer
also embeds in `L`, and both actions are conjugation through these
embeddings.  Extension characters on `Ω` and `L` whose normalized values
agree on the cover kernel then induce associated projective
representations with identical factors and centralizer scalars.

This is the reusable interface for the `GL(2,5)` construction: `Ω` is the
full general linear group and `L` is the inverse image of a Sylow
stabilizer.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open CharacterTriple.CommonCentralCoverSemidirectProjective

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} {P : Sylow p G}

namespace EquivariantMcKayEquiv

/-- A common central cover with matched extension characters proves the
projective clause for one exact-normalizer row. -/
theorem tripleCompatible_of_commonCentralCover
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p)
    {L : Type v} [Group L] [Finite L]
    {Ω : Type w} [Group Ω] [Finite Ω]
    (cover :
      L →* PPrimeCharacterStabilizer P χ)
    (cover_surjective : Function.Surjective cover)
    (ambientEmbedding : G →* Ω)
    (coverEmbedding : L →* Ω)
    (localEmbedding :
      e.toExactNormalizerLocalCorrespondence.intermediate →* L)
    (embedding_square :
      ∀ n : e.toExactNormalizerLocalCorrespondence.intermediate,
        coverEmbedding (localEmbedding n) =
          ambientEmbedding n.1)
    (cover_localEmbedding :
      ∀ n : e.toExactNormalizerLocalCorrespondence.intermediate,
        cover (localEmbedding n) =
          normalizerInnerCharacterStabilizerHom P χ n)
    (ambient_conjugates :
      ∀ (l : L) (g : G),
        ambientEmbedding
            (PPrimeCharacterStabilizer.ambientAction
              (cover l) g) =
          coverEmbedding l * ambientEmbedding g *
            (coverEmbedding l)⁻¹)
    (local_conjugates :
      ∀ (l : L)
        (n : e.toExactNormalizerLocalCorrespondence.intermediate),
        localEmbedding
            (e.toExactNormalizerLocalCorrespondence
              |>.stabilizerIntermediateAction χ
                (cover l) n) =
          l * localEmbedding n * l⁻¹)
    (kernel_central_ambient :
      ∀ l : L, l ∈ cover.ker →
        coverEmbedding l ∈ Subgroup.center Ω)
    (kernel_central_local :
      ∀ l : L, l ∈ cover.ker →
        l ∈ Subgroup.center L)
    (ambientExtension : IrreducibleCharacter Ω)
    (ambientExtends :
      IrreducibleCharacter.IsExtensionAlong
        ambientEmbedding χ.1 ambientExtension)
    (localExtension : IrreducibleCharacter L)
    (localExtends :
      IrreducibleCharacter.IsExtensionAlong
        localEmbedding
          (e.toExactNormalizerLocalCorrespondence.localCharacter χ).1
          localExtension)
    (kernel_cross :
      ∀ l : L, l ∈ cover.ker →
        ambientExtension.values (coverEmbedding l) *
            (localExtension.degree : ℂ) =
          localExtension.values l *
            (ambientExtension.degree : ℂ)) :
    e.toExactNormalizerLocalCorrespondence.TripleCompatible χ := by
  let d := e.toExactNormalizerLocalCorrespondence
  let leftProjective :=
    CommonCentralCoverSemidirectProjective.projectiveRepresentation
      (φ := PPrimeCharacterStabilizer.ambientAction)
      (cover := cover)
      (cover_surjective := cover_surjective)
      (normalEmbedding := ambientEmbedding)
      (coverEmbedding := coverEmbedding)
      (cover_conjugates := ambient_conjugates)
      (extensionCharacter := ambientExtension)
      (kernel_central := kernel_central_ambient)
  let rightProjective :=
    CommonCentralCoverSemidirectProjective.projectiveRepresentation
      (φ := d.stabilizerIntermediateAction χ)
      (cover := cover)
      (cover_surjective := cover_surjective)
      (normalEmbedding := localEmbedding)
      (coverEmbedding := MonoidHom.id L)
      (cover_conjugates := local_conjugates)
      (extensionCharacter := localExtension)
      (kernel_central := by
        intro l hl
        simpa using kernel_central_local l hl)
  let leftAssociated :=
    CommonCentralCoverSemidirectProjective.associated
      PPrimeCharacterStabilizer.ambientAction χ.1
      PPrimeCharacterStabilizer.character_invariant
      cover cover_surjective ambientEmbedding coverEmbedding
      ambient_conjugates ambientExtension ambientExtends
      kernel_central_ambient
  let rightAssociated :=
    CommonCentralCoverSemidirectProjective.associated
      (d.stabilizerIntermediateAction χ) (d.localCharacter χ).1
      (d.localCharacter_invariant χ)
      cover cover_surjective localEmbedding (MonoidHom.id L)
      local_conjugates localExtension
      (by
        change
          IrreducibleCharacter.IsExtensionAlong
            localEmbedding
              (e.toExactNormalizerLocalCorrespondence
                |>.localCharacter χ).1
              localExtension
        exact localExtends)
      (by
        intro l hl
        simpa using kernel_central_local l hl)
  have factorAgreement :
      ∀ h k :
        SylowNormalizer P ⋊[d.stabilizerIntermediateAction χ]
          PPrimeCharacterStabilizer P χ,
        leftProjective.factor (d.semidirectEmbedding χ h)
            (d.semidirectEmbedding χ k) =
          rightProjective.factor h k := by
    intro h k
    let defect :=
      sectionDefect cover cover_surjective h.right k.right
    have hdefect : defect ∈ cover.ker :=
      sectionDefect_mem_ker cover cover_surjective h.right k.right
    change
      ambientExtension.centralUnit
          (coverEmbedding defect)
          (kernel_central_ambient defect hdefect) =
        localExtension.centralUnit defect
          (kernel_central_local defect hdefect)
    exact
      ambientExtension.centralUnit_eq_of_cross
        localExtension (coverEmbedding defect) defect
        (kernel_central_ambient defect hdefect)
        (kernel_central_local defect hdefect)
        (kernel_cross defect hdefect)
  apply
    (show
      EquivariantLocalCorrespondence.ProjectiveCompatibilityWitness
        d χ ambientExtension.realization localExtension.realization from
      { leftProjective := leftProjective
        leftAssociated := leftAssociated
        rightProjective := rightProjective
        rightAssociated := rightAssociated
        factorAgreement := factorAgreement
        scalarAgreement := by
          intro h hh
          let coveredWord : L :=
            localEmbedding h.left *
              normalizedSection cover cover_surjective h.right
          have coveredWord_mem_ker : coveredWord ∈ cover.ker := by
            rw [MonoidHom.mem_ker]
            rw [map_mul, cover_localEmbedding,
              cover_normalizedSection]
            apply Subtype.ext
            apply Subtype.ext
            apply DFunLike.ext _ _
            intro g
            have hcomm :=
              (Subgroup.mem_centralizer_iff.mp hh)
                (SemidirectProduct.inl g)
                (show
                  SemidirectProduct.inl g ∈
                    (EquivariantLocalCorrespondence.ambientTriple
                      (P := P) χ).normalSubgroup from
                  ⟨g, rfl⟩)
            have hleft := congrArg SemidirectProduct.left hcomm
            change
              g * h.left.1 =
                h.left.1 *
                  PPrimeCharacterStabilizer.ambientAction
                    h.right g at hleft
            change
              h.left.1 *
                    PPrimeCharacterStabilizer.ambientAction
                      h.right g *
                  h.left.1⁻¹ =
                g
            rw [← hleft]
            group
          have word_square :
              word PPrimeCharacterStabilizer.ambientAction
                  cover cover_surjective ambientEmbedding coverEmbedding
                  (d.semidirectEmbedding χ h) =
                coverEmbedding coveredWord := by
            change
              ambientEmbedding h.left.1 *
                  coverEmbedding
                    (normalizedSection cover cover_surjective h.right) =
                coverEmbedding
                  (localEmbedding h.left *
                    normalizedSection cover cover_surjective h.right)
            rw [map_mul, embedding_square]
          let commonUnit : ℂˣ :=
            ambientExtension.centralUnit
              (coverEmbedding coveredWord)
              (kernel_central_ambient
                coveredWord coveredWord_mem_ker)
          refine ⟨commonUnit, ?_, ?_⟩
          · change
              AssociatedExistence.realizationAction ambientExtension
                  (word PPrimeCharacterStabilizer.ambientAction
                    cover cover_surjective ambientEmbedding coverEmbedding
                    (d.semidirectEmbedding χ h)) =
                scalarLinearEquiv ℂ ambientExtension.realization
                  commonUnit
            rw [word_square]
            exact
              ambientExtension.realizationAction_eq_centralUnit
                (coverEmbedding coveredWord)
                (kernel_central_ambient
                  coveredWord coveredWord_mem_ker)
          · change
              AssociatedExistence.realizationAction localExtension
                  coveredWord =
                scalarLinearEquiv ℂ localExtension.realization
                  commonUnit
            exact
              ambientExtension
                |>.realizationAction_eq_commonCentralUnit_of_cross
                  localExtension
                  (coverEmbedding coveredWord) coveredWord
                  (kernel_central_ambient
                    coveredWord coveredWord_mem_ker)
                  (kernel_central_local
                    coveredWord coveredWord_mem_ker)
                  (kernel_cross
                    coveredWord coveredWord_mem_ker) }).tripleCompatible

end EquivariantMcKayEquiv

end InductiveMcKay
end McKayConjecture
