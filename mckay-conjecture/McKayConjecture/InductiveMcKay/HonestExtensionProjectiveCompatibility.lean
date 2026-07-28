/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.ExactNormalizerProjectiveTableData
import McKayConjecture.InductiveMcKay.HonestExtensionCentralWitness
import McKayConjecture.CharacterTriple.ProjectiveObstructionExtension

/-!
# Projective compatibility from honest semidirect extensions

This file gives the reduced inductive-McKay interface for the factor-one
construction in `HonestExtensionCentralWitness`.  Once the two matched normal
characters extend honestly to their canonical semidirect products, only the
cross-multiplied centralizer value identity remains.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {G : Type} [Group G] [Finite G] {p : ℕ}
variable {P : Sylow p G}

namespace EquivariantLocalCorrespondence

/-- Honest extensions of both canonical semidirect characters, with matching
normalized values over the canonical embedding, imply the projective clause
of the local inductive McKay condition. -/
theorem tripleCompatible_of_honestExtensions
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p)
    (ψ :
      IrreducibleCharacter
        (G ⋊[PPrimeCharacterStabilizer.ambientAction]
          PPrimeCharacterStabilizer P χ))
    (ξ :
      IrreducibleCharacter
        (d.intermediate ⋊[d.stabilizerIntermediateAction χ]
          PPrimeCharacterStabilizer P χ))
    (hψ :
      IrreducibleCharacter.IsExtensionAlong
        (ambientTriple (P := P) χ).normalSubgroup.subtype
        (ambientTriple (P := P) χ).character ψ)
    (hξ :
      IrreducibleCharacter.IsExtensionAlong
        (d.intermediateTriple χ).normalSubgroup.subtype
        (d.intermediateTriple χ).character ξ)
    (centralizer_cross :
      ∀ h :
        d.intermediate ⋊[d.stabilizerIntermediateAction χ]
          PPrimeCharacterStabilizer P χ,
        d.semidirectEmbedding χ h ∈
            Subgroup.centralizer
              ((ambientTriple (P := P) χ).normalSubgroup :
                Set
                  (G ⋊[PPrimeCharacterStabilizer.ambientAction]
                    PPrimeCharacterStabilizer P χ)) →
          ψ.values (d.semidirectEmbedding χ h) * (ξ.degree : ℂ) =
            ξ.values h * (ψ.degree : ℂ)) :
    d.TripleCompatible χ := by
  have hleft :
      IrreducibleCharacter.extensionCharacterTriple hψ =
        ambientTriple (P := P) χ :=
    IrreducibleCharacter.extensionCharacterTriple_eq ψ hψ
  have hright :
      IrreducibleCharacter.extensionCharacterTriple hξ =
        d.intermediateTriple χ :=
    IrreducibleCharacter.extensionCharacterTriple_eq ξ hξ
  let groupData :
      CentralRestrictionGroupData
        (IrreducibleCharacter.extensionCharacterTriple hψ)
        (IrreducibleCharacter.extensionCharacterTriple hξ)
        (d.semidirectEmbedding χ) := by
    rw [hleft, hright]
    exact
      { embedding_injective := d.semidirectEmbedding_injective χ
        centralizer_le :=
          d.centralizer_le_semidirectEmbedding_range χ
        ambient_eq_product :=
          d.ambient_eq_normal_mul_semidirectEmbedding χ
        intersection_eq :=
          d.normal_inf_embedding_range χ }
  have centralizer_cross' :
      ∀ h :
        d.intermediate ⋊[d.stabilizerIntermediateAction χ]
          PPrimeCharacterStabilizer P χ,
        d.semidirectEmbedding χ h ∈
            Subgroup.centralizer
              ((IrreducibleCharacter.extensionCharacterTriple hψ).normalSubgroup :
                Set
                  (G ⋊[PPrimeCharacterStabilizer.ambientAction]
                    PPrimeCharacterStabilizer P χ)) →
          ψ.values (d.semidirectEmbedding χ h) * (ξ.degree : ℂ) =
            ξ.values h * (ψ.degree : ℂ) := by
    intro h hh
    apply centralizer_cross h
    simpa only [hleft] using hh
  let C :=
    completeCentralIsomorphismWitnessOfExtensions
      hψ hξ (d.semidirectEmbedding χ) groupData centralizer_cross'
  have hCembedding :
      C.embedding = d.semidirectEmbedding χ := by
    dsimp only [C]
    exact
      completeCentralIsomorphismWitnessOfExtensions_embedding
        hψ hξ (d.semidirectEmbedding χ) groupData centralizer_cross'
  unfold TripleCompatible
  cases hleft
  cases hright
  refine
    ⟨C.leftSpace, C.rightSpace,
      C.leftAddCommGroup, C.leftModule, C.leftModuleFinite,
      C.leftNontrivial, C.rightAddCommGroup, C.rightModule,
      C.rightModuleFinite, C.rightNontrivial, C.witness, ?_⟩
  exact hCembedding

end EquivariantLocalCorrespondence

/-- Repackage the existential `TripleCompatible` predicate as the concrete
row datum expected by an exact-normalizer projective table. -/
theorem ExactNormalizerProjectiveRowData.nonempty_ofTripleCompatible
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p)
    (h :
      e.toExactNormalizerLocalCorrespondence.TripleCompatible χ) :
    Nonempty (ExactNormalizerProjectiveRowData e χ) := by
  have hp :
      e.toExactNormalizerLocalCorrespondence.ProjectivelyCompatible χ :=
    (EquivariantLocalCorrespondence.projectivelyCompatible_iff_tripleCompatible
      e.toExactNormalizerLocalCorrespondence χ).2 h
  obtain
    ⟨V, W, instVAdd, instVModule, instVFinite, instVNontrivial,
      instWAdd, instWModule, instWFinite, instWNontrivial, ⟨witness⟩⟩ :=
    hp
  refine ⟨?_⟩
  exact
    { leftSpace := V
      rightSpace := W
      leftAddCommGroup := instVAdd
      leftModule := instVModule
      leftModuleFinite := instVFinite
      leftNontrivial := instVNontrivial
      rightAddCommGroup := instWAdd
      rightModule := instWModule
      rightModuleFinite := instWFinite
      rightNontrivial := instWNontrivial
      witness := witness }

/-- Choose the concrete spaces and reduced witness supplied by
`TripleCompatible`. -/
noncomputable def ExactNormalizerProjectiveRowData.ofTripleCompatible
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p)
    (h :
      e.toExactNormalizerLocalCorrespondence.TripleCompatible χ) :
    ExactNormalizerProjectiveRowData e χ :=
  Classical.choice
    (ExactNormalizerProjectiveRowData.nonempty_ofTripleCompatible e χ h)

end InductiveMcKay
end McKayConjecture
