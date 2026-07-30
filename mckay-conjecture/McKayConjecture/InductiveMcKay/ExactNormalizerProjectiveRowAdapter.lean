/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CanonicalProjective
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveTraceComparison
import McKayConjecture.InductiveMcKay.ExactNormalizerProjectiveTableData

/-!
# Exact-normalizer projective rows from factors and traces

For associated projective representations on the two canonical
semidirect products, literal factor-set agreement leaves one scalar
condition.  Schur's lemma turns that condition into a numerical one:
cross-multiplied equality of the two projective traces.

This file connects that existing trace criterion directly to
`ProjectiveCompatibilityWitness` and hence to
`ExactNormalizerProjectiveRowData`.  A specialization to the canonical
associated lifts makes both association certificates automatic.  The
factor and trace identities remain explicit rowwise obligations.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} {P : Sylow p G}

namespace EquivariantLocalCorrespondence

/-- The automatic group-theoretic comparison data for the canonical
embedding of an equivariant local correspondence's semidirect products. -/
theorem semidirectCentralRestrictionGroupData
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    CentralRestrictionGroupData
      (ambientTriple (P := P) χ)
      (d.intermediateTriple χ)
      (d.semidirectEmbedding χ) where
  embedding_injective :=
    d.semidirectEmbedding_injective χ
  centralizer_le :=
    d.centralizer_le_semidirectEmbedding_range χ
  ambient_eq_product :=
    d.ambient_eq_normal_mul_semidirectEmbedding χ
  intersection_eq :=
    d.normal_inf_embedding_range χ

/-- Construct the reduced projective compatibility witness from two
associated lifts, literal factor agreement, and cross-multiplied equality
of their projective traces on the relevant centralizer.

The right-centralizer membership and the common scalar are derived
automatically. -/
def projectiveCompatibilityWitness_ofAssociatedFactorAgreementTraceCross
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p)
    {V W : Type}
    [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] [Nontrivial V]
    [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] [Nontrivial W]
    (leftProjective :
      ProjectiveRepresentation ℂ
        (G ⋊[PPrimeCharacterStabilizer.ambientAction]
          PPrimeCharacterStabilizer P χ) V)
    (leftAssociated :
      AssociatedProjectiveRepresentation
        (ambientTriple (P := P) χ) V leftProjective)
    (rightProjective :
      ProjectiveRepresentation ℂ
        (d.intermediate ⋊[d.stabilizerIntermediateAction χ]
          PPrimeCharacterStabilizer P χ) W)
    (rightAssociated :
      AssociatedProjectiveRepresentation
        (d.intermediateTriple χ) W rightProjective)
    (factorAgreement :
      ∀ h k :
        d.intermediate ⋊[d.stabilizerIntermediateAction χ]
          PPrimeCharacterStabilizer P χ,
        leftProjective.factor
            (d.semidirectEmbedding χ h)
            (d.semidirectEmbedding χ k) =
          rightProjective.factor h k)
    (traceCross :
      ∀ h :
        d.intermediate ⋊[d.stabilizerIntermediateAction χ]
          PPrimeCharacterStabilizer P χ,
        d.semidirectEmbedding χ h ∈
            Subgroup.centralizer
              ((ambientTriple (P := P) χ).normalSubgroup :
                Set
                  (G ⋊[PPrimeCharacterStabilizer.ambientAction]
                    PPrimeCharacterStabilizer P χ)) →
          LinearMap.trace ℂ V
                (leftProjective.operator
                  (d.semidirectEmbedding χ h) : V →ₗ[ℂ] V) *
              (Module.finrank ℂ W : ℂ) =
            LinearMap.trace ℂ W
                (rightProjective.operator h : W →ₗ[ℂ] W) *
              (Module.finrank ℂ V : ℂ)) :
    ProjectiveCompatibilityWitness d χ V W where
  leftProjective := leftProjective
  leftAssociated := leftAssociated
  rightProjective := rightProjective
  rightAssociated := rightAssociated
  factorAgreement := factorAgreement
  scalarAgreement := by
    intro h hh
    exact
      CompleteCentralProjectiveComparisonData.exists_common_scalar_of_trace_cross
        leftAssociated rightAssociated
        (d.semidirectEmbedding χ h) h hh
        (d.semidirectCentralRestrictionGroupData χ
          |>.mem_rightCentralizer_of_embedding_mem_leftCentralizer h hh)
        (traceCross h hh)

end EquivariantLocalCorrespondence

namespace ExactNormalizerProjectiveRowData

/-- Package chosen associated projective realizations, literal factor
agreement, and the numerical trace criterion directly as one
exact-normalizer projective row. -/
def ofAssociatedFactorAgreementTraceCross
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p)
    {V W : Type}
    [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] [Nontrivial V]
    [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] [Nontrivial W]
    (leftProjective :
      ProjectiveRepresentation ℂ
        (G ⋊[PPrimeCharacterStabilizer.ambientAction]
          PPrimeCharacterStabilizer P χ) V)
    (leftAssociated :
      AssociatedProjectiveRepresentation
        (EquivariantLocalCorrespondence.ambientTriple
          (P := P) χ) V leftProjective)
    (rightProjective :
      ProjectiveRepresentation ℂ
        (e.toExactNormalizerLocalCorrespondence.intermediate
          ⋊[(e.toExactNormalizerLocalCorrespondence
            |>.stabilizerIntermediateAction χ)]
          PPrimeCharacterStabilizer P χ) W)
    (rightAssociated :
      AssociatedProjectiveRepresentation
        (e.toExactNormalizerLocalCorrespondence.intermediateTriple χ)
        W rightProjective)
    (factorAgreement :
      ∀ h k :
        e.toExactNormalizerLocalCorrespondence.intermediate
          ⋊[(e.toExactNormalizerLocalCorrespondence
            |>.stabilizerIntermediateAction χ)]
          PPrimeCharacterStabilizer P χ,
        leftProjective.factor
            (e.toExactNormalizerLocalCorrespondence.semidirectEmbedding χ h)
            (e.toExactNormalizerLocalCorrespondence.semidirectEmbedding χ k) =
          rightProjective.factor h k)
    (traceCross :
      ∀ h :
        e.toExactNormalizerLocalCorrespondence.intermediate
          ⋊[(e.toExactNormalizerLocalCorrespondence
            |>.stabilizerIntermediateAction χ)]
          PPrimeCharacterStabilizer P χ,
        e.toExactNormalizerLocalCorrespondence.semidirectEmbedding χ h ∈
            Subgroup.centralizer
              ((EquivariantLocalCorrespondence.ambientTriple
                  (P := P) χ).normalSubgroup :
                Set
                  (G ⋊[PPrimeCharacterStabilizer.ambientAction]
                    PPrimeCharacterStabilizer P χ)) →
          LinearMap.trace ℂ V
                (leftProjective.operator
                  (e.toExactNormalizerLocalCorrespondence
                    |>.semidirectEmbedding χ h) : V →ₗ[ℂ] V) *
              (Module.finrank ℂ W : ℂ) =
            LinearMap.trace ℂ W
                (rightProjective.operator h : W →ₗ[ℂ] W) *
              (Module.finrank ℂ V : ℂ)) :
    ExactNormalizerProjectiveRowData e χ where
  leftSpace := V
  rightSpace := W
  witness :=
    e.toExactNormalizerLocalCorrespondence
      |>.projectiveCompatibilityWitness_ofAssociatedFactorAgreementTraceCross
        χ leftProjective leftAssociated rightProjective rightAssociated
        factorAgreement traceCross

/-- For the canonical associated lifts, one exact-normalizer row reduces
to literal equality of the two canonical factors on the inertia group and
cross-multiplied equality of their projective traces on the centralizer. -/
def ofCanonicalFactorAgreementTraceCross
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p)
    (factorAgreement :
      ∀ a b : PPrimeCharacterStabilizer P χ,
        AssociatedExistence.intertwinerFactor
              PPrimeCharacterStabilizer.ambientAction χ.1
              PPrimeCharacterStabilizer.character_invariant a b =
          AssociatedExistence.intertwinerFactor
              (e.toExactNormalizerLocalCorrespondence
                |>.stabilizerIntermediateAction χ)
              (e.toExactNormalizerLocalCorrespondence.localCharacter χ).1
              (e.toExactNormalizerLocalCorrespondence
                |>.localCharacter_invariant χ) a b)
    (traceCross :
      ∀ h :
        e.toExactNormalizerLocalCorrespondence.intermediate
          ⋊[(e.toExactNormalizerLocalCorrespondence
            |>.stabilizerIntermediateAction χ)]
          PPrimeCharacterStabilizer P χ,
        e.toExactNormalizerLocalCorrespondence.semidirectEmbedding χ h ∈
            Subgroup.centralizer
              ((EquivariantLocalCorrespondence.ambientTriple
                  (P := P) χ).normalSubgroup :
                Set
                  (G ⋊[PPrimeCharacterStabilizer.ambientAction]
                    PPrimeCharacterStabilizer P χ)) →
          LinearMap.trace ℂ χ.1.realization
                ((e.toExactNormalizerLocalCorrespondence
                  |>.canonicalAmbientProjective χ).operator
                    (e.toExactNormalizerLocalCorrespondence
                      |>.semidirectEmbedding χ h) :
                  χ.1.realization →ₗ[ℂ] χ.1.realization) *
              (Module.finrank ℂ
                (e.toExactNormalizerLocalCorrespondence.localCharacter χ).1.realization :
                  ℂ) =
            LinearMap.trace ℂ
                (e.toExactNormalizerLocalCorrespondence.localCharacter χ).1.realization
                ((e.toExactNormalizerLocalCorrespondence
                  |>.canonicalIntermediateProjective χ).operator h :
                  (e.toExactNormalizerLocalCorrespondence.localCharacter χ).1.realization
                    →ₗ[ℂ]
                  (e.toExactNormalizerLocalCorrespondence.localCharacter χ).1.realization) *
              (Module.finrank ℂ χ.1.realization : ℂ)) :
    ExactNormalizerProjectiveRowData e χ :=
  ofAssociatedFactorAgreementTraceCross e χ
    (e.toExactNormalizerLocalCorrespondence
      |>.canonicalAmbientProjective χ)
    (AssociatedExistence.associated
      PPrimeCharacterStabilizer.ambientAction χ.1
      PPrimeCharacterStabilizer.character_invariant)
    (e.toExactNormalizerLocalCorrespondence
      |>.canonicalIntermediateProjective χ)
    (AssociatedExistence.associated
      (e.toExactNormalizerLocalCorrespondence
        |>.stabilizerIntermediateAction χ)
      (e.toExactNormalizerLocalCorrespondence.localCharacter χ).1
      (e.toExactNormalizerLocalCorrespondence
        |>.localCharacter_invariant χ))
    (by
      intro h k
      exact factorAgreement h.right k.right)
    traceCross

end ExactNormalizerProjectiveRowData

end InductiveMcKay
end McKayConjecture
