/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleRestrictionWitness

/-!
# Central witnesses from independent projective comparisons

A central isomorphism of character triples consists of two independent
associated projective representations, equality of their factor sets along
the chosen embedding, equality of their scalar actions on the relevant
centralizer, and four ordinary group conditions.

`CompleteCentralProjectiveComparisonData` bundles precisely the
representation-theoretic part.  Together with
`CentralRestrictionGroupData`, it constructs a complete central-isomorphism
witness.  Unlike literal projective restriction, the two representation
spaces are independent, so no equality of character degrees is imposed.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]

/-- The projective-representation part of a central isomorphism for a fixed
embedding.  The two associated representations may have unrelated
dimensions. -/
structure CompleteCentralProjectiveComparisonData
    (T : CharacterTriple A) (U : CharacterTriple B)
    (e : B →* A) where
  /-- Representation space on the left. -/
  leftSpace : Type
  /-- Representation space on the right. -/
  rightSpace : Type
  [leftAddCommGroup : AddCommGroup leftSpace]
  [leftModule : Module ℂ leftSpace]
  [leftModuleFinite : Module.Finite ℂ leftSpace]
  [leftNontrivial : Nontrivial leftSpace]
  [rightAddCommGroup : AddCommGroup rightSpace]
  [rightModule : Module ℂ rightSpace]
  [rightModuleFinite : Module.Finite ℂ rightSpace]
  [rightNontrivial : Nontrivial rightSpace]
  /-- Projective representation associated with the left triple. -/
  leftProjective :
    ProjectiveRepresentation ℂ A leftSpace
  /-- Association of the left projective representation. -/
  leftAssociated :
    AssociatedProjectiveRepresentation
      T leftSpace leftProjective
  /-- Projective representation associated with the right triple. -/
  rightProjective :
    ProjectiveRepresentation ℂ B rightSpace
  /-- Association of the right projective representation. -/
  rightAssociated :
    AssociatedProjectiveRepresentation
      U rightSpace rightProjective
  /-- Equality of factor sets after pullback along the embedding. -/
  factor_agreement :
    ∀ h k : B,
      leftProjective.factor (e h) (e k) =
        rightProjective.factor h k
  /-- Equality of the two scalar actions over the left centralizer. -/
  scalar_agreement :
    ∀ h : B,
      e h ∈
          Subgroup.centralizer
            (T.normalSubgroup : Set A) →
        ∃ c : ℂˣ,
          leftProjective.operator (e h) =
              scalarLinearEquiv ℂ leftSpace c ∧
            rightProjective.operator h =
              scalarLinearEquiv ℂ rightSpace c

namespace CompleteCentralProjectiveComparisonData

variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}

/-- Add the ordinary group conditions to an independent projective
comparison and obtain a complete central-isomorphism witness. -/
def toCompleteCentralIsomorphismWitness
    (d : CompleteCentralProjectiveComparisonData T U e)
    (g : CentralRestrictionGroupData T U e) :
    CompleteCentralIsomorphismWitness T U := by
  letI := d.leftAddCommGroup
  letI := d.leftModule
  letI := d.leftModuleFinite
  letI := d.leftNontrivial
  letI := d.rightAddCommGroup
  letI := d.rightModule
  letI := d.rightModuleFinite
  letI := d.rightNontrivial
  exact
    { leftSpace := d.leftSpace
      rightSpace := d.rightSpace
      witness :=
        { leftProjective := d.leftProjective
          leftAssociated := d.leftAssociated
          rightProjective := d.rightProjective
          rightAssociated := d.rightAssociated
          embedding := e
          embedding_injective := g.embedding_injective
          centralizer_le := g.centralizer_le
          ambient_eq_product := g.ambient_eq_product
          intersection_eq := g.intersection_eq
          factor_agreement := d.factor_agreement
          scalar_agreement := d.scalar_agreement } }

@[simp]
theorem toCompleteCentralIsomorphismWitness_embedding
    (d : CompleteCentralProjectiveComparisonData T U e)
    (g : CentralRestrictionGroupData T U e) :
    (d.toCompleteCentralIsomorphismWitness g).embedding = e :=
  rfl

end CompleteCentralProjectiveComparisonData

end InductiveMcKay
end McKayConjecture
