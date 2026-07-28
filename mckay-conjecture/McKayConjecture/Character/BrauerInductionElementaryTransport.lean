/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionTransitivity
import McKayConjecture.Character.ElementaryBrauerInductionReduction
import McKayConjecture.Character.Transport

/-!
# Transporting elementary induction terms through subgroup inclusions

A displayed `p`-elementary decomposition transports across a group
equivalence.  Applying this to the canonical equivalence between a
subgroup of `H` and its image in `G` turns every elementary induction term
for `H` into an elementary induction term for `G`.

Together with transitivity of induction, the induced class function of
the transported term is exactly the result of inducing the original
term through `H`.
-/

noncomputable section

namespace McKayConjecture

universe u v

namespace PElementaryDecomposition

variable {p : ℕ}
variable {E : Type u} {F : Type v}
variable [Group E] [Group F]

/-- Transport a displayed elementary direct-product decomposition across
a group equivalence. -/
def mapEquiv
    (D : PElementaryDecomposition p E)
    (e : E ≃* F) :
    PElementaryDecomposition p F := by
  let eC :
      D.cyclicPart ≃*
        D.cyclicPart.map e.toMonoidHom :=
    e.subgroupMap D.cyclicPart
  let eP :
      D.pPart ≃*
        D.pPart.map e.toMonoidHom :=
    e.subgroupMap D.pPart
  let productEquiv :
      (D.cyclicPart.map e.toMonoidHom) ×
          (D.pPart.map e.toMonoidHom) ≃*
        F :=
    ((MulEquiv.prodCongr eC eP).symm.trans
      D.multiplicationEquiv).trans e
  have hproduct :
      (fun z :
          (D.cyclicPart.map e.toMonoidHom) ×
            (D.pPart.map e.toMonoidHom) =>
          (z.1 : F) * (z.2 : F)) =
        productEquiv := by
    funext z
    apply e.symm.injective
    simp only [map_mul, productEquiv,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change
      e.symm (z.1 : F) * e.symm (z.2 : F) =
        ((eC.symm z.1 : D.cyclicPart) : E) *
          ((eP.symm z.2 : D.pPart) : E)
    congr 1
  exact
    { cyclicPart :=
        D.cyclicPart.map e.toMonoidHom
      pPart :=
        D.pPart.map e.toMonoidHom
      cyclic :=
        eC.isCyclic.mp D.cyclic
      cyclicPart_coprime := by
        rw [← Nat.card_congr eC.toEquiv]
        exact D.cyclicPart_coprime
      isPGroup :=
        D.isPGroup.of_equiv eP
      cyclicPart_normal :=
        D.cyclicPart_normal.map
          e.toMonoidHom e.surjective
      pPart_normal :=
        D.pPart_normal.map
          e.toMonoidHom e.surjective
      complementary := by
        change
          Function.Bijective
            (fun z :
                (D.cyclicPart.map e.toMonoidHom) ×
                  (D.pPart.map e.toMonoidHom) =>
              (z.1 : F) * (z.2 : F))
        rw [hproduct]
        exact productEquiv.bijective }

end PElementaryDecomposition

namespace ElementaryInductionTerm

variable {G : Type} [Group G] [Finite G]

noncomputable local instance elementaryTransportFintypeG :
    Fintype G :=
  Fintype.ofFinite _

noncomputable local instance elementaryTransportFintypeSubgroup
    (H : Subgroup G) :
    Fintype H :=
  Fintype.ofFinite _

/-- Map an elementary induction term for an intermediate subgroup into
the ambient group. -/
def mapSubtype
    (H : Subgroup G)
    (t : ElementaryInductionTerm H) :
    ElementaryInductionTerm G := by
  let e :
      t.subgroup ≃*
        t.subgroup.map H.subtype :=
    t.subgroup.equivMapOfInjective
      H.subtype H.subtype_injective
  exact
    { prime := t.prime
      prime_isPrime := t.prime_isPrime
      subgroup := t.subgroup.map H.subtype
      decomposition :=
        t.decomposition.mapEquiv e
      character :=
        t.character.comap e.symm }

omit [Finite G] in
@[simp]
theorem mapSubtype_subgroup
    (H : Subgroup G)
    (t : ElementaryInductionTerm H) :
    (t.mapSubtype H).subgroup =
      t.subgroup.map H.subtype :=
  rfl

omit [Finite G] in
/-- The character in a mapped term is the canonical transport of the
original character. -/
theorem mapSubtype_character_toClassFunction
    (H : Subgroup G)
    (t : ElementaryInductionTerm H) :
    (t.mapSubtype H).character.toClassFunction =
      ClassFunction.mapSubtypeClassFunction
        H t.subgroup t.character.toClassFunction := by
  ext x
  rfl

/-- Inducing a mapped elementary term is the same as first inducing the
original term to `H` and then inducing through `H`. -/
theorem mapSubtype_inducedClassFunction
    (H : Subgroup G)
    (t : ElementaryInductionTerm H) :
    (t.mapSubtype H).inducedClassFunction =
      ClassFunction.induce H t.inducedClassFunction := by
  change
    ClassFunction.induce
        (t.subgroup.map H.subtype)
        (t.mapSubtype H).character.toClassFunction =
      ClassFunction.induce H
        (ClassFunction.induce t.subgroup
          t.character.toClassFunction)
  rw [mapSubtype_character_toClassFunction]
  exact
    (ClassFunction.induce_induce_subgroup
      H t.subgroup t.character.toClassFunction).symm

end ElementaryInductionTerm
end McKayConjecture
