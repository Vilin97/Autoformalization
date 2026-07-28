/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorMatchedCharacterBijection
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveComparison

/-!
# Bundled factor-matched character-triple equivalences

This file separates the exact hypotheses needed for the ordinary character
correspondence from the extra hypotheses in a central isomorphism.

`FactorMatchedRestrictionGroupData` contains only injectivity, the ambient
product decomposition, and the exact normal-subgroup intersection.
`CompleteFactorMatchedProjectiveComparisonData` contains two associated
projective lifts and literal factor-set agreement.  Together they produce a
bundled `FactorMatchedIsomorphismWitness`, hence explicit ordinary and
prime-to-`p` character equivalences.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {A B : Type}
variable [Finite A] [Group A] [Finite B] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}

/-- The three ordinary subgroup conditions used by the factor-matched
character correspondence.  No centralizer containment is required. -/
structure FactorMatchedRestrictionGroupData
    (T : CharacterTriple A) (U : CharacterTriple B)
    (e : B →* A) : Prop where
  embedding_injective : Function.Injective e
  ambient_eq_product :
    ∀ a : A,
      ∃ x : T.normalSubgroup,
        ∃ h : B, (x : A) * e h = a
  intersection_eq :
    T.normalSubgroup ⊓ MonoidHom.range e =
      U.normalSubgroup.map e

namespace CentralRestrictionGroupData

/-- Forget the centralizer-containment field of the ordinary group package. -/
theorem toFactorMatchedRestrictionGroupData
    (g : CentralRestrictionGroupData T U e) :
    FactorMatchedRestrictionGroupData T U e where
  embedding_injective := g.embedding_injective
  ambient_eq_product := g.ambient_eq_product
  intersection_eq := g.intersection_eq

end CentralRestrictionGroupData

/-- The representation-theoretic data used by the factor-matched character
correspondence.  In particular, there is no scalar-agreement field. -/
structure CompleteFactorMatchedProjectiveComparisonData
    (T : CharacterTriple A) (U : CharacterTriple B)
    (e : B →* A) where
  leftSpace : Type
  rightSpace : Type
  [leftAddCommGroup : AddCommGroup leftSpace]
  [leftModule : Module ℂ leftSpace]
  [leftModuleFinite : Module.Finite ℂ leftSpace]
  [leftNontrivial : Nontrivial leftSpace]
  [rightAddCommGroup : AddCommGroup rightSpace]
  [rightModule : Module ℂ rightSpace]
  [rightModuleFinite : Module.Finite ℂ rightSpace]
  [rightNontrivial : Nontrivial rightSpace]
  leftProjective :
    ProjectiveRepresentation ℂ A leftSpace
  leftAssociated :
    AssociatedProjectiveRepresentation
      T leftSpace leftProjective
  rightProjective :
    ProjectiveRepresentation ℂ B rightSpace
  rightAssociated :
    AssociatedProjectiveRepresentation
      U rightSpace rightProjective
  factor_agreement :
    ∀ b c : B,
      leftProjective.factor (e b) (e c) =
        rightProjective.factor b c

/-- A factor-matched witness bundled with its two representation spaces and
their instances. -/
structure CompleteFactorMatchedIsomorphismWitness
    (T : CharacterTriple A) (U : CharacterTriple B) where
  leftSpace : Type
  rightSpace : Type
  [leftAddCommGroup : AddCommGroup leftSpace]
  [leftModule : Module ℂ leftSpace]
  [leftModuleFinite : Module.Finite ℂ leftSpace]
  [leftNontrivial : Nontrivial leftSpace]
  [rightAddCommGroup : AddCommGroup rightSpace]
  [rightModule : Module ℂ rightSpace]
  [rightModuleFinite : Module.Finite ℂ rightSpace]
  [rightNontrivial : Nontrivial rightSpace]
  witness :
    FactorMatchedIsomorphismWitness
      T U leftSpace rightSpace

namespace CompleteFactorMatchedProjectiveComparisonData

/-- Add the three ordinary subgroup conditions to the projective comparison
and obtain the complete weak witness. -/
def toCompleteFactorMatchedIsomorphismWitness
    (d : CompleteFactorMatchedProjectiveComparisonData T U e)
    (g : FactorMatchedRestrictionGroupData T U e) :
    CompleteFactorMatchedIsomorphismWitness T U := by
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
          ambient_eq_product := g.ambient_eq_product
          intersection_eq := g.intersection_eq
          factor_agreement := d.factor_agreement } }

end CompleteFactorMatchedProjectiveComparisonData

namespace CompleteCentralProjectiveComparisonData

/-- Forget scalar agreement from a complete central projective comparison. -/
def toCompleteFactorMatchedProjectiveComparisonData
    (d : CompleteCentralProjectiveComparisonData T U e) :
    CompleteFactorMatchedProjectiveComparisonData T U e := by
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
      leftProjective := d.leftProjective
      leftAssociated := d.leftAssociated
      rightProjective := d.rightProjective
      rightAssociated := d.rightAssociated
      factor_agreement := d.factor_agreement }

end CompleteCentralProjectiveComparisonData

namespace CompleteFactorMatchedIsomorphismWitness

/-- The explicit equivalence of all irreducible characters lying over the
two distinguished normal characters. -/
def irreducibleCharactersOverEquiv
    (C : CompleteFactorMatchedIsomorphismWitness T U) :
    CliffordCorrespondence.IrreducibleCharactersOverAlong
        T.normalSubgroup.subtype T.character ≃
      CliffordCorrespondence.IrreducibleCharactersOverAlong
        U.normalSubgroup.subtype U.character := by
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  exact C.witness.irreducibleCharactersOverEquiv

/-- The explicit equivalence on the prime-to-`p` character subtypes. -/
def pPrimeIrreducibleCharactersOverEquiv
    {p : ℕ} (hp : p.Prime)
    (C : CompleteFactorMatchedIsomorphismWitness T U)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character ≃
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p U.normalSubgroup.subtype U.character := by
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  exact C.witness.pPrimeIrreducibleCharactersOverEquiv hp hT hU

end CompleteFactorMatchedIsomorphismWitness

namespace CompleteFactorMatchedProjectiveComparisonData

/-- Directly construct the ordinary character equivalence from the
projective comparison and the three subgroup conditions. -/
def irreducibleCharactersOverEquiv
    (d : CompleteFactorMatchedProjectiveComparisonData T U e)
    (g : FactorMatchedRestrictionGroupData T U e) :
    CliffordCorrespondence.IrreducibleCharactersOverAlong
        T.normalSubgroup.subtype T.character ≃
      CliffordCorrespondence.IrreducibleCharactersOverAlong
        U.normalSubgroup.subtype U.character :=
  (d.toCompleteFactorMatchedIsomorphismWitness g).irreducibleCharactersOverEquiv

/-- Directly construct the prime-to-`p` character equivalence from the
projective comparison and the three subgroup conditions. -/
def pPrimeIrreducibleCharactersOverEquiv
    {p : ℕ} (hp : p.Prime)
    (d : CompleteFactorMatchedProjectiveComparisonData T U e)
    (g : FactorMatchedRestrictionGroupData T U e)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character ≃
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p U.normalSubgroup.subtype U.character :=
  (d.toCompleteFactorMatchedIsomorphismWitness g).pPrimeIrreducibleCharactersOverEquiv
    hp hT hU

end CompleteFactorMatchedProjectiveComparisonData

end InductiveMcKay
end McKayConjecture
