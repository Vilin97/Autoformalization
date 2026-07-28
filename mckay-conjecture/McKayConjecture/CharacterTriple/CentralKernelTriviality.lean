/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.QuotientDescent
import McKayConjecture.CharacterTriple.CentralCorrespondence

/-!
# Triviality on matched central subgroups

A central isomorphism of character triples identifies the scalar by which
matched elements of the centralizer of the left normal subgroup act in the
two associated projective representations.  Consequently, the two normal
characters are simultaneously trivial on any pair of central subgroups
identified by the witness embedding.

This is the representation-level statement needed before descending a local
character correspondence through a central quotient.  It deliberately uses
`IrreducibleCharacter.TrivialOn`, rather than equality of character values at
the relevant elements.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace CharacterTriple
namespace CentralIsomorphismWitness

variable {A : Type u} {B : Type v}
  [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]

/-- An element central in the left normal subgroup, viewed in the left
ambient group, centralizes the whole left normal subgroup. -/
theorem normalCenterElement_mem_ambientCentralizer
    (z : Subgroup.center T.normalSubgroup) :
    ((z.1 : T.normalSubgroup) : A) ∈
      Subgroup.centralizer (T.normalSubgroup : Set A) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact congrArg Subtype.val
    ((Subgroup.mem_center_iff.mp z.2) ⟨x, hx⟩)

/-- Matched central elements act by one and the same scalar in the two
normal-subgroup characters of a central-isomorphism witness. -/
theorem normalCharacter_matchedCentral_scalar
    (C : CentralIsomorphismWitness T U V W)
    (x : T.normalSubgroup) (y : U.normalSubgroup)
    (hxy : C.embedding (y : B) = (x : A))
    (hx : x ∈ Subgroup.center T.normalSubgroup) :
    ∃ c : ℂˣ,
      T.character.values x =
          (c : ℂ) * (T.character.degree : ℂ) ∧
        U.character.values y =
          (c : ℂ) * (U.character.degree : ℂ) := by
  have hcentralizer :
      C.embedding (y : B) ∈
        Subgroup.centralizer
          (T.normalSubgroup : Set A) := by
    rw [hxy]
    exact normalCenterElement_mem_ambientCentralizer
      (T := T) ⟨x, hx⟩
  obtain ⟨c, hleft, hright⟩ :=
    C.scalar_agreement (y : B) hcentralizer
  refine ⟨c, ?_, ?_⟩
  · rw [← C.leftAssociated.traceFunction_normal x]
    change
      LinearMap.trace ℂ V
          (C.leftProjective.operator (x : A) :
            V →ₗ[ℂ] V) =
        (c : ℂ) * (T.character.degree : ℂ)
    have hleftx :
        C.leftProjective.operator (x : A) =
          scalarLinearEquiv ℂ V c := by
      rw [← hxy]
      exact hleft
    rw [hleftx]
    change
      LinearMap.trace ℂ V
          ((scalarLinearEquiv ℂ V c :
            V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) =
        (c : ℂ) * (T.character.degree : ℂ)
    have hscalar :
        ((scalarLinearEquiv ℂ V c :
            V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) =
          (c : ℂ) •
            (LinearMap.id : Module.End ℂ V) := by
      ext v
      simp
    rw [hscalar, map_smul, LinearMap.trace_id,
      C.leftAssociated.finrank_eq_character_degree]
    rfl
  · rw [← C.rightAssociated.traceFunction_normal y]
    change
      LinearMap.trace ℂ W
          (C.rightProjective.operator (y : B) :
            W →ₗ[ℂ] W) =
        (c : ℂ) * (U.character.degree : ℂ)
    rw [hright]
    have hscalar :
        ((scalarLinearEquiv ℂ W c :
            W ≃ₗ[ℂ] W) : W →ₗ[ℂ] W) =
          (c : ℂ) •
            (LinearMap.id : Module.End ℂ W) := by
      ext w
      simp
    rw [hscalar, map_smul, LinearMap.trace_id,
      C.rightAssociated.finrank_eq_character_degree]
    rfl

/-- Cross-multiplied central-character equality for matched central
elements.  Unlike a normalized quotient, this formulation never divides by
a character degree. -/
theorem normalCharacter_matchedCentral_cross
    (C : CentralIsomorphismWitness T U V W)
    (x : T.normalSubgroup) (y : U.normalSubgroup)
    (hxy : C.embedding (y : B) = (x : A))
    (hx : x ∈ Subgroup.center T.normalSubgroup) :
    T.character.values x *
        (U.character.degree : ℂ) =
      U.character.values y *
        (T.character.degree : ℂ) := by
  obtain ⟨c, hxvalue, hyvalue⟩ :=
    C.normalCharacter_matchedCentral_scalar
      x y hxy hx
  rw [hxvalue, hyvalue]
  ring

/-- A central character-triple witness preserves representation-level
triviality on matched central subgroups of its two normal subgroups.

The equivalence `eZ` points from the right subgroup to the left subgroup,
and `hcomm` says that this equivalence is literally induced by the ambient
embedding stored in the witness. -/
theorem normalCharacter_trivialOn_iff
    (C : CentralIsomorphismWitness T U V W)
    (ZT : Subgroup T.normalSubgroup)
    (ZU : Subgroup U.normalSubgroup)
    (hZT : ZT ≤ Subgroup.center T.normalSubgroup)
    (eZ : ZU ≃* ZT)
    (hcomm : ∀ z : ZU,
      C.embedding ((z.1 : U.normalSubgroup) : B) =
        ((eZ z : ZT).1 : T.normalSubgroup)) :
    T.character.TrivialOn ZT ↔
      U.character.TrivialOn ZU := by
  have hleft :
      T.character.TrivialOn ZT ↔
        FDRep.IsTrivialOn C.leftAssociated.fdRestriction ZT :=
    IrreducibleCharacter.trivialOn_iff_of_character_eq
      ZT T.character C.leftAssociated.fdRestriction
        C.leftAssociated.fdRestriction_character
  have hright :
      U.character.TrivialOn ZU ↔
        FDRep.IsTrivialOn C.rightAssociated.fdRestriction ZU :=
    IrreducibleCharacter.trivialOn_iff_of_character_eq
      ZU U.character C.rightAssociated.fdRestriction
        C.rightAssociated.fdRestriction_character
  rw [hleft, hright]
  constructor
  · intro htriv z
    let zT : ZT := eZ z
    have hzcentral :
        (zT.1 : T.normalSubgroup) ∈
          Subgroup.center T.normalSubgroup :=
      hZT zT.2
    have hzambient :
        C.embedding ((z.1 : U.normalSubgroup) : B) ∈
          Subgroup.centralizer (T.normalSubgroup : Set A) := by
      rw [hcomm z]
      exact normalCenterElement_mem_ambientCentralizer
        (T := T) ⟨zT.1, hzcentral⟩
    obtain ⟨c, hleftScalar, hrightScalar⟩ :=
      C.scalar_agreement
        ((z.1 : U.normalSubgroup) : B) hzambient
    have hleftRestrictionOne :
        C.leftAssociated.restriction
            (zT.1 : T.normalSubgroup) =
          1 := by
      ext v
      exact LinearMap.congr_fun (htriv zT) v
    have hleftOne :
        C.leftProjective.operator
            (C.embedding ((z.1 : U.normalSubgroup) : B)) =
          1 := by
      rw [hcomm z]
      rw [← C.leftAssociated.restriction_apply
        (zT.1 : T.normalSubgroup)]
      exact hleftRestrictionOne
    have hc : c = 1 := by
      apply scalarLinearEquiv_injective ℂ V
      rw [← hleftScalar, hleftOne]
      exact (map_one (scalarLinearEquiv ℂ V)).symm
    have hrightOne :
        C.rightProjective.operator
            ((z.1 : U.normalSubgroup) : B) =
          1 := by
      rw [hrightScalar, hc]
      exact map_one (scalarLinearEquiv ℂ W)
    apply LinearMap.ext
    intro w
    change
      C.rightAssociated.restriction
          (z.1 : U.normalSubgroup) w = w
    rw [C.rightAssociated.restriction_apply, hrightOne]
    rfl
  · intro htriv z
    let zU : ZU := eZ.symm z
    have hzcentral :
        (z.1 : T.normalSubgroup) ∈
          Subgroup.center T.normalSubgroup :=
      hZT z.2
    have hmatch :
        C.embedding ((zU.1 : U.normalSubgroup) : B) =
          (z.1 : T.normalSubgroup) := by
      simpa [zU] using hcomm zU
    have hzambient :
        C.embedding ((zU.1 : U.normalSubgroup) : B) ∈
          Subgroup.centralizer (T.normalSubgroup : Set A) := by
      rw [hmatch]
      exact normalCenterElement_mem_ambientCentralizer
        (T := T) ⟨z.1, hzcentral⟩
    obtain ⟨c, hleftScalar, hrightScalar⟩ :=
      C.scalar_agreement
        ((zU.1 : U.normalSubgroup) : B) hzambient
    have hrightRestrictionOne :
        C.rightAssociated.restriction
            (zU.1 : U.normalSubgroup) =
          1 := by
      ext w
      exact LinearMap.congr_fun (htriv zU) w
    have hrightOne :
        C.rightProjective.operator
            ((zU.1 : U.normalSubgroup) : B) =
          1 := by
      rw [← C.rightAssociated.restriction_apply
        (zU.1 : U.normalSubgroup)]
      exact hrightRestrictionOne
    have hc : c = 1 := by
      apply scalarLinearEquiv_injective ℂ W
      rw [← hrightScalar, hrightOne]
      exact (map_one (scalarLinearEquiv ℂ W)).symm
    have hleftOne :
        C.leftProjective.operator
            (C.embedding ((zU.1 : U.normalSubgroup) : B)) =
          1 := by
      rw [hleftScalar, hc]
      exact map_one (scalarLinearEquiv ℂ V)
    apply LinearMap.ext
    intro v
    change
      C.leftAssociated.restriction
          (z.1 : T.normalSubgroup) v = v
    rw [C.leftAssociated.restriction_apply]
    change
      C.leftProjective.operator
          ((z.1 : T.normalSubgroup) : A) v = v
    rw [← hmatch, hleftOne]
    rfl

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
