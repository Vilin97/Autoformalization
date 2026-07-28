/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.QuotientDescent
import McKayConjecture.CharacterTriple.AssociatedQuotientCompatibility

/-!
# Descent of associated projective representations

This file packages the exact data saying that a surjection of ambient
groups is a quotient map of two character triples.  When an associated
projective representation is exactly trivial on the ambient kernel, its
chosen operators and factors descend.  The descended normal restriction is
proved irreducible by reflection of irreducibility along the surjective
normal-subgroup map.
-/

noncomputable section

open CategoryTheory

universe u v

namespace McKayConjecture
namespace CharacterTriple

variable {A : Type u} {B : Type v}
variable [Group A] [Group B] [Finite A] [Finite B]
variable (T : CharacterTriple A) (U : CharacterTriple B)

/-- A surjective ambient homomorphism which sends one character triple
onto another, including exact inflation of the normal character. -/
structure QuotientData (f : A →* B) where
  /-- The ambient homomorphism is onto. -/
  surjective : Function.Surjective f
  /-- The source normal subgroup maps into the target normal subgroup. -/
  normalProjection : T.normalSubgroup →* U.normalSubgroup
  /-- The normal projection is induced by the ambient projection. -/
  normalProjection_coe :
    ∀ x : T.normalSubgroup,
      ((normalProjection x : U.normalSubgroup) : B) =
        f (x : A)
  /-- The induced normal-subgroup map is onto. -/
  normal_surjective :
    Function.Surjective
      normalProjection
  /-- The source normal character is the inflation of the target normal
  character. -/
  character_values :
    ∀ x : T.normalSubgroup,
      T.character.values x =
        U.character.values (normalProjection x)
  /-- The ambient quotient kernel is contained in the source normal
  subgroup. -/
  ker_le_normal : f.ker ≤ T.normalSubgroup

namespace QuotientData

variable {T U}
variable {f : A →* B} (q : QuotientData T U f)

@[simp]
theorem normalProjection_apply_coe
    (x : T.normalSubgroup) :
    ((q.normalProjection x : U.normalSubgroup) : B) =
      f (x : A) :=
  q.normalProjection_coe x

/-- The first-isomorphism identification for the ambient quotient. -/
def ambientQuotientEquiv :
    (A ⧸ f.ker) ≃* B :=
  QuotientGroup.quotientKerEquivOfSurjective f q.surjective

@[simp]
theorem ambientQuotientEquiv_mk (a : A) :
    q.ambientQuotientEquiv (QuotientGroup.mk a) =
      f a := by
  change QuotientGroup.kerLift f (QuotientGroup.mk a) = f a
  exact QuotientGroup.kerLift_mk f a

/-- The first-isomorphism identification for the normal-subgroup
projection. -/
def normalQuotientEquiv :
    (T.normalSubgroup ⧸ q.normalProjection.ker) ≃*
      U.normalSubgroup :=
  QuotientGroup.quotientKerEquivOfSurjective
    q.normalProjection q.normal_surjective

@[simp]
theorem normalQuotientEquiv_mk
    (x : T.normalSubgroup) :
    q.normalQuotientEquiv
        (QuotientGroup.mk' q.normalProjection.ker x) =
      q.normalProjection x := by
  change
    QuotientGroup.kerLift q.normalProjection
        (QuotientGroup.mk x) =
      q.normalProjection x
  exact QuotientGroup.kerLift_mk q.normalProjection x

/-- The kernel of the induced normal projection is the ambient kernel,
viewed inside the source normal subgroup. -/
@[simp]
theorem normalProjection_ker :
    q.normalProjection.ker =
      f.ker.subgroupOf T.normalSubgroup := by
  ext x
  constructor
  · intro hx
    apply MonoidHom.mem_ker.mpr
    have hx' := MonoidHom.mem_ker.mp hx
    have hxCoe :=
      congrArg (fun y : U.normalSubgroup => (y : B)) hx'
    rw [q.normalProjection_apply_coe] at hxCoe
    exact hxCoe
  · intro hx
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    rw [q.normalProjection_apply_coe]
    exact MonoidHom.mem_ker.mp hx

/-- Exact inflation of the normal character makes it trivial on the normal
projection kernel. -/
theorem character_trivialOn_normalProjection_ker :
    T.character.TrivialOn q.normalProjection.ker := by
  let ψ : IrreducibleCharacter
      (T.normalSubgroup ⧸ q.normalProjection.ker) :=
    U.character.comap q.normalQuotientEquiv
  have hcharacter :
      T.character =
        IrreducibleCharacter.inflate
          q.normalProjection.ker ψ := by
    apply IrreducibleCharacter.ext
    funext x
    rw [IrreducibleCharacter.inflate_values,
      IrreducibleCharacter.comap_values]
    calc
      T.character.values x =
          U.character.values (q.normalProjection x) :=
        q.character_values x
      _ =
          U.character.values
            (q.normalQuotientEquiv
              (QuotientGroup.mk' q.normalProjection.ker x)) := by
        rw [q.normalQuotientEquiv_mk]
  rw [hcharacter]
  exact
    IrreducibleCharacter.inflate_trivialOn
      q.normalProjection.ker ψ

variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- The exact chosen-operator descent, transported from the kernel quotient
to the target ambient group. -/
def quotientProjective
    (hP : P.IsQuotientCompatible f.ker) :
    ProjectiveRepresentation ℂ B V :=
  (P.quotientDescent f.ker hP).comap
    q.ambientQuotientEquiv.symm.toMonoidHom

@[simp]
theorem quotientProjective_operator_projection
    (hP : P.IsQuotientCompatible f.ker)
    (a : A) :
    (q.quotientProjective hP).operator (f a) =
      P.operator a := by
  change
    (P.quotientDescent f.ker hP).operator
        (q.ambientQuotientEquiv.symm (f a)) =
      P.operator a
  rw [← q.ambientQuotientEquiv_mk a,
    q.ambientQuotientEquiv.symm_apply_apply]
  exact P.quotientDescent_operator_mk hP a

@[simp]
theorem quotientProjective_factor_projection
    (hP : P.IsQuotientCompatible f.ker)
    (a b : A) :
    (q.quotientProjective hP).factor (f a) (f b) =
      P.factor a b := by
  change
    (P.quotientDescent f.ker hP).factor
        (q.ambientQuotientEquiv.symm (f a))
        (q.ambientQuotientEquiv.symm (f b)) =
      P.factor a b
  rw [← q.ambientQuotientEquiv_mk a,
    ← q.ambientQuotientEquiv_mk b,
    q.ambientQuotientEquiv.symm_apply_apply,
    q.ambientQuotientEquiv.symm_apply_apply]
  exact P.quotientDescent_factor_mk hP a b

variable (R : AssociatedProjectiveRepresentation T V P)

include q R in
/-- Association plus exact character inflation automatically supplies the
operator and factor hypotheses needed for ambient projective descent. -/
lemma associated_isQuotientCompatible :
    P.IsQuotientCompatible f.ker := by
  have h :=
    AssociatedProjectiveRepresentation.isQuotientCompatible_of_trivialOn
      R
      q.normalProjection.ker
      q.character_trivialOn_normalProjection_ker
  rw [q.normalProjection_ker,
    Subgroup.map_subgroupOf_eq_of_le q.ker_le_normal] at h
  exact h

/-- The source normal restriction is trivial on the kernel of the normal
projection. -/
theorem restriction_trivialOn_normalProjection_ker
    (hP : P.IsQuotientCompatible f.ker)
    (x : q.normalProjection.ker) :
    R.restriction (x : T.normalSubgroup) = 1 := by
  rw [R.restriction_apply]
  let n : f.ker :=
    ⟨(x : T.normalSubgroup), by
      apply MonoidHom.mem_ker.mpr
      have hx := MonoidHom.mem_ker.mp x.property
      have hxCoe :=
        congrArg (fun z : U.normalSubgroup => (z : B)) hx
      rw [q.normalProjection_apply_coe] at hxCoe
      exact hxCoe⟩
  have hn :=
    ProjectiveRepresentation.IsQuotientCompatible.operator_normal
      hP n
  change P.operator (x.1.1 : A) = 1 at hn ⊢
  exact hn

/-- The kernel of the normal projection lies in the kernel of the ordinary
normal restriction. -/
theorem normalProjection_ker_le_restriction_ker
    (hP : P.IsQuotientCompatible f.ker) :
    q.normalProjection.ker ≤ R.restriction.ker := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  exact q.restriction_trivialOn_normalProjection_ker
    R hP ⟨x, hx⟩

/-- Descent of the ordinary normal-subgroup restriction. -/
def quotientRestriction
    (hP : P.IsQuotientCompatible f.ker) :
    U.normalSubgroup →* (V ≃ₗ[ℂ] V) :=
  (QuotientGroup.lift q.normalProjection.ker
      R.restriction
      (q.normalProjection_ker_le_restriction_ker
        R hP)).comp
    q.normalQuotientEquiv.symm.toMonoidHom

@[simp]
theorem quotientRestriction_normalProjection
    (hP : P.IsQuotientCompatible f.ker)
    (x : T.normalSubgroup) :
    q.quotientRestriction R hP (q.normalProjection x) =
      R.restriction x := by
  change
    QuotientGroup.lift q.normalProjection.ker
        R.restriction
        (q.normalProjection_ker_le_restriction_ker R hP)
        (q.normalQuotientEquiv.symm
          (q.normalProjection x)) =
      R.restriction x
  rw [← q.normalQuotientEquiv_mk x,
    q.normalQuotientEquiv.symm_apply_apply]
  exact QuotientGroup.lift_mk' _ _ x

/-- The descended normal restriction is the restriction of the descended
projective representation. -/
theorem quotientRestriction_apply
    (hP : P.IsQuotientCompatible f.ker)
    (y : U.normalSubgroup) :
    q.quotientRestriction R hP y =
      (q.quotientProjective hP).operator y := by
  obtain ⟨x, rfl⟩ := q.normal_surjective y
  rw [q.quotientRestriction_normalProjection R hP x,
    R.restriction_apply]
  rw [q.normalProjection_apply_coe]
  exact
    (q.quotientProjective_operator_projection
      hP (x : A)).symm

/-- The descended normal restriction remains irreducible. -/
theorem quotientRestriction_simple
    (hP : P.IsQuotientCompatible f.ker) :
    Simple
      (FDRep.of
        (linearRepresentationOfAction
          (q.quotientRestriction R hP))) := by
  let σ :=
    linearRepresentationOfAction
      (q.quotientRestriction R hP)
  have hs :
      Simple
        (FDRep.of
          (σ.comp q.normalProjection)) ↔
        Simple (FDRep.of σ) :=
    FDRep.simple_comp_iff_of_surjective
      σ q.normalProjection q.normal_surjective
  apply hs.mp
  have hrep :
      σ.comp q.normalProjection =
        linearRepresentationOfAction R.restriction := by
    apply MonoidHom.ext
    intro x
    change
      ((q.quotientRestriction R hP
        (q.normalProjection x) : V ≃ₗ[ℂ] V) :
          V →ₗ[ℂ] V) =
        ((R.restriction x : V ≃ₗ[ℂ] V) :
          V →ₗ[ℂ] V)
    rw [q.quotientRestriction_normalProjection R hP x]
  rw [hrep]
  exact R.restriction_simple

/-- Descend an associated projective representation through a quotient of
character triples. -/
def quotientAssociated
    (hP : P.IsQuotientCompatible f.ker) :
    AssociatedProjectiveRepresentation U V
      (q.quotientProjective hP) where
  restriction := q.quotientRestriction R hP
  restriction_apply := q.quotientRestriction_apply R hP
  restriction_simple := q.quotientRestriction_simple R hP
  restriction_character := by
    funext y
    obtain ⟨x, rfl⟩ := q.normal_surjective y
    change
      LinearMap.trace ℂ V
          ((q.quotientRestriction R hP
            (q.normalProjection x) : V ≃ₗ[ℂ] V) :
              V →ₗ[ℂ] V) =
        U.character.values (q.normalProjection x)
    rw [q.quotientRestriction_normalProjection R hP x]
    calc
      LinearMap.trace ℂ V
          ((R.restriction x : V ≃ₗ[ℂ] V) :
            V →ₗ[ℂ] V) =
          T.character.values x :=
        congrFun R.restriction_character x
      _ = U.character.values (q.normalProjection x) :=
        q.character_values x
  normal_mul := by
    intro y b
    obtain ⟨x, rfl⟩ := q.normal_surjective y
    obtain ⟨a, rfl⟩ := q.surjective b
    rw [q.normalProjection_apply_coe,
      ← map_mul,
      q.quotientProjective_operator_projection hP,
      R.normal_mul,
      q.quotientProjective_operator_projection hP,
      q.quotientProjective_operator_projection hP]
  mul_normal := by
    intro b y
    obtain ⟨a, rfl⟩ := q.surjective b
    obtain ⟨x, rfl⟩ := q.normal_surjective y
    rw [q.normalProjection_apply_coe,
      ← map_mul,
      q.quotientProjective_operator_projection hP,
      R.mul_normal,
      q.quotientProjective_operator_projection hP,
      q.quotientProjective_operator_projection hP]

end QuotientData
end CharacterTriple
end McKayConjecture
