/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralCorrespondence
import McKayConjecture.CharacterTriple.CentralQuotient
import McKayConjecture.CharacterTriple.ProjectiveQuotientDescent

/-!
# Exact projective lift across a central character-triple isomorphism

Let `C : (A, X, χ) ≥c (B, M, χ')`.  A projective representation on `B`
whose factor is inverse to the associated right factor and whose chosen
operators are identity on `M` descends *with those exact operators* to
`B / M`.  Transport across `C.quotientEquiv.symm` and inflation along
`A → A / X` then produces a projective representation on `A`.

Unlike lifting a projective-linear action, this construction recovers the
chosen operators on `B` exactly.  Scalar injectivity consequently recovers
the factor exactly as well.  The resulting representation is identity on
`X` and has factor inverse to the associated left factor.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace CharacterTriple
namespace FactorMatchedIsomorphismWitness

local notation "CentralIsomorphismWitness" =>
  FactorMatchedIsomorphismWitness

variable {A : Type u} {B : Type v}
variable [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W Z : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]
variable [AddCommGroup Z] [Module ℂ Z] [Nontrivial Z]

/-- The associated left factor is constant on pairs of `X`-cosets. -/
theorem leftFactorIsQuotientCompatible
    (C : CentralIsomorphismWitness T U V W) :
    C.leftProjective.FactorIsQuotientCompatible
      T.normalSubgroup where
  factor_normal_left :=
    C.leftAssociated.factor_normal_left
  factor_normal_right :=
    C.leftAssociated.factor_normal_right

omit [Nontrivial Z] in
/-- An inverse right factor is likewise constant on pairs of `M`-cosets. -/
theorem rightFactorIsQuotientCompatible
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ B Z)
    (hQ : C.rightProjective.HasInverseFactorSet Q) :
    Q.FactorIsQuotientCompatible U.normalSubgroup where
  factor_normal_left := by
    intro m b
    rw [hQ, C.rightAssociated.factor_normal_left m b, inv_one]
  factor_normal_right := by
    intro b m
    rw [hQ, C.rightAssociated.factor_normal_right b m, inv_one]

omit [Nontrivial Z] in
/-- The inverse-factor and normal-operator hypotheses give the exact data
needed to descend the chosen right operators. -/
theorem rightIsQuotientCompatible
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ B Z)
    (hQ : C.rightProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal U) :
    Q.IsQuotientCompatible U.normalSubgroup where
  toFactorIsQuotientCompatible :=
    C.rightFactorIsQuotientCompatible Q hQ
  operator_normal := htriv

/-- The exact chosen-operator descent of `Q` to `B / M`. -/
def descendRightProjective
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ B Z)
    (hQ : C.rightProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal U) :
    ProjectiveRepresentation ℂ (B ⧸ U.normalSubgroup) Z :=
  Q.quotientDescent U.normalSubgroup
    (C.rightIsQuotientCompatible Q hQ htriv)

/-- Transport the descended representation from `B / M` to `A / X`. -/
def transportRightProjectiveToLeftQuotient
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ B Z)
    (hQ : C.rightProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal U) :
    ProjectiveRepresentation ℂ (A ⧸ T.normalSubgroup) Z :=
  (C.descendRightProjective Q hQ htriv).comap
    C.quotientEquiv.symm.toMonoidHom

/-- Lift a right inverse-factor projective representation to the left
ambient group, retaining its chosen operators on the embedded copy of `B`. -/
def liftRightProjective
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ B Z)
    (hQ : C.rightProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal U) :
    ProjectiveRepresentation ℂ A Z :=
  (C.transportRightProjectiveToLeftQuotient Q hQ htriv).comap
    (QuotientGroup.mk' T.normalSubgroup)

omit [Nontrivial Z] in
/-- The exact descent recovers a right chosen operator on its quotient
coset. -/
@[simp]
theorem descendRightProjective_operator_mk
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ B Z)
    (hQ : C.rightProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal U) (b : B) :
    (C.descendRightProjective Q hQ htriv).operator
        (QuotientGroup.mk' U.normalSubgroup b) =
      Q.operator b :=
  Q.quotientDescent_operator_mk
    (C.rightIsQuotientCompatible Q hQ htriv) b

omit [Nontrivial Z] in
/-- On the embedded right ambient group, the lifted chosen operator is
literally the original chosen operator, not merely a scalar multiple. -/
@[simp]
theorem liftRightProjective_operator_embedding
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ B Z)
    (hQ : C.rightProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal U) (b : B) :
    (C.liftRightProjective Q hQ htriv).operator
        (C.embedding b) =
      Q.operator b := by
  change
    (C.descendRightProjective Q hQ htriv).operator
        (C.quotientEquiv.symm
          (QuotientGroup.mk' T.normalSubgroup
            (C.embedding b))) =
      Q.operator b
  rw [← C.quotientEquiv_mk b,
    C.quotientEquiv.symm_apply_apply]
  exact C.descendRightProjective_operator_mk Q hQ htriv b

omit [Nontrivial Z] in
/-- The lifted action is identity on the left normal subgroup. -/
theorem liftRightProjective_isTrivialOnNormal
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ B Z)
    (hQ : C.rightProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal U) :
    (C.liftRightProjective Q hQ htriv).IsTrivialOnNormal T := by
  intro x
  change
    (C.descendRightProjective Q hQ htriv).operator
        (C.quotientEquiv.symm
          (QuotientGroup.mk' T.normalSubgroup (x : A))) =
      1
  have hx :
      QuotientGroup.mk' T.normalSubgroup (x : A) = 1 :=
    (QuotientGroup.eq_one_iff (x : A)).2 x.property
  rw [hx, map_one]
  calc
    (C.descendRightProjective Q hQ htriv).operator 1 =
        (C.descendRightProjective Q hQ htriv).operator
          (QuotientGroup.mk' U.normalSubgroup (1 : B)) := by
      rw [map_one]
    _ = Q.operator 1 :=
      C.descendRightProjective_operator_mk Q hQ htriv 1
    _ = 1 := htriv (1 : U.normalSubgroup)

omit [Nontrivial Z] in
/-- Pullback along the central-isomorphism embedding recovers all chosen
right operators. -/
theorem liftRightProjective_comap_operator
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ B Z)
    (hQ : C.rightProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal U) :
    ((C.liftRightProjective Q hQ htriv).comap
        C.embedding).operator =
      Q.operator := by
  funext b
  exact C.liftRightProjective_operator_embedding Q hQ htriv b

/-- Exact operator recovery forces exact recovery of the factor. -/
theorem liftRightProjective_comap_factor
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ B Z)
    (hQ : C.rightProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal U) :
    ((C.liftRightProjective Q hQ htriv).comap
        C.embedding).factor =
      Q.factor :=
  ProjectiveRepresentation.factor_eq_of_operator_eq _ _
    (C.liftRightProjective_comap_operator Q hQ htriv)

/-- Pullback of the lift along the embedding is exactly `Q`. -/
theorem liftRightProjective_comap
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ B Z)
    (hQ : C.rightProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal U) :
    (C.liftRightProjective Q hQ htriv).comap
        C.embedding =
      Q :=
  ProjectiveRepresentation.ext_of_operator_eq _ _
    (C.liftRightProjective_comap_operator Q hQ htriv)

/-- In particular, the factor agrees exactly on embedded right elements. -/
@[simp]
theorem liftRightProjective_factor_embedding
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ B Z)
    (hQ : C.rightProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal U) (b c : B) :
    (C.liftRightProjective Q hQ htriv).factor
        (C.embedding b) (C.embedding c) =
      Q.factor b c :=
  congrFun
    (congrFun
      (C.liftRightProjective_comap_factor Q hQ htriv) b) c

/-- A normal-times-embedded decomposition gives equality of the
corresponding left quotient cosets. -/
theorem quotient_mk_eq_embedding_of_normal_mul
    (C : CentralIsomorphismWitness T U V W)
    (a : A) (x : T.normalSubgroup) (b : B)
    (hxb : (x : A) * C.embedding b = a) :
    QuotientGroup.mk' T.normalSubgroup a =
      QuotientGroup.mk' T.normalSubgroup (C.embedding b) := by
  calc
    QuotientGroup.mk' T.normalSubgroup a =
        QuotientGroup.mk' T.normalSubgroup
          ((x : A) * C.embedding b) :=
      congrArg (QuotientGroup.mk' T.normalSubgroup) hxb.symm
    _ =
        QuotientGroup.mk' T.normalSubgroup (x : A) *
          QuotientGroup.mk' T.normalSubgroup
            (C.embedding b) :=
      (QuotientGroup.mk' T.normalSubgroup).map_mul _ _
    _ = 1 *
          QuotientGroup.mk' T.normalSubgroup
            (C.embedding b) := by
      exact congrArg
        (fun q : A ⧸ T.normalSubgroup ↦
          q * QuotientGroup.mk' T.normalSubgroup
            (C.embedding b))
        ((QuotientGroup.eq_one_iff (x : A)).2 x.property)
    _ =
        QuotientGroup.mk' T.normalSubgroup
          (C.embedding b) := one_mul _

/-- The lifted factor is inverse to the associated left factor on every
pair of ambient elements. -/
theorem liftRightProjective_hasInverseFactorSet
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ B Z)
    (hQ : C.rightProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal U) :
    C.leftProjective.HasInverseFactorSet
      (C.liftRightProjective Q hQ htriv) := by
  intro a k
  obtain ⟨x, b, hxb⟩ := C.ambient_eq_product a
  obtain ⟨y, c, hyc⟩ := C.ambient_eq_product k
  have ha :=
    C.quotient_mk_eq_embedding_of_normal_mul a x b hxb
  have hk :=
    C.quotient_mk_eq_embedding_of_normal_mul k y c hyc
  have hleft :
      C.leftProjective.factor a k =
        C.leftProjective.factor
          (C.embedding b) (C.embedding c) :=
    (C.leftFactorIsQuotientCompatible).factor_eq_of_mk_eq
      ha hk
  have hlift :
      (C.liftRightProjective Q hQ htriv).factor a k =
        Q.factor b c := by
    calc
      (C.liftRightProjective Q hQ htriv).factor a k =
          (C.liftRightProjective Q hQ htriv).factor
            (C.embedding b) (C.embedding c) := by
        change
          (C.transportRightProjectiveToLeftQuotient
              Q hQ htriv).factor
              (QuotientGroup.mk' T.normalSubgroup a)
              (QuotientGroup.mk' T.normalSubgroup k) =
            (C.transportRightProjectiveToLeftQuotient
              Q hQ htriv).factor
              (QuotientGroup.mk' T.normalSubgroup
                (C.embedding b))
              (QuotientGroup.mk' T.normalSubgroup
                (C.embedding c))
        rw [ha, hk]
      _ = Q.factor b c :=
        C.liftRightProjective_factor_embedding Q hQ htriv b c
  calc
    (C.liftRightProjective Q hQ htriv).factor a k =
        Q.factor b c := hlift
    _ = (C.rightProjective.factor b c)⁻¹ := hQ b c
    _ =
        (C.leftProjective.factor
          (C.embedding b) (C.embedding c))⁻¹ := by
      rw [C.factor_agreement]
    _ = (C.leftProjective.factor a k)⁻¹ := by
      rw [hleft]

end FactorMatchedIsomorphismWitness

namespace CentralIsomorphismWitness

export FactorMatchedIsomorphismWitness
  (rightFactorIsQuotientCompatible rightIsQuotientCompatible
    descendRightProjective descendRightProjective_operator_mk
    transportRightProjectiveToLeftQuotient leftFactorIsQuotientCompatible
    liftRightProjective liftRightProjective_operator_embedding
    liftRightProjective_comap_operator liftRightProjective_comap
    liftRightProjective_comap_factor liftRightProjective_factor_embedding
    liftRightProjective_hasInverseFactorSet
    liftRightProjective_isTrivialOnNormal
    quotient_mk_eq_embedding_of_normal_mul)

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
