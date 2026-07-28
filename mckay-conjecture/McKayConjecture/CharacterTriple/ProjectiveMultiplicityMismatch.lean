/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.MultiplicityProjective
import McKayConjecture.CharacterTriple.FactorSetCohomologyGroup
import McKayConjecture.CharacterTriple.ProjectiveFactorDeterminantCoboundary
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveFactorCohomology

/-!
# The projective mismatch on a restriction multiplicity space

Let `T` and `U` be character triples related by central-restriction group
data along `e : B →* A`.  Given independently associated projective
representations `P` and `Q`, the normal-subgroup intertwining space

`Hom_{U.normalSubgroup}(Q|_U, (P ∘ e)|_U)`

carries the projective action

`f ↦ P(e b) ∘ f ∘ Q(b)⁻¹`.

Its factor is the pointwise quotient

`P.factor (e b) (e c) * Q.factor b c⁻¹`.

The action is literally the identity on `U.normalSubgroup`, so it descends
with its chosen operators to the common outer quotient.  This is the
representation-theoretic mismatch whose determinant is controlled by the
restriction multiplicity.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveMultiplicityMismatch

open InductiveMcKay

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
variable {Q : ProjectiveRepresentation ℂ B W}

/-- The homomorphism between the distinguished normal subgroups induced by
the ambient embedding. -/
def normalHom
    (g : CentralRestrictionGroupData T U e) :
    U.normalSubgroup →* T.normalSubgroup where
  toFun x :=
    ⟨e x, g.rightNormal_le_comap_leftNormal x.property⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp

@[simp]
theorem normalHom_coe
    (g : CentralRestrictionGroupData T U e)
    (x : U.normalSubgroup) :
    ((normalHom g x : T.normalSubgroup) : A) = e (x : B) :=
  rfl

/-- The left normal restriction pulled back to the right normal subgroup. -/
abbrev leftNormalRestriction
    (R : AssociatedProjectiveRepresentation T V P)
    (g : CentralRestrictionGroupData T U e) :
    Representation ℂ U.normalSubgroup V :=
  R.fdRestriction.ρ.comp (normalHom g)

/-- The restriction-multiplicity space between the two distinguished normal
characters, in the chosen associated realizations. -/
abbrev Space
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e) :=
  Representation.IntertwiningMap S.fdRestriction.ρ
    (leftNormalRestriction R g)

/-- Translate between the categorical normal-restriction Hom-space and the
unbundled intertwining-map model carrying the mismatch action. -/
def fdRepHomEquivSpace
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e) :
    (S.fdRestriction ⟶
        FDRep.res (normalHom g) R.fdRestriction) ≃ₗ[ℂ]
      Space R S g :=
  (FDRep.forget₂HomLinearEquiv
      S.fdRestriction
      (FDRep.res (normalHom g) R.fdRestriction)).symm |>.trans
    (Rep.homLinearEquiv _ _)

/-- Replace the chosen associated normal restrictions by the canonical
realizations of the two normal characters. -/
def normalCharacterHomEquivFDRepHom
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e) :
    (U.character.realization ⟶
        FDRep.res (normalHom g) T.character.realization) ≃ₗ[ℂ]
      (S.fdRestriction ⟶
        FDRep.res (normalHom g) R.fdRestriction) := by
  let iS :=
    MultiplicityProjective.restrictionIsoRealization S
  let iR :=
    MultiplicityProjective.restrictionIsoRealization R
  let riR :=
    (FDRep.resFunctor (normalHom g)).mapIso iR
  exact
    { toFun := fun f ↦ iS.hom ≫ f ≫ riR.inv
      invFun := fun f ↦ iS.inv ≫ f ≫ riR.hom
      left_inv := by
        intro f
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [Iso.inv_hom_id, Category.comp_id]
      right_inv := by
        intro f
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        rw [Iso.hom_inv_id, Category.comp_id]
      map_add' := by
        intro f h
        simp
      map_smul' := by
        intro c f
        simp }

/-- The mismatch space is canonically linearly equivalent to the
character-level restriction Hom-space. -/
def normalCharacterHomEquivSpace
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e) :
    (U.character.realization ⟶
        FDRep.res (normalHom g) T.character.realization) ≃ₗ[ℂ]
      Space R S g :=
  (normalCharacterHomEquivFDRepHom R S g).trans
    (fdRepHomEquivSpace R S g)

/-- The dimension of the mismatch space is exactly the ordinary
restriction multiplicity of the right normal character inside the left
normal character. -/
theorem finrank_space_eq_restrictionMultiplicity
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e) :
    Module.finrank ℂ (Space R S g) =
      CliffordCorrespondence.restrictionMultiplicity
        (normalHom g) U.character T.character := by
  rw [CliffordCorrespondence.restrictionMultiplicity]
  exact (normalCharacterHomEquivSpace R S g).finrank_eq.symm

/-- The normal-subgroup homomorphism commutes with ambient conjugation. -/
theorem normalHom_conjNormal
    (g : CentralRestrictionGroupData T U e)
    (b : B) (x : U.normalSubgroup) :
    normalHom g (MulAut.conjNormal b x) =
      MulAut.conjNormal (e b) (normalHom g x) := by
  apply Subtype.ext
  simp only [normalHom_coe, MulAut.conjNormal_apply, map_mul, map_inv]

/-- Move a target normal operator past the inverse target projective
operator. -/
theorem right_restriction_mul_operator_symm
    (S : AssociatedProjectiveRepresentation U W Q)
    (b : B) (x : U.normalSubgroup) :
    S.restriction ((MulAut.conjNormal b).symm x) *
        (Q.operator b).symm =
      (Q.operator b).symm * S.restriction x :=
  MultiplicityProjective.restriction_mul_operator_symm S b x

/-- Conjugation by the pulled-back left projective operator carries the
pulled-back normal restriction at `x` to the restriction at `bxb⁻¹`. -/
theorem left_operator_mul_restriction
    (R : AssociatedProjectiveRepresentation T V P)
    (g : CentralRestrictionGroupData T U e)
    (b : B) (x : U.normalSubgroup) :
    P.operator (e b) * R.restriction (normalHom g x) =
      R.restriction (normalHom g (MulAut.conjNormal b x)) *
        P.operator (e b) := by
  rw [normalHom_conjNormal]
  exact
    MultiplicityProjective.operator_mul_restriction
      R (e b) (normalHom g x)

/-- The value of the mismatch action at an ambient element. -/
def actValue
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (b : B) (f : Space R S g) :
    Space R S g where
  toLinearMap :=
    (P.operator (e b)).toLinearMap ∘ₗ
      f.toLinearMap ∘ₗ (Q.operator b).symm.toLinearMap
  isIntertwining' x := by
    apply LinearMap.ext
    intro w
    let y : U.normalSubgroup :=
      (MulAut.conjNormal b).symm x
    have hright :=
      DFunLike.congr_fun
        (right_restriction_mul_operator_symm S b x) w
    have hright' :
        S.restriction y ((Q.operator b).symm w) =
          (Q.operator b).symm (S.restriction x w) := by
      simpa only [LinearEquiv.mul_apply] using hright
    change
      P.operator (e b)
          (f ((Q.operator b).symm (S.restriction x w))) =
        R.restriction (normalHom g x)
          (P.operator (e b)
            (f ((Q.operator b).symm w)))
    rw [← hright']
    have hf :=
      LinearMap.ext_iff.mp (f.isIntertwining' y)
        ((Q.operator b).symm w)
    change
      f (S.restriction y ((Q.operator b).symm w)) =
        R.restriction (normalHom g y)
          (f ((Q.operator b).symm w)) at hf
    rw [hf]
    have hleft :=
      DFunLike.congr_fun
        (left_operator_mul_restriction R g b y)
        (f ((Q.operator b).symm w))
    have hconj :
        MulAut.conjNormal b y = x := by
      exact (MulEquiv.apply_symm_apply
        (MulAut.conjNormal b) x)
    simpa only [LinearEquiv.mul_apply, hconj] using hleft

@[simp]
theorem actValue_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (b : B) (f : Space R S g) (w : W) :
    actValue R S g b f w =
      P.operator (e b) (f ((Q.operator b).symm w)) :=
  rfl

/-- The explicit inverse of the mismatch action at an ambient element. -/
def actValueInv
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (b : B) (f : Space R S g) :
    Space R S g where
  toLinearMap :=
    (P.operator (e b)).symm.toLinearMap ∘ₗ
      f.toLinearMap ∘ₗ (Q.operator b).toLinearMap
  isIntertwining' x := by
    apply LinearMap.ext
    intro w
    let z : U.normalSubgroup := MulAut.conjNormal b x
    have hright :=
      DFunLike.congr_fun
        (MultiplicityProjective.operator_mul_restriction S b x) w
    have hright' :
        Q.operator b (S.restriction x w) =
          S.restriction z (Q.operator b w) := by
      simpa only [LinearEquiv.mul_apply] using hright
    change
      (P.operator (e b)).symm
          (f (Q.operator b (S.restriction x w))) =
        R.restriction (normalHom g x)
          ((P.operator (e b)).symm
            (f (Q.operator b w)))
    rw [hright']
    have hf :=
      LinearMap.ext_iff.mp (f.isIntertwining' z)
        (Q.operator b w)
    change
      f (S.restriction z (Q.operator b w)) =
        R.restriction (normalHom g z)
          (f (Q.operator b w)) at hf
    rw [hf]
    apply (P.operator (e b)).injective
    have hleft :=
      DFunLike.congr_fun
        (left_operator_mul_restriction R g b x)
        ((P.operator (e b)).symm (f (Q.operator b w)))
    simpa only [LinearEquiv.mul_apply,
      LinearEquiv.apply_symm_apply] using hleft.symm

@[simp]
theorem actValueInv_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (b : B) (f : Space R S g) (w : W) :
    actValueInv R S g b f w =
      (P.operator (e b)).symm (f (Q.operator b w)) :=
  rfl

/-- Each element of the right ambient group acts invertibly on the mismatch
multiplicity space. -/
def operator
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (b : B) :
    Space R S g ≃ₗ[ℂ] Space R S g where
  toFun := actValue R S g b
  invFun := actValueInv R S g b
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    change
      (P.operator (e b)).symm
          (P.operator (e b)
            (f ((Q.operator b).symm (Q.operator b w)))) = f w
    simp
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    change
      P.operator (e b)
          ((P.operator (e b)).symm
            (f (Q.operator b ((Q.operator b).symm w)))) = f w
    simp
  map_add' f f' := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    change
      P.operator (e b)
          ((f + f') ((Q.operator b).symm w)) =
        P.operator (e b) (f ((Q.operator b).symm w)) +
          P.operator (e b) (f' ((Q.operator b).symm w))
    simp
    rfl
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    change
      P.operator (e b)
          ((c • f) ((Q.operator b).symm w)) =
        c • P.operator (e b) (f ((Q.operator b).symm w))
    simp
    rfl

@[simp]
theorem operator_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (b : B) (f : Space R S g) (w : W) :
    operator R S g b f w =
      P.operator (e b) (f ((Q.operator b).symm w)) :=
  rfl

/-- The mismatch action is projective, with factor equal to the quotient of
the pulled-back left factor by the right factor. -/
def projective
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e) :
    ProjectiveRepresentation ℂ B (Space R S g) where
  operator := operator R S g
  factor b c :=
    P.factor (e b) (e c) * (Q.factor b c)⁻¹
  map_mul b c := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    change
      actValue R S g b (actValue R S g c f) w =
        (scalarLinearEquiv ℂ (Space R S g)
          (P.factor (e b) (e c) * (Q.factor b c)⁻¹)
          (actValue R S g (b * c) f)).toLinearMap w
    rw [actValue_apply, actValue_apply,
      scalarLinearEquiv_apply]
    change
      P.operator (e b)
          (P.operator (e c)
            (f ((Q.operator c).symm
              ((Q.operator b).symm w)))) =
        (↑(P.factor (e b) (e c) *
            (Q.factor b c)⁻¹) : ℂ) •
          actValue R S g (b * c) f w
    rw [actValue_apply]
    have hqmul :=
      congrArg (fun z : W ≃ₗ[ℂ] W ↦ z⁻¹)
        (Q.map_mul b c)
    have hqapp := DFunLike.congr_fun hqmul w
    simp only [mul_inv_rev, LinearEquiv.mul_apply] at hqapp
    have hqapp' :
        (Q.operator c).symm ((Q.operator b).symm w) =
          (Q.operator (b * c)).symm
            ((scalarLinearEquiv ℂ W (Q.factor b c))⁻¹ w) :=
      hqapp
    rw [hqapp']
    have hqscalar :
        (scalarLinearEquiv ℂ W (Q.factor b c))⁻¹ w =
          ((Q.factor b c : ℂ)⁻¹ • w) := by
      rw [← map_inv]
      rw [scalarLinearEquiv_apply, Units.val_inv_eq_inv_val]
    rw [hqscalar]
    simp only [map_smul]
    have hpapp :=
      DFunLike.congr_fun (P.map_mul (e b) (e c))
        (f ((Q.operator (b * c)).symm w))
    have hpapp' :
        P.operator (e b)
            (P.operator (e c)
              (f ((Q.operator (b * c)).symm w))) =
          (P.factor (e b) (e c) : ℂ) •
            P.operator (e (b * c))
              (f ((Q.operator (b * c)).symm w)) := by
      simpa only [map_mul, LinearEquiv.mul_apply,
        scalarLinearEquiv_apply] using hpapp
    rw [hpapp']
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    module

@[simp]
theorem projective_operator
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (b : B) :
    (projective R S g).operator b = operator R S g b :=
  rfl

@[simp]
theorem projective_factor
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (b c : B) :
    (projective R S g).factor b c =
      P.factor (e b) (e c) * (Q.factor b c)⁻¹ :=
  rfl

/-- The mismatch action is literally the identity on the distinguished
right normal subgroup. -/
theorem operator_normal
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (x : U.normalSubgroup) :
    operator R S g (x : B) = 1 := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro f
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro w
  change
    P.operator ((normalHom g x : T.normalSubgroup) : A)
        (f ((Q.operator (x : B)).symm w)) =
      f w
  have hf :=
    LinearMap.ext_iff.mp (f.isIntertwining' x)
      ((Q.operator (x : B)).symm w)
  change
    f (S.restriction x
        ((Q.operator (x : B)).symm w)) =
      R.restriction (normalHom g x)
        (f ((Q.operator (x : B)).symm w)) at hf
  rw [← R.restriction_apply (normalHom g x),
    ← hf, S.restriction_apply,
    LinearEquiv.apply_symm_apply]

@[simp]
theorem projective_operator_normal
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (x : U.normalSubgroup) :
    (projective R S g).operator (x : B) = 1 :=
  operator_normal R S g x

/-- The mismatch factor is one when its first argument lies in the
distinguished right normal subgroup. -/
theorem factor_normal_left
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (x : U.normalSubgroup) (b : B) :
    (projective R S g).factor (x : B) b = 1 := by
  rw [projective_factor,
    ← normalHom_coe g x,
    R.factor_normal_left (normalHom g x) (e b),
    S.factor_normal_left x b]
  simp

/-- The mismatch factor is one when its second argument lies in the
distinguished right normal subgroup. -/
theorem factor_normal_right
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (b : B) (x : U.normalSubgroup) :
    (projective R S g).factor b (x : B) = 1 := by
  rw [projective_factor,
    ← normalHom_coe g x,
    R.factor_normal_right (e b) (normalHom g x),
    S.factor_normal_right b x]
  simp

/-- Exact quotient compatibility of the mismatch action. -/
theorem isQuotientCompatible
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e) :
    (projective R S g).IsQuotientCompatible U.normalSubgroup where
  factor_normal_left := factor_normal_left R S g
  factor_normal_right := factor_normal_right R S g
  operator_normal := projective_operator_normal R S g

/-- The mismatch action descended to the common right outer quotient. -/
def quotientProjective
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e) :
    ProjectiveRepresentation ℂ
      (B ⧸ U.normalSubgroup) (Space R S g) :=
  (projective R S g).quotientDescent U.normalSubgroup
    (isQuotientCompatible R S g)

@[simp]
theorem quotientProjective_operator_mk
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (b : B) :
    (quotientProjective R S g).operator
        (QuotientGroup.mk' U.normalSubgroup b) =
      operator R S g b :=
  (projective R S g).quotientDescent_operator_mk
    (isQuotientCompatible R S g) b

@[simp]
theorem quotientProjective_factor_mk
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    [Nontrivial (Space R S g)]
    (b c : B) :
    (quotientProjective R S g).factor
        (QuotientGroup.mk' U.normalSubgroup b)
        (QuotientGroup.mk' U.normalSubgroup c) =
      P.factor (e b) (e c) * (Q.factor b c)⁻¹ := by
  change
    ((projective R S g).quotientDescent
      U.normalSubgroup
      (isQuotientCompatible R S g)).factor
        (QuotientGroup.mk' U.normalSubgroup b)
        (QuotientGroup.mk' U.normalSubgroup c) =
      P.factor (e b) (e c) * (Q.factor b c)⁻¹
  calc
    _ = (projective R S g).factor b c :=
      (projective R S g).quotientDescent_factor_mk
        (isQuotientCompatible R S g) b c
    _ = _ := rfl

/-- The quotient mismatch factor set is the pointwise quotient of the
transported left factor set by the right factor set. -/
theorem quotientProjective_factorSet
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    [Nontrivial (Space R S g)] :
    (quotientProjective R S g).factorSet =
      R.quotientFactorSetAlong g * S.quotientFactorSet⁻¹ := by
  apply FactorSet.ext
  intro a b
  induction a using QuotientGroup.induction_on with
  | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
          change
            (quotientProjective R S g).factor
                (QuotientGroup.mk' U.normalSubgroup a)
                (QuotientGroup.mk' U.normalSubgroup b) =
              (R.quotientFactorSetAlong g *
                S.quotientFactorSet⁻¹)
                (QuotientGroup.mk' U.normalSubgroup a)
                (QuotientGroup.mk' U.normalSubgroup b)
          rw [quotientProjective_factor_mk,
            FactorSet.mul_apply, FactorSet.inv_apply,
            R.quotientFactorSetAlong_mk g,
            S.quotientFactorSet_mk]

/-- The restriction-multiplicity dimension annihilates the mismatch of the
two quotient factor classes. -/
theorem finrank_nsmul_quotientFactorMismatch_h2Class_eq_zero
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    [Nontrivial (Space R S g)] :
    letI :=
      trivialMulDistribMulAction
        (B ⧸ U.normalSubgroup) ℂˣ
    Module.finrank ℂ (Space R S g) •
        (R.quotientFactorSetAlong g *
          S.quotientFactorSet⁻¹).h2Class =
      0 := by
  letI :=
    trivialMulDistribMulAction
      (B ⧸ U.normalSubgroup) ℂˣ
  rw [← quotientProjective_factorSet R S g]
  exact
    (quotientProjective R S g
      ).finrank_nsmul_factorSet_h2Class_eq_zero

/-- If the restriction-multiplicity mismatch class vanishes, the two
quotient factor classes agree. -/
theorem quotientFactorH2ClassAgreement_of_mismatch_eq_zero
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (h :
      letI :=
        trivialMulDistribMulAction
          (B ⧸ U.normalSubgroup) ℂˣ
      (R.quotientFactorSetAlong g *
        S.quotientFactorSet⁻¹).h2Class = 0) :
    R.QuotientFactorH2ClassAgreement S g := by
  letI :=
    trivialMulDistribMulAction
      (B ⧸ U.normalSubgroup) ℂˣ
  exact
    (FactorSet.h2Class_mul_inv_eq_zero_iff
      (R.quotientFactorSetAlong g)
      S.quotientFactorSet).mp h |>.symm

end ProjectiveMultiplicityMismatch
end CharacterTriple
end McKayConjecture
