/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Determination
import McKayConjecture.CharacterTriple.CentralIsomorphism

/-!
# Uniqueness of associated projective representations

Two projective representations associated with the same invariant
irreducible character need not have literally equal chosen lifts.  After
identifying their irreducible restrictions, however, Schur's lemma shows
that their ambient operators differ by a unique nonzero scalar at every
group element.  The resulting scalar cochain is trivial on the normal
subgroup and constant on its left and right cosets.

Consequently one associated lift can be rescaled, without changing its
restriction, so that it is exactly conjugate to the other lift.  In
particular, the rescaled factor sets agree literally, not merely in
cohomology.
-/

noncomputable section

open CategoryTheory

universe u

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

variable {A : Type u} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
  {Q : ProjectiveRepresentation ℂ A W}

/-- The restrictions of two associated lifts of the same character are
equivalent. -/
def restrictionEquiv
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q) :
    Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction) := by
  let i :=
    Classical.choice
      (FDRep.nonempty_iso_of_character_eq
      R.fdRestriction S.fdRestriction
      (R.fdRestriction_character.trans
        S.fdRestriction_character.symm))
  let e := FDRep.isoToLinearEquiv i
  apply Representation.Equiv.mk e
  intro x
  have hconj := FDRep.Iso.conj_ρ i x
  apply LinearMap.ext
  intro v
  have hv := LinearMap.congr_fun hconj (e v)
  simpa [e, LinearEquiv.conj_apply] using hv.symm

/-- An associated lift conjugates its normal restriction in the expected
way. -/
theorem operator_mul_restriction
    (R : AssociatedProjectiveRepresentation T V P)
    (a : A) (x : T.normalSubgroup) :
    P.operator a * R.restriction x =
      R.restriction (MulAut.conjNormal a x) * P.operator a := by
  rw [R.restriction_apply, R.restriction_apply]
  calc
    P.operator a * P.operator (x : A) =
        P.operator (a * (x : A)) :=
      (R.mul_normal a x).symm
    _ = P.operator
        (((MulAut.conjNormal a x : T.normalSubgroup) : A) * a) := by
      congr 1
      change a * (x : A) =
        (a * (x : A) * a⁻¹) * a
      group
    _ = P.operator
          ((MulAut.conjNormal a x : T.normalSubgroup) : A) *
        P.operator a :=
      R.normal_mul (MulAut.conjNormal a x) a

/-- The inverse ambient operator satisfies the reverse conjugation
identity. -/
theorem operator_symm_mul_conjugate_restriction
    (R : AssociatedProjectiveRepresentation T V P)
    (a : A) (x : T.normalSubgroup) :
    (P.operator a)⁻¹ * R.restriction (MulAut.conjNormal a x) =
      R.restriction x * (P.operator a)⁻¹ := by
  have h := R.operator_mul_restriction a x
  calc
    (P.operator a)⁻¹ *
        R.restriction (MulAut.conjNormal a x) =
      (P.operator a)⁻¹ *
        (R.restriction (MulAut.conjNormal a x) *
          P.operator a) *
          (P.operator a)⁻¹ := by group
    _ = (P.operator a)⁻¹ *
        (P.operator a * R.restriction x) *
          (P.operator a)⁻¹ := by rw [h]
    _ = R.restriction x * (P.operator a)⁻¹ := by group

/-- Comparing two associated lifts at one ambient element gives another
equivalence between their normal restrictions. -/
def comparisonEquiv
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction))
    (a : A) :
    Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction) := by
  let e :
      V ≃ₗ[ℂ] W :=
    ((P.operator a).trans E.toLinearEquiv).trans
      (Q.operator a).symm
  apply Representation.Equiv.mk e
  intro x
  apply LinearMap.ext
  intro v
  change
    (Q.operator a)⁻¹
        (E (P.operator a (R.restriction x v))) =
      S.restriction x
        ((Q.operator a)⁻¹ (E (P.operator a v)))
  have hR :=
    DFunLike.congr_fun
      (R.operator_mul_restriction a x) v
  change
    P.operator a (R.restriction x v) =
      R.restriction (MulAut.conjNormal a x)
        (P.operator a v)
    at hR
  rw [hR]
  have hE :=
    LinearMap.congr_fun
      (E.isIntertwining'
        (MulAut.conjNormal a x))
      (P.operator a v)
  change
    E (R.restriction (MulAut.conjNormal a x)
      (P.operator a v)) =
      S.restriction (MulAut.conjNormal a x)
        (E (P.operator a v))
    at hE
  rw [hE]
  have hQ :=
    S.operator_symm_mul_conjugate_restriction a x
  exact DFunLike.congr_fun hQ (E (P.operator a v))

/-- Pointwise form of the comparison equivalence. -/
@[simp]
theorem comparisonEquiv_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction))
    (a : A) (v : V) :
    comparisonEquiv R S E a v =
      (Q.operator a)⁻¹ (E (P.operator a v)) :=
  rfl

/-- The quotient of the comparison equivalence by the fixed restriction
equivalence is an automorphism of the first restriction representation. -/
def comparisonEndEquiv
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction))
    (a : A) :
    Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction R.restriction) :=
  (comparisonEquiv R S E a).trans E.symm

@[simp]
theorem comparisonEndEquiv_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction))
    (a : A) (v : V) :
    comparisonEndEquiv R S E a v =
      E.symm ((Q.operator a)⁻¹ (E (P.operator a v))) :=
  rfl

/-- Schur uniqueness at a single ambient element: after fixing an
equivalence of the normal restrictions, the two chosen projective operators
differ by a nonzero scalar. -/
theorem exists_operator_scalar
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction))
    (a : A) :
    ∃ c : ℂˣ, ∀ v : V,
      E (P.operator a v) =
        (c : ℂ) • Q.operator a (E v) := by
  let D := comparisonEndEquiv R S E a
  let homEquiv :
      (R.fdRestriction ⟶ R.fdRestriction) ≃ₗ[ℂ]
        Representation.IntertwiningMap
          R.fdRestriction.ρ R.fdRestriction.ρ :=
    (FDRep.forget₂HomLinearEquiv
      R.fdRestriction R.fdRestriction).symm |>.trans
        (Rep.homLinearEquiv _ _)
  let d : R.fdRestriction ⟶ R.fdRestriction :=
    homEquiv.symm D.toIntertwiningMap
  obtain ⟨c, hc⟩ :=
    endomorphism_simple_eq_smul_id ℂ d
  have hpoint : ∀ v : V, c • v = D v := by
    intro v
    have hv := ConcreteCategory.congr_hom hc v
    change c • v = D v at hv
    exact hv
  have hc0 : c ≠ 0 := by
    intro hc0
    obtain ⟨v : V, hv⟩ := exists_ne (0 : V)
    have hzero : D v = 0 := by
      rw [← hpoint v, hc0, zero_smul]
    apply hv
    apply D.toLinearEquiv.injective
    simpa using hzero
  refine ⟨Units.mk0 c hc0, fun v ↦ ?_⟩
  have h :=
    congrArg
      (fun z : V ↦ Q.operator a (E z))
      (hpoint v)
  simpa [D] using h.symm

/-- A fixed equivalence of normal restrictions determines the scalar
cochain comparing the two associated lifts. -/
def gaugeScalar
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction)) :
    A → ℂˣ :=
  fun a ↦ Classical.choose (exists_operator_scalar R S E a)

/-- Defining operator identity for the comparison scalar cochain. -/
theorem gaugeScalar_spec
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction))
    (a : A) (v : V) :
    E (P.operator a v) =
      (gaugeScalar R S E a : ℂ) •
        Q.operator a (E v) :=
  Classical.choose_spec (exists_operator_scalar R S E a) v

/-- The comparison scalar is one on the normal subgroup. -/
theorem gaugeScalar_normal
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction))
    (x : T.normalSubgroup) :
    gaugeScalar R S E (x : A) = 1 := by
  obtain ⟨v : V, hv⟩ := exists_ne (0 : V)
  have hscalar :=
    gaugeScalar_spec R S E (x : A) v
  have hintertwining :=
    LinearMap.congr_fun (E.isIntertwining' x) v
  change
    E (R.restriction x v) =
      S.restriction x (E v)
    at hintertwining
  rw [R.restriction_apply, S.restriction_apply]
    at hintertwining
  have hw :
      Q.operator (x : A) (E v) ≠ 0 := by
    intro hzero
    apply hv
    apply E.toLinearEquiv.injective
    apply (Q.operator (x : A)).injective
    simpa using hzero
  apply Units.ext
  apply smul_left_injective ℂ hw
  simpa only [Units.val_one, one_smul] using
    hscalar.symm.trans hintertwining

/-- Pointwise conjugacy between the first lift and the rescaling of the
second lift by the comparison cochain. -/
theorem gauge_operator_eq
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction))
    (a : A) (v : V) :
    E (P.operator a v) =
      (Q.rescale (gaugeScalar R S E)).operator a (E v) := by
  rw [ProjectiveRepresentation.rescale_operator,
    LinearEquiv.mul_apply, scalarLinearEquiv_apply]
  exact gaugeScalar_spec R S E a v

omit [Finite A] [Module.Finite ℂ V] [Module.Finite ℂ W]
    [Nontrivial W] in
/-- Conjugate projective lifts have literally equal factor sets. -/
theorem factor_eq_of_equiv_operator_eq
    (E : V ≃ₗ[ℂ] W)
    (hoperator : ∀ (a : A) (v : V),
      E (P.operator a v) = Q.operator a (E v))
    (g h : A) :
    P.factor g h = Q.factor g h := by
  obtain ⟨v : V, hv⟩ := exists_ne (0 : V)
  have hw :
      Q.operator (g * h) (E v) ≠ 0 := by
    intro hzero
    apply hv
    apply E.injective
    apply (Q.operator (g * h)).injective
    simpa using hzero
  apply Units.ext
  apply smul_left_injective ℂ hw
  calc
    (P.factor g h : ℂ) • Q.operator (g * h) (E v) =
        E ((P.factor g h : ℂ) •
          P.operator (g * h) v) := by
      rw [map_smul, hoperator]
    _ = E (P.operator g (P.operator h v)) := by
      congr 1
      exact
        (DFunLike.congr_fun (P.map_mul g h) v).symm
    _ = Q.operator g (E (P.operator h v)) :=
      hoperator g (P.operator h v)
    _ = Q.operator g (Q.operator h (E v)) := by
      rw [hoperator h v]
    _ = (Q.factor g h : ℂ) •
        Q.operator (g * h) (E v) :=
      DFunLike.congr_fun (Q.map_mul g h) (E v)

/-- The first factor set is exactly the factor set of the gauge-rescaled
second lift. -/
theorem gauge_factor_eq
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction))
    (g h : A) :
    P.factor g h =
      (Q.rescale (gaugeScalar R S E)).factor g h :=
  factor_eq_of_equiv_operator_eq E.toLinearEquiv
    (gauge_operator_eq R S E) g h

/-- The factor sets of associated projective representations of the same
character triple are cohomologous. -/
theorem factorSet_cohomologous
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q) :
    Q.factorSet.Cohomologous P.factorSet := by
  let E := restrictionEquiv R S
  refine ⟨gaugeScalar R S E, ?_⟩
  calc
    P.factorSet =
        (Q.rescale (gaugeScalar R S E)).factorSet := by
      ext g h
      exact congrArg
        (fun z : ℂˣ ↦ (z : ℂ))
        (gauge_factor_eq R S E g h)
    _ = Q.factorSet.gauge (gaugeScalar R S E) :=
      Q.rescale_factorSet _

/-- The comparison cochain is constant on left normal cosets. -/
theorem gaugeScalar_normal_mul
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction))
    (x : T.normalSubgroup) (a : A) :
    gaugeScalar R S E ((x : A) * a) =
      gaugeScalar R S E a := by
  have hfactor := gauge_factor_eq R S E (x : A) a
  rw [R.factor_normal_left,
    ProjectiveRepresentation.rescale_factor,
    S.factor_normal_left,
    gaugeScalar_normal R S E x] at hfactor
  have hdiv :
      gaugeScalar R S E a /
          gaugeScalar R S E ((x : A) * a) =
        1 := by
    simpa using hfactor.symm
  exact (div_eq_one.mp hdiv).symm

/-- The comparison cochain is constant on right normal cosets. -/
theorem gaugeScalar_mul_normal
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction))
    (a : A) (x : T.normalSubgroup) :
    gaugeScalar R S E (a * (x : A)) =
      gaugeScalar R S E a := by
  have hfactor := gauge_factor_eq R S E a (x : A)
  rw [R.factor_normal_right,
    ProjectiveRepresentation.rescale_factor,
    S.factor_normal_right,
    gaugeScalar_normal R S E x] at hfactor
  have hdiv :
      gaugeScalar R S E a /
          gaugeScalar R S E (a * (x : A)) =
        1 := by
    simpa using hfactor.symm
  exact (div_eq_one.mp hdiv).symm

/-- Rescaling by the comparison cochain preserves associatedness.

The coset laws above are exactly what is needed for the two normal
multiplication axioms. -/
def rescaleAssociated
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction)) :
    AssociatedProjectiveRepresentation T W
      (Q.rescale (gaugeScalar R S E)) where
  restriction := S.restriction
  restriction_apply x := by
    rw [ProjectiveRepresentation.rescale_operator,
      gaugeScalar_normal R S E x, map_one, one_mul]
    exact S.restriction_apply x
  restriction_simple := S.restriction_simple
  restriction_character := S.restriction_character
  normal_mul x a := by
    rw [ProjectiveRepresentation.rescale_operator,
      ProjectiveRepresentation.rescale_operator,
      ProjectiveRepresentation.rescale_operator,
      gaugeScalar_normal_mul R S E x a,
      gaugeScalar_normal R S E x,
      map_one, one_mul, S.normal_mul]
    calc
      scalarLinearEquiv ℂ W (gaugeScalar R S E a) *
          (Q.operator (x : A) * Q.operator a) =
        (scalarLinearEquiv ℂ W (gaugeScalar R S E a) *
            Q.operator (x : A)) *
          Q.operator a := (mul_assoc _ _ _).symm
      _ = (Q.operator (x : A) *
            scalarLinearEquiv ℂ W (gaugeScalar R S E a)) *
          Q.operator a := by
        rw [scalarLinearEquiv_comm]
      _ = Q.operator (x : A) *
          (scalarLinearEquiv ℂ W (gaugeScalar R S E a) *
            Q.operator a) := mul_assoc _ _ _
  mul_normal a x := by
    rw [ProjectiveRepresentation.rescale_operator,
      ProjectiveRepresentation.rescale_operator,
      ProjectiveRepresentation.rescale_operator,
      gaugeScalar_mul_normal R S E a x,
      gaugeScalar_normal R S E x,
      map_one, one_mul, S.mul_normal]
    exact (mul_assoc _ _ _).symm

/-- Strong uniqueness form: after a normal-trivial, coset-constant gauge
change, two associated projective lifts are exactly conjugate and have
literally equal factor sets. -/
theorem exists_exact_rescaling
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q) :
    ∃ (E : Representation.Equiv
        (linearRepresentationOfAction R.restriction)
        (linearRepresentationOfAction S.restriction))
      (c : A → ℂˣ),
      (∀ x : T.normalSubgroup, c (x : A) = 1) ∧
      (∀ (x : T.normalSubgroup) (a : A),
        c ((x : A) * a) = c a) ∧
      (∀ (a : A) (x : T.normalSubgroup),
        c (a * (x : A)) = c a) ∧
      Nonempty
        (AssociatedProjectiveRepresentation T W (Q.rescale c)) ∧
      (∀ (a : A) (v : V),
        E (P.operator a v) =
          (Q.rescale c).operator a (E v)) ∧
      ∀ g h : A,
        P.factor g h = (Q.rescale c).factor g h := by
  let E := restrictionEquiv R S
  let c := gaugeScalar R S E
  exact
    ⟨E, c,
      gaugeScalar_normal R S E,
      gaugeScalar_normal_mul R S E,
      gaugeScalar_mul_normal R S E,
      ⟨rescaleAssociated R S E⟩,
      gauge_operator_eq R S E,
      gauge_factor_eq R S E⟩

end AssociatedProjectiveRepresentation

namespace AssociatedProjectiveRepresentation

/-! ### Comparison along an identification of normal groups -/

universe u'

variable {A₁ : Type u} {A₂ : Type u'} [Finite A₁] [Finite A₂]
  [Group A₁] [Group A₂]
variable {T₁ : CharacterTriple A₁} {T₂ : CharacterTriple A₂}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A₁ V}
  {Q : ProjectiveRepresentation ℂ A₂ W}

/-- Identify the normal restrictions of associated lifts after identifying
the normal groups and their irreducible characters. -/
def restrictionEquivAlong
    (R : AssociatedProjectiveRepresentation T₁ V P)
    (S : AssociatedProjectiveRepresentation T₂ W Q)
    (e : T₁.normalSubgroup ≃* T₂.normalSubgroup)
    (hchar : ∀ x : T₁.normalSubgroup,
      T₁.character.values x =
        T₂.character.values (e x)) :
    Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction
        (S.restriction.comp e.toMonoidHom)) := by
  let Wres : FDRep ℂ T₁.normalSubgroup :=
    FDRep.of
      (linearRepresentationOfAction
        (S.restriction.comp e.toMonoidHom))
  let F : FDRep ℂ T₂.normalSubgroup ≌
      FDRep ℂ T₁.normalSubgroup :=
    Action.resEquiv (FGModuleCat ℂ) e
  letI : Simple Wres := by
    change Simple (F.functor.obj S.fdRestriction)
    exact CategoryTheory.simple_obj F.functor S.fdRestriction
  have hWchar :
      Wres.character = T₁.character.values := by
    funext x
    change
      LinearMap.trace ℂ W (S.restriction (e x)) =
        T₁.character.values x
    calc
      LinearMap.trace ℂ W (S.restriction (e x)) =
          T₂.character.values (e x) :=
        congrFun S.restriction_character (e x)
      _ = T₁.character.values x := (hchar x).symm
  let i :=
    Classical.choice
      (FDRep.nonempty_iso_of_character_eq
        R.fdRestriction Wres
        (R.fdRestriction_character.trans hWchar.symm))
  let E := FDRep.isoToLinearEquiv i
  apply Representation.Equiv.mk E
  intro x
  have hconj := FDRep.Iso.conj_ρ i x
  apply LinearMap.ext
  intro v
  have hv := LinearMap.congr_fun hconj (E v)
  simpa [E, Wres, LinearEquiv.conj_apply] using hv.symm

/-- The condition that two ambient elements induce the same automorphism
after identifying their normal groups. -/
def InducesSameAutomorphism
    (e : T₁.normalSubgroup ≃* T₂.normalSubgroup)
    (a₁ : A₁) (a₂ : A₂) : Prop :=
  ∀ x : T₁.normalSubgroup,
    e (MulAut.conjNormal a₁ x) =
      MulAut.conjNormal a₂ (e x)

/-- Matched ambient automorphisms give a comparison equivalence between the
identified normal restrictions. -/
def comparisonEquivAlong
    (R : AssociatedProjectiveRepresentation T₁ V P)
    (S : AssociatedProjectiveRepresentation T₂ W Q)
    (e : T₁.normalSubgroup ≃* T₂.normalSubgroup)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction
        (S.restriction.comp e.toMonoidHom)))
    (a₁ : A₁) (a₂ : A₂)
    (ha : InducesSameAutomorphism e a₁ a₂) :
    Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction
        (S.restriction.comp e.toMonoidHom)) := by
  let f :
      V ≃ₗ[ℂ] W :=
    ((P.operator a₁).trans E.toLinearEquiv).trans
      (Q.operator a₂).symm
  apply Representation.Equiv.mk f
  intro x
  apply LinearMap.ext
  intro v
  change
    (Q.operator a₂)⁻¹
        (E (P.operator a₁ (R.restriction x v))) =
      S.restriction (e x)
        ((Q.operator a₂)⁻¹ (E (P.operator a₁ v)))
  have hR :=
    DFunLike.congr_fun
      (R.operator_mul_restriction a₁ x) v
  change
    P.operator a₁ (R.restriction x v) =
      R.restriction (MulAut.conjNormal a₁ x)
        (P.operator a₁ v)
    at hR
  rw [hR]
  have hE :=
    LinearMap.congr_fun
      (E.isIntertwining'
        (MulAut.conjNormal a₁ x))
      (P.operator a₁ v)
  change
    E (R.restriction (MulAut.conjNormal a₁ x)
      (P.operator a₁ v)) =
      S.restriction
        (e (MulAut.conjNormal a₁ x))
        (E (P.operator a₁ v))
    at hE
  rw [hE, ha x]
  exact DFunLike.congr_fun
    (S.operator_symm_mul_conjugate_restriction
      a₂ (e x))
    (E (P.operator a₁ v))

@[simp]
theorem comparisonEquivAlong_apply
    (R : AssociatedProjectiveRepresentation T₁ V P)
    (S : AssociatedProjectiveRepresentation T₂ W Q)
    (e : T₁.normalSubgroup ≃* T₂.normalSubgroup)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction
        (S.restriction.comp e.toMonoidHom)))
    (a₁ : A₁) (a₂ : A₂)
    (ha : InducesSameAutomorphism e a₁ a₂)
    (v : V) :
    comparisonEquivAlong R S e E a₁ a₂ ha v =
      (Q.operator a₂)⁻¹ (E (P.operator a₁ v)) :=
  rfl

/-- Cross-ambient Schur uniqueness: matched automorphisms have projective
operators differing by a nonzero scalar after the normal restrictions are
identified. -/
theorem exists_operator_scalar_along
    (R : AssociatedProjectiveRepresentation T₁ V P)
    (S : AssociatedProjectiveRepresentation T₂ W Q)
    (e : T₁.normalSubgroup ≃* T₂.normalSubgroup)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction
        (S.restriction.comp e.toMonoidHom)))
    (a₁ : A₁) (a₂ : A₂)
    (ha : InducesSameAutomorphism e a₁ a₂) :
    ∃ c : ℂˣ, ∀ v : V,
      E (P.operator a₁ v) =
        (c : ℂ) • Q.operator a₂ (E v) := by
  let F := comparisonEquivAlong R S e E a₁ a₂ ha
  let D := F.trans E.symm
  let homEquiv :
      (R.fdRestriction ⟶ R.fdRestriction) ≃ₗ[ℂ]
        Representation.IntertwiningMap
          R.fdRestriction.ρ R.fdRestriction.ρ :=
    (FDRep.forget₂HomLinearEquiv
      R.fdRestriction R.fdRestriction).symm |>.trans
        (Rep.homLinearEquiv _ _)
  let d : R.fdRestriction ⟶ R.fdRestriction :=
    homEquiv.symm D.toIntertwiningMap
  obtain ⟨c, hc⟩ :=
    endomorphism_simple_eq_smul_id ℂ d
  have hpoint : ∀ v : V, c • v = D v := by
    intro v
    have hv := ConcreteCategory.congr_hom hc v
    change c • v = D v at hv
    exact hv
  have hc0 : c ≠ 0 := by
    intro hc0
    obtain ⟨v : V, hv⟩ := exists_ne (0 : V)
    have hzero : D v = 0 := by
      rw [← hpoint v, hc0, zero_smul]
    apply hv
    apply D.toLinearEquiv.injective
    simpa using hzero
  refine ⟨Units.mk0 c hc0, fun v ↦ ?_⟩
  have hE := congrArg E (hpoint v)
  change
    E (c • v) =
      E (E.symm (F v))
    at hE
  rw [map_smul, E.apply_symm_apply] at hE
  change
    c • E v =
      (Q.operator a₂)⁻¹ (E (P.operator a₁ v))
    at hE
  have hE' :
      c • E v =
        (Q.operator a₂)⁻¹ (E (P.operator a₁ v)) :=
    hE
  have hQ := congrArg (Q.operator a₂) hE'
  simpa using hQ.symm

end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
