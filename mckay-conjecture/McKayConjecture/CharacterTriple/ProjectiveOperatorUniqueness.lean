/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedOperatorTransport

/-!
# Projective uniqueness of operators implementing a normal action

An associated projective operator is determined up to scalar by the
automorphism that it induces on the irreducible normal restriction.  This
file records the slightly more general form needed by tensor-permutation
constructions: the competing operator need not itself be part of an
associated projective representation.
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
variable {Q : ProjectiveRepresentation ℂ A W}

/-- An arbitrary invertible operator implementing conjugation on a simple
normal representation differs by a scalar from the corresponding operator
of an associated projective representation. -/
theorem exists_operator_scalar_of_normal_covariance
    (S : AssociatedProjectiveRepresentation T W Q)
    (D : T.normalSubgroup →* (V ≃ₗ[ℂ] V))
    (hDsimple :
      Simple (FDRep.of (linearRepresentationOfAction D)))
    (E : Representation.Equiv
      (linearRepresentationOfAction D)
      (linearRepresentationOfAction S.restriction))
    (a : A)
    (f : V ≃ₗ[ℂ] V)
    (hcovariance :
      ∀ x : T.normalSubgroup,
        f * D x =
          D (MulAut.conjNormal a x) * f) :
    ∃ c : ℂˣ, ∀ v : V,
      E (f v) =
        (c : ℂ) • Q.operator a (E v) := by
  let F :
      Representation.Equiv
        (linearRepresentationOfAction D)
        (linearRepresentationOfAction S.restriction) := by
    let e : V ≃ₗ[ℂ] W :=
      (f.trans E.toLinearEquiv).trans
        (Q.operator a).symm
    apply Representation.Equiv.mk e
    intro x
    apply LinearMap.ext
    intro v
    change
      (Q.operator a)⁻¹
          (E (f (D x v))) =
        S.restriction x
          ((Q.operator a)⁻¹ (E (f v)))
    have hf :=
      DFunLike.congr_fun (hcovariance x) v
    change
      f (D x v) =
        D (MulAut.conjNormal a x) (f v)
      at hf
    rw [hf]
    have hE :=
      LinearMap.congr_fun
        (E.isIntertwining'
          (MulAut.conjNormal a x))
        (f v)
    change
      E (D (MulAut.conjNormal a x) (f v)) =
        S.restriction (MulAut.conjNormal a x)
          (E (f v))
      at hE
    rw [hE]
    exact DFunLike.congr_fun
      (S.operator_symm_mul_conjugate_restriction a x)
      (E (f v))
  let H := F.trans E.symm
  letI :
      Simple (FDRep.of (linearRepresentationOfAction D)) :=
    hDsimple
  let homEquiv :
      (FDRep.of (linearRepresentationOfAction D) ⟶
          FDRep.of (linearRepresentationOfAction D)) ≃ₗ[ℂ]
        Representation.IntertwiningMap
          (FDRep.of (linearRepresentationOfAction D)).ρ
          (FDRep.of (linearRepresentationOfAction D)).ρ :=
    (FDRep.forget₂HomLinearEquiv
      (FDRep.of (linearRepresentationOfAction D))
      (FDRep.of (linearRepresentationOfAction D))).symm |>.trans
        (Rep.homLinearEquiv _ _)
  let h :
      FDRep.of (linearRepresentationOfAction D) ⟶
        FDRep.of (linearRepresentationOfAction D) :=
    homEquiv.symm H.toIntertwiningMap
  obtain ⟨c, hc⟩ :=
    endomorphism_simple_eq_smul_id ℂ h
  have hpoint : ∀ v : V, c • v = H v := by
    intro v
    have hv := ConcreteCategory.congr_hom hc v
    change c • v = H v at hv
    exact hv
  have hc0 : c ≠ 0 := by
    intro hc0
    obtain ⟨v : V, hv⟩ := exists_ne (0 : V)
    have hzero : H v = 0 := by
      rw [← hpoint v, hc0, zero_smul]
    apply hv
    apply H.toLinearEquiv.injective
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
      (Q.operator a)⁻¹ (E (f v))
    at hE
  have hQ := congrArg (Q.operator a) hE
  simpa using hQ.symm

/-- Projective-linear form of
`exists_operator_scalar_of_normal_covariance`. -/
theorem projectiveClass_conjugateOperator_eq_of_normal_covariance
    (S : AssociatedProjectiveRepresentation T W Q)
    (D : T.normalSubgroup →* (V ≃ₗ[ℂ] V))
    (hDsimple :
      Simple (FDRep.of (linearRepresentationOfAction D)))
    (E : Representation.Equiv
      (linearRepresentationOfAction D)
      (linearRepresentationOfAction S.restriction))
    (a : A)
    (f : V ≃ₗ[ℂ] V)
    (hcovariance :
      ∀ x : T.normalSubgroup,
        f * D x =
          D (MulAut.conjNormal a x) * f) :
    ProjectiveLinearGroup.mk ℂ W
        (conjugateOperator E.toLinearEquiv f) =
      Q.toProjectiveLinearGroup a := by
  obtain ⟨c, hc⟩ :=
    exists_operator_scalar_of_normal_covariance
      S D hDsimple E a f hcovariance
  have hop :
      conjugateOperator E.toLinearEquiv f =
        scalarLinearEquiv ℂ W c * Q.operator a := by
    ext w
    change
      E (f (E.symm w)) =
        (c : ℂ) • Q.operator a w
    simpa only [E.apply_symm_apply] using hc (E.symm w)
  rw [hop, map_mul, ProjectiveLinearGroup.mk_scalar, one_mul]
  rfl

end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
