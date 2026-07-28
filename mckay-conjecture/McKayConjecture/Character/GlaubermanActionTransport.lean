/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionStrong
import McKayConjecture.Character.OverAlongTransport

/-!
# Transporting action-level Glauberman correspondences

An equivariant pair of group isomorphisms transports fixed points,
invariant irreducible characters, restriction multiplicities, and hence
the entire strong action-level Glauberman correspondence.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable (P Q A B : Type)
variable [Group P] [Group Q] [Group A] [Group B]
variable [MulDistribMulAction P A]
variable [MulDistribMulAction Q B]
variable [Finite P] [Finite Q] [Finite A] [Finite B]
variable {p : ℕ}

/-- An equivariant pair of group isomorphisms induces an isomorphism of
fixed-point subgroups. -/
def actionFixedPointsEquivOfEquivariant
    (eP : Q ≃* P)
    (eA : B ≃* A)
    (hsmul : ∀ q : Q, ∀ b : B,
      eA (q • b) = eP q • eA b) :
    FixedPoints.subgroup Q B ≃*
      FixedPoints.subgroup P A where
  toFun b :=
    ⟨eA b.1, fun g ↦ by
      let q : Q := eP.symm g
      have hfixed := congrArg eA (b.2 q)
      rw [hsmul, eP.apply_symm_apply] at hfixed
      exact hfixed⟩
  invFun a :=
    ⟨eA.symm a.1, fun q ↦ by
      apply eA.injective
      rw [hsmul, eA.apply_symm_apply,
        a.2 (eP q)]⟩
  left_inv b := by
    apply Subtype.ext
    exact eA.symm_apply_apply b.1
  right_inv a := by
    apply Subtype.ext
    exact eA.apply_symm_apply a.1
  map_mul' b c := by
    apply Subtype.ext
    exact eA.map_mul b.1 c.1

@[simp]
theorem actionFixedPointsEquivOfEquivariant_apply_coe
    (eP : Q ≃* P)
    (eA : B ≃* A)
    (hsmul : ∀ q : Q, ∀ b : B,
      eA (q • b) = eP q • eA b)
    (b : FixedPoints.subgroup Q B) :
    ((actionFixedPointsEquivOfEquivariant
      P Q A B eP eA hsmul b :
        FixedPoints.subgroup P A) : A) =
      eA b.1 :=
  rfl

/-- Equivariant group isomorphisms transport invariant prime-to-`p`
irreducible characters. -/
def actionInvariantPPrimeIrreducibleCharacterEquivOfEquivariant
    (eP : Q ≃* P)
    (eA : B ≃* A)
    (hsmul : ∀ q : Q, ∀ b : B,
      eA (q • b) = eP q • eA b) :
    ActionInvariantPPrimeIrreducibleCharacter P A p ≃
      ActionInvariantPPrimeIrreducibleCharacter Q B p where
  toFun θ :=
    ⟨IrreducibleCharacter.pPrimeComapEquiv p eA θ.1,
      fun q b ↦ by
        change
          θ.1.1.values (eA (q • b)) =
            θ.1.1.values (eA b)
        rw [hsmul]
        exact θ.2 (eP q) (eA b)⟩
  invFun η :=
    ⟨IrreducibleCharacter.pPrimeComapEquiv p eA.symm η.1,
      fun g a ↦ by
        have harg :
            eA.symm (g • a) =
              eP.symm g • eA.symm a := by
          apply eA.injective
          rw [eA.apply_symm_apply, hsmul,
            eP.apply_symm_apply, eA.apply_symm_apply]
        change
          η.1.1.values (eA.symm (g • a)) =
            η.1.1.values (eA.symm a)
        rw [harg]
        exact η.2 (eP.symm g) (eA.symm a)⟩
  left_inv θ := by
    apply Subtype.ext
    exact
      (IrreducibleCharacter.pPrimeComapEquiv
        p eA).left_inv θ.1
  right_inv η := by
    apply Subtype.ext
    exact
      (IrreducibleCharacter.pPrimeComapEquiv
        p eA).right_inv η.1

@[simp]
theorem actionInvariantPPrimeIrreducibleCharacterEquivOfEquivariant_apply_coe
    (eP : Q ≃* P)
    (eA : B ≃* A)
    (hsmul : ∀ q : Q, ∀ b : B,
      eA (q • b) = eP q • eA b)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p) :
    (actionInvariantPPrimeIrreducibleCharacterEquivOfEquivariant
      P Q A B eP eA hsmul θ).1.1 =
      θ.1.1.comap eA :=
  rfl

/-- Restriction multiplicity is preserved by an equivariant pair of
group isomorphisms. -/
theorem restrictionMultiplicity_actionEquivOfEquivariant
    (eP : Q ≃* P)
    (eA : B ≃* A)
    (hsmul : ∀ q : Q, ∀ b : B,
      eA (q • b) = eP q • eA b)
    (φ : IrreducibleCharacter
      (FixedPoints.subgroup P A))
    (θ : IrreducibleCharacter A) :
    restrictionMultiplicity
        (actionFixedPointsInclusion Q B)
        (φ.comap
          (actionFixedPointsEquivOfEquivariant
            P Q A B eP eA hsmul))
        (θ.comap eA) =
      restrictionMultiplicity
        (actionFixedPointsInclusion P A)
        φ θ := by
  let eC :=
    actionFixedPointsEquivOfEquivariant
      P Q A B eP eA hsmul
  have hcomm :
      eA.toMonoidHom.comp
          (actionFixedPointsInclusion Q B) =
        (actionFixedPointsInclusion P A).comp
          eC.toMonoidHom := by
    ext b
    rfl
  exact
    restrictionMultiplicity_comap_equiv
      eA eC
      (actionFixedPointsInclusion P A)
      (actionFixedPointsInclusion Q B)
      hcomm φ θ

/-- Transport a strong action Glauberman correspondence through an
equivariant pair of group isomorphisms. -/
def StrongActionGlaubermanCorrespondence.transport
    (eP : Q ≃* P)
    (eA : B ≃* A)
    (hsmul : ∀ q : Q, ∀ b : B,
      eA (q • b) = eP q • eA b)
    (d : StrongActionGlaubermanCorrespondence Q B p) :
    StrongActionGlaubermanCorrespondence P A p := by
  let eC :=
    actionFixedPointsEquivOfEquivariant
      P Q A B eP eA hsmul
  let eSource :=
    actionInvariantPPrimeIrreducibleCharacterEquivOfEquivariant
      (p := p) P Q A B eP eA hsmul
  let eTarget :=
    IrreducibleCharacter.pPrimeComapEquiv p eC
  let e :=
    eSource.trans (d.characterEquiv.trans eTarget.symm)
  refine
    { characterEquiv := e
      multiplicity_isPPrime := ?_
      eq_correspondent_of_multiplicity_isPPrime := ?_ }
  · intro θ
    have htarget :
        (e θ).1.comap eC =
          (d.characterEquiv (eSource θ)).1 := by
      change
        (eTarget
          (eTarget.symm
            (d.characterEquiv (eSource θ)))).1 =
            (d.characterEquiv (eSource θ)).1
      exact
        congrArg Subtype.val
          (eTarget.apply_symm_apply
            (d.characterEquiv (eSource θ)))
    rw [←
      restrictionMultiplicity_actionEquivOfEquivariant
        P Q A B eP eA hsmul]
    rw [htarget]
    exact d.multiplicity_isPPrime (eSource θ)
  · intro θ φ hφ
    have hφ' :
        ¬p ∣
          restrictionMultiplicity
            (actionFixedPointsInclusion Q B)
            (φ.comap eC)
            (eSource θ).1.1 := by
      rw [
        actionInvariantPPrimeIrreducibleCharacterEquivOfEquivariant_apply_coe]
      rw [
        restrictionMultiplicity_actionEquivOfEquivariant
          P Q A B eP eA hsmul]
      exact hφ
    have heq :
        φ.comap eC =
          (d.characterEquiv (eSource θ)).1 :=
      d.eq_correspondent_of_multiplicity_isPPrime
        (eSource θ) (φ.comap eC) hφ'
    apply IrreducibleCharacter.comapEquiv eC |>.injective
    change
      φ.comap eC =
        (e θ).1.comap eC
    calc
      φ.comap eC =
          (d.characterEquiv (eSource θ)).1 :=
        heq
      _ = (e θ).1.comap eC := by
        change
          (d.characterEquiv (eSource θ)).1 =
            (eTarget
              (eTarget.symm
                (d.characterEquiv (eSource θ)))).1
        exact
          congrArg Subtype.val
            (eTarget.apply_symm_apply
              (d.characterEquiv (eSource θ))).symm

end McKayConjecture
