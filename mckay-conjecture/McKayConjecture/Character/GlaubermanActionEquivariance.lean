/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanAction
import McKayConjecture.Character.OverAlongTransport

/-!
# Equivariance of the action-level Glauberman correspondence

Let `Q ◁ P` act on `A`.  A `P`-invariant character is in particular
`Q`-invariant.  Uniqueness in the Glauberman correspondence for `Q` forces
its correspondent on `A^Q` to be invariant under the induced `P / Q`
action.  This is the equivariance input required for transitivity.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable (P A : Type) [Group P] [Group A]
variable [MulDistribMulAction P A]
variable [Finite P] [Finite A]
variable (Q : Subgroup P) [Q.Normal]
variable {p : ℕ}

/-- Restrict a `P`-invariant character to the action of a subgroup. -/
def actionInvariantCharacterOfSubgroup
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p) :
    ActionInvariantPPrimeIrreducibleCharacter Q A p :=
  ⟨θ.1, fun q a ↦ θ.2 q.1 a⟩

@[simp]
theorem actionInvariantCharacterOfSubgroup_coe
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p) :
    (actionInvariantCharacterOfSubgroup P A Q θ).1 =
      θ.1 :=
  rfl

/-- The automorphism of `A` supplied by an element of the acting group. -/
abbrev actionMulAut (g : P) : MulAut A :=
  MulDistribMulAction.toMulAut P A g

/-- The induced automorphism of `A^Q`. -/
abbrev fixedPointsActionMulAut (g : P) :
    MulAut (FixedPoints.subgroup Q A) :=
  MulDistribMulAction.toMulAut (P ⧸ Q)
    (FixedPoints.subgroup Q A) (g : P ⧸ Q)

/-- The inclusion `A^Q ↪ A` commutes with the automorphisms induced by
every `g ∈ P`. -/
theorem actionFixedPointsInclusion_commutes
    (g : P) :
    (actionMulAut P A g).symm.toMonoidHom.comp
        (actionFixedPointsInclusion Q A) =
      (actionFixedPointsInclusion Q A).comp
        (fixedPointsActionMulAut P A Q g).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro a
  change
    g⁻¹ • (a : A) =
      (((g : P ⧸ Q)⁻¹ • a :
        FixedPoints.subgroup Q A) : A)
  rfl

/-- Simultaneous action by `g ∈ P` on a character of `A` and a character
of `A^Q` preserves restriction multiplicity. -/
theorem restrictionMultiplicity_action
    (g : P)
    (θ : IrreducibleCharacter A)
    (φ : IrreducibleCharacter
      (FixedPoints.subgroup Q A)) :
    restrictionMultiplicity
        (actionFixedPointsInclusion Q A)
        (fixedPointsActionMulAut P A Q g • φ)
        (actionMulAut P A g • θ) =
      restrictionMultiplicity
        (actionFixedPointsInclusion Q A)
        φ θ := by
  exact
    restrictionMultiplicity_comap_equiv
      (actionMulAut P A g).symm
      (fixedPointsActionMulAut P A Q g).symm
      (actionFixedPointsInclusion Q A)
      (actionFixedPointsInclusion Q A)
      (actionFixedPointsInclusion_commutes P A Q g)
      φ θ

/-- A `P`-invariant character is fixed by the induced automorphism action
of every element of `P`. -/
theorem actionMulAut_smul_eq_of_invariant
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p)
    (g : P) :
    actionMulAut P A g • θ.1.1 = θ.1.1 := by
  apply IrreducibleCharacter.ext
  funext a
  rw [IrreducibleCharacter.smul_values]
  exact θ.2 g⁻¹ a

/-- Conjugating a `Q`-invariant character by an element of the ambient
acting group preserves `Q`-invariance because `Q ◁ P`. -/
def actionInvariantCharacterByAmbient
    (g : P)
    (θ : ActionInvariantPPrimeIrreducibleCharacter Q A p) :
    ActionInvariantPPrimeIrreducibleCharacter Q A p := by
  refine ⟨actionMulAut P A g • θ.1, ?_⟩
  intro q a
  change
    (actionMulAut P A g • θ.1.1).values
        ((q : P) • a) =
      (actionMulAut P A g • θ.1.1).values a
  rw [IrreducibleCharacter.smul_values,
    IrreducibleCharacter.smul_values]
  let q' : Q :=
    ⟨g⁻¹ * (q : P) * g,
      by
        simpa using
          (inferInstance : Q.Normal).conj_mem
            (q : P) q.2 g⁻¹⟩
  have harg :
      g⁻¹ • ((q : P) • a) =
        (q' : P) • (g⁻¹ • a) := by
    calc
      g⁻¹ • ((q : P) • a) =
          (g⁻¹ * (q : P)) • a :=
        (mul_smul g⁻¹ (q : P) a).symm
      _ =
          ((g⁻¹ * (q : P) * g) * g⁻¹) • a := by
        congr 1
        group
      _ =
          (q' : P) • (g⁻¹ • a) := by
        exact mul_smul (q' : P) g⁻¹ a
  change
    θ.1.1.values (g⁻¹ • ((q : P) • a)) =
      θ.1.1.values (g⁻¹ • a)
  rw [harg]
  exact θ.2 q' (g⁻¹ • a)

@[simp]
theorem actionInvariantCharacterByAmbient_coe
    (g : P)
    (θ : ActionInvariantPPrimeIrreducibleCharacter Q A p) :
    (actionInvariantCharacterByAmbient P A Q g θ).1 =
      actionMulAut P A g • θ.1 :=
  rfl

/-- Uniqueness forces the action-level correspondence for `Q` to commute
with every element of the ambient acting group `P`. -/
theorem characterEquiv_action
    (d : ActionGlaubermanCorrespondence Q A p)
    (g : P)
    (θ : ActionInvariantPPrimeIrreducibleCharacter Q A p) :
    d.characterEquiv
        (actionInvariantCharacterByAmbient P A Q g θ) =
      fixedPointsActionMulAut P A Q g •
        d.characterEquiv θ := by
  symm
  apply d.eq_correspondent_of_multiplicity_isPPrime
  change
    ¬p ∣
      restrictionMultiplicity
        (actionFixedPointsInclusion Q A)
        (fixedPointsActionMulAut P A Q g •
          (d.characterEquiv θ).1)
        (actionMulAut P A g • θ.1.1)
  rw [restrictionMultiplicity_action P A Q]
  exact d.multiplicity_isPPrime θ

/-- The `Q`-Glauberman correspondent of a `P`-invariant character is fixed
by the action of every element of `P` on `A^Q`. -/
theorem characterEquiv_fixed_by_ambient_action
    (d : ActionGlaubermanCorrespondence Q A p)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p)
    (g : P) :
    fixedPointsActionMulAut P A Q g •
        (d.characterEquiv
          (actionInvariantCharacterOfSubgroup P A Q θ)).1 =
      (d.characterEquiv
        (actionInvariantCharacterOfSubgroup P A Q θ)).1 := by
  let θQ :=
    actionInvariantCharacterOfSubgroup P A Q θ
  let φ := d.characterEquiv θQ
  have hmult :
      ¬p ∣
        restrictionMultiplicity
          (actionFixedPointsInclusion Q A)
          (fixedPointsActionMulAut P A Q g • φ.1)
          θ.1.1 := by
    rw [← actionMulAut_smul_eq_of_invariant
      P A θ g,
      restrictionMultiplicity_action P A Q]
    exact d.multiplicity_isPPrime θQ
  have heq :
      (⟨fixedPointsActionMulAut P A Q g • φ.1,
          φ.2⟩ :
        PPrimeIrreducibleCharacter
          (FixedPoints.subgroup Q A) p) =
        φ :=
    d.eq_correspondent_of_multiplicity_isPPrime
      θQ _ hmult
  exact congrArg Subtype.val heq

/-- A quotient-invariant character of `A^Q` is fixed under the induced
automorphism action on characters. -/
theorem fixedPointsActionMulAut_smul_eq_of_invariant
    (φ :
      ActionInvariantPPrimeIrreducibleCharacter
        (P ⧸ Q) (FixedPoints.subgroup Q A) p)
    (g : P) :
    fixedPointsActionMulAut P A Q g • φ.1.1 =
      φ.1.1 := by
  apply IrreducibleCharacter.ext
  funext a
  rw [IrreducibleCharacter.smul_values]
  exact φ.2 ((g : P ⧸ Q)⁻¹) a

/-- The `Q`-Glauberman correspondent of a `P`-invariant character is
invariant under the quotient action of `P / Q`. -/
def quotientInvariantCorrespondent
    (d : ActionGlaubermanCorrespondence Q A p)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p) :
    ActionInvariantPPrimeIrreducibleCharacter
      (P ⧸ Q) (FixedPoints.subgroup Q A) p := by
  let φ :=
    d.characterEquiv
      (actionInvariantCharacterOfSubgroup P A Q θ)
  refine ⟨φ, ?_⟩
  intro g a
  refine Quotient.inductionOn' g ?_
  intro x
  have hfixed :=
    characterEquiv_fixed_by_ambient_action
      P A Q d θ x⁻¹
  have hvalue :=
    congrArg
      (fun χ : IrreducibleCharacter
          (FixedPoints.subgroup Q A) ↦
        χ.values a)
      hfixed
  rw [IrreducibleCharacter.smul_values] at hvalue
  simpa [fixedPointsActionMulAut] using hvalue

@[simp]
theorem quotientInvariantCorrespondent_coe
    (d : ActionGlaubermanCorrespondence Q A p)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p) :
    (quotientInvariantCorrespondent P A Q d θ).1 =
      d.characterEquiv
        (actionInvariantCharacterOfSubgroup P A Q θ) :=
  by
    apply Subtype.ext
    rfl

/-- A correspondence for `Q` identifies the `P`-invariant characters of
`A` with the `(P / Q)`-invariant characters of `A^Q`.  Equivariance of
the correspondence supplies both directions. -/
def invariantCharacterEquivQuotientInvariantCorrespondent
    (d : ActionGlaubermanCorrespondence Q A p) :
    ActionInvariantPPrimeIrreducibleCharacter P A p ≃
      ActionInvariantPPrimeIrreducibleCharacter
        (P ⧸ Q) (FixedPoints.subgroup Q A) p where
  toFun :=
    quotientInvariantCorrespondent P A Q d
  invFun φ := by
    let θQ :
        ActionInvariantPPrimeIrreducibleCharacter Q A p :=
      d.characterEquiv.symm φ.1
    refine ⟨θQ.1, ?_⟩
    intro g a
    have hsource :
        actionInvariantCharacterByAmbient
            P A Q g⁻¹ θQ =
          θQ := by
      apply d.characterEquiv.injective
      rw [characterEquiv_action P A Q]
      have hfixed :
          fixedPointsActionMulAut P A Q g⁻¹ • φ.1.1 =
            φ.1.1 :=
        fixedPointsActionMulAut_smul_eq_of_invariant
          P A Q φ g⁻¹
      apply Subtype.ext
      simpa [θQ] using hfixed
    have hcharacter :=
      congrArg
        (fun η :
          ActionInvariantPPrimeIrreducibleCharacter Q A p ↦
            η.1.1)
        hsource
    have hvalue :=
      congrArg
        (fun η : IrreducibleCharacter A ↦
          η.values a)
        hcharacter
    change
      (actionMulAut P A g⁻¹ • θQ.1.1).values a =
        θQ.1.1.values a at hvalue
    rw [IrreducibleCharacter.smul_values] at hvalue
    simpa [θQ] using hvalue
  left_inv θ := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [quotientInvariantCorrespondent]
    change
      (d.characterEquiv.symm
        (d.characterEquiv
          (actionInvariantCharacterOfSubgroup
            P A Q θ))).1.1 =
        θ.1.1
    rw [d.characterEquiv.symm_apply_apply]
    rfl
  right_inv φ := by
    apply Subtype.ext
    apply Subtype.ext
    change
      (d.characterEquiv
        (d.characterEquiv.symm φ.1)).1 =
        φ.1.1
    rw [d.characterEquiv.apply_symm_apply]

end McKayConjecture
