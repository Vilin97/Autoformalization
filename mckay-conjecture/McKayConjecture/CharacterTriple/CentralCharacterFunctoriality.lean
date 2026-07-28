/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralCharacterBijection
import McKayConjecture.CharacterTriple.Transitivity

/-!
# Functoriality of central character correspondences

This file proves the identity law for the character equivalence attached to
a central-isomorphism witness and develops the composition law when the two
witnesses use the same chosen projective representation on their common
middle character triple.

The weaker `MiddleCompatibility` used by `compose` identifies middle factor
sets but not the chosen middle operators.  Their scalar comparison can
therefore retain a nontrivial quotient linear character.  Consequently the
canonical literal composition law is stated for `compose_of_projective_eq`;
removing that hypothesis would require either recording the comparison
cochain or quotienting character correspondences by the resulting twists.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CharacterTriple
namespace CentralIsomorphismWitness

section Identity

variable {A : Type} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- The all-character correspondence of the identity witness fixes every
character pointwise. -/
@[simp]
theorem centralCharacterEquiv_refl_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      T.normalSubgroup.subtype T.character) :
    (refl R).centralCharacterEquiv χ = χ := by
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext a
  change
    ((refl R).rightMultiplicityCharacter χ.1 χ.2).values a =
      χ.1.values a
  rw [(refl R).rightMultiplicityCharacter_values χ.1 χ.2]
  calc
    ((refl R).rightMultiplicityFDRep χ.1 χ.2).character a =
        χ.1.realization.character a := by
      exact congrFun
        (Representation.char_iso
          ((refl R).leftMultiplicityEvaluationEquiv χ.1 χ.2)) a
    _ = χ.1.values a :=
      congrFun χ.1.realization_character a

/-- Extensional identity law for the all-character equivalence. -/
@[simp]
theorem centralCharacterEquiv_refl
    (R : AssociatedProjectiveRepresentation T V P) :
    (refl R).centralCharacterEquiv = Equiv.refl _ := by
  ext χ
  exact centralCharacterEquiv_refl_apply R χ

/-- Application law for the prime-to-`p` identity correspondence. -/
@[simp]
theorem centralPPrimeCharacterEquiv_refl_apply
    {p : ℕ} (hp : p.Prime)
    (R : AssociatedProjectiveRepresentation T V P)
    (hT : T.character.IsPPrimeDegree p)
    (χ :
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character) :
    (refl R).centralPPrimeCharacterEquiv hp hT hT χ = χ := by
  apply Subtype.ext
  exact centralCharacterEquiv_refl_apply R χ.1

/-- Extensional identity law for the prime-to-`p` equivalence. -/
@[simp]
theorem centralPPrimeCharacterEquiv_refl
    {p : ℕ} (hp : p.Prime)
    (R : AssociatedProjectiveRepresentation T V P)
    (hT : T.character.IsPPrimeDegree p) :
    (refl R).centralPPrimeCharacterEquiv hp hT hT =
      Equiv.refl _ := by
  ext χ
  exact centralPPrimeCharacterEquiv_refl_apply hp R hT χ

end Identity

section Composition

variable {A B D : Type}
  [Finite A] [Finite B] [Finite D]
  [Group A] [Group B] [Group D]
variable {T : CharacterTriple A} {U : CharacterTriple B}
  {S : CharacterTriple D}
variable {V W Y : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup Y] [Module ℂ Y] [Module.Finite ℂ Y] [Nontrivial Y]



/-- The projective multiplicity factor after the first transport, viewed on
the middle ambient group. -/
abbrev compositionMiddleProjective
    (C₁ : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A) :
    ProjectiveRepresentation ℂ B (C₁.leftMultiplicitySpace χ) :=
  (C₁.leftMultiplicityProjective χ).comap C₁.embedding

/-- The intermediate character produced by the first witness. -/
abbrev compositionMiddleCharacter
    (C₁ : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    IrreducibleCharacter B :=
  C₁.rightMultiplicityCharacter χ hχ

theorem compositionMiddle_hasInverseFactorSet
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U S W Y)
    (hP : C₁.rightProjective = C₂.leftProjective)
    (χ : IrreducibleCharacter A) :
    C₂.leftProjective.HasInverseFactorSet
      (compositionMiddleProjective C₁ χ) := by
  rw [← hP]
  exact C₁.right_hasInverseFactorSet
    (C₁.leftMultiplicityProjective χ)
    (C₁.leftMultiplicity_hasInverseFactorSet χ)

theorem compositionMiddle_isTrivialOnNormal
    (C₁ : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A) :
    (compositionMiddleProjective C₁ χ).IsTrivialOnNormal U :=
  C₁.right_isTrivialOnNormal
    (C₁.leftMultiplicityProjective χ)
    (C₁.leftMultiplicity_isTrivialOnNormal χ)



omit [Finite A] [Finite B] [Finite D] [Module.Finite ℂ V] [Nontrivial V]
  [Module.Finite ℂ W] [Nontrivial W] [Module.Finite ℂ Y] [Nontrivial Y] in
/-- Transport an equivalence of cancelled tensor representations across
equality of the first projective factor. -/
def cancelTensorRepresentationEquivOfLeftEq
    {P P' : ProjectiveRepresentation ℂ B W}
    {M N : Type}
    [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N]
    (Q : ProjectiveRepresentation ℂ B M)
    (hP : P = P')
    (hQ : P.HasInverseFactorSet Q)
    (hQ' : P'.HasInverseFactorSet Q)
    (D : Representation ℂ B N)
    (e : Representation.Equiv
      (P.cancelTensorRepresentation Q hQ) D) :
    Representation.Equiv
      (P'.cancelTensorRepresentation Q hQ') D := by
  subst P'
  exact e

/-- The first concrete tensor realization, rewritten with the second
witness's literally equal middle projective lift. -/
def compositionMiddleRealizationEquiv
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U S W Y)
    (hP : C₁.rightProjective = C₂.leftProjective)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Representation.Equiv
      (C₂.leftProjective.cancelTensorRepresentation
        (compositionMiddleProjective C₁ χ)
        (compositionMiddle_hasInverseFactorSet C₁ C₂ hP χ))
      (compositionMiddleCharacter C₁ χ hχ).realization.ρ := by
  let e₀ := C₁.rightMultiplicityRealizationEquiv χ hχ
  change Representation.Equiv
    (C₁.rightProjective.cancelTensorRepresentation
      (compositionMiddleProjective C₁ χ)
      (C₁.right_hasInverseFactorSet
        (C₁.leftMultiplicityProjective χ)
        (C₁.leftMultiplicity_hasInverseFactorSet χ)))
    (compositionMiddleCharacter C₁ χ hχ).realization.ρ at e₀
  exact
    cancelTensorRepresentationEquivOfLeftEq
      (compositionMiddleProjective C₁ χ) hP
      (C₁.right_hasInverseFactorSet
        (C₁.leftMultiplicityProjective χ)
        (C₁.leftMultiplicity_hasInverseFactorSet χ))
      (compositionMiddle_hasInverseFactorSet C₁ C₂ hP χ)
      (compositionMiddleCharacter C₁ χ hχ).realization.ρ e₀

theorem compositionMiddle_isIrreducible
    (C₁ : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (compositionMiddleProjective C₁ χ).IsIrreducible := by
  exact
    (C₁.multiplicity_isIrreducible_iff_comap
      (C₁.leftMultiplicityProjective χ)
      (C₁.leftMultiplicity_hasInverseFactorSet χ)
      (C₁.leftMultiplicity_isTrivialOnNormal χ)).mp
      (C₁.leftMultiplicityProjective_isIrreducible χ hχ)

/-- The exact recovery intertwiner from the first multiplicity factor to the
second multiplicity factor. -/
def compositionRecoveryIntertwiningMap
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U S W Y)
    (hP : C₁.rightProjective = C₂.leftProjective)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (compositionMiddleProjective C₁ χ).IntertwiningMap
      (C₂.leftMultiplicityProjective
        (compositionMiddleCharacter C₁ χ hχ)) := by
  letI : Nontrivial (C₁.leftMultiplicitySpace χ) :=
    C₁.leftMultiplicitySpace_nontrivial χ hχ
  exact
    MultiplicityProjective.tensorFactorMultiplicityIntertwiningMap
      C₂.leftAssociated
      (compositionMiddleProjective C₁ χ)
      (compositionMiddle_hasInverseFactorSet C₁ C₂ hP χ)
      (compositionMiddle_isTrivialOnNormal C₁ χ)
      (compositionMiddleCharacter C₁ χ hχ).realization.ρ
      (compositionMiddleRealizationEquiv C₁ C₂ hP χ hχ)

theorem compositionRecoveryIntertwiningMap_ne_zero
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U S W Y)
    (hP : C₁.rightProjective = C₂.leftProjective)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (compositionRecoveryIntertwiningMap
      C₁ C₂ hP χ hχ).toLinearMap ≠ 0 := by
  letI : Nontrivial (C₁.leftMultiplicitySpace χ) :=
    C₁.leftMultiplicitySpace_nontrivial χ hχ
  exact
    MultiplicityProjective.tensorFactorMultiplicityIntertwiningMap_ne_zero
      C₂.leftAssociated
      (compositionMiddleProjective C₁ χ)
      (compositionMiddle_hasInverseFactorSet C₁ C₂ hP χ)
      (compositionMiddle_isTrivialOnNormal C₁ χ)
      (compositionMiddleCharacter C₁ χ hχ).realization.ρ
      (compositionMiddleRealizationEquiv C₁ C₂ hP χ hχ)

/-- The recovered multiplicity factor is linearly equivalent to the original
factor. -/
def compositionRecoveryLinearEquiv
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U S W Y)
    (hP : C₁.rightProjective = C₂.leftProjective)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    C₁.leftMultiplicitySpace χ ≃ₗ[ℂ]
      C₂.leftMultiplicitySpace
        (compositionMiddleCharacter C₁ χ hχ) := by
  letI : Nontrivial (C₁.leftMultiplicitySpace χ) :=
    C₁.leftMultiplicitySpace_nontrivial χ hχ
  exact
    (compositionRecoveryIntertwiningMap C₁ C₂ hP χ hχ).linearEquivOfNeZero
      (compositionMiddle_isIrreducible C₁ χ hχ)
      (C₂.leftMultiplicityProjective_isIrreducible
        (compositionMiddleCharacter C₁ χ hχ)
        (C₁.rightMultiplicityCharacter_liesOver χ hχ))
      (compositionRecoveryIntertwiningMap_ne_zero C₁ C₂ hP χ hχ)

theorem compositionRecoveryLinearEquiv_intertwines
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U S W Y)
    (hP : C₁.rightProjective = C₂.leftProjective)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (b : B) (z : C₁.leftMultiplicitySpace χ) :
    compositionRecoveryLinearEquiv C₁ C₂ hP χ hχ
        ((compositionMiddleProjective C₁ χ).operator b z) =
      (C₂.leftMultiplicityProjective
          (compositionMiddleCharacter C₁ χ hχ)).operator b
        (compositionRecoveryLinearEquiv C₁ C₂ hP χ hχ z) :=
  (compositionRecoveryIntertwiningMap C₁ C₂ hP χ hχ).intertwines_apply b z

/-- Multiplicity recovery identifies the traces used by one-step and
two-step transport. -/
theorem compositionalMultiplicity_trace_eq
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U S W Y)
    (hP : C₁.rightProjective = C₂.leftProjective)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (b : B) :
    (C₂.leftMultiplicityProjective
        (compositionMiddleCharacter C₁ χ hχ)).traceFunction b =
      (C₁.leftMultiplicityProjective χ).traceFunction
        (C₁.embedding b) := by
  let E := compositionRecoveryLinearEquiv C₁ C₂ hP χ hχ
  have hconj :
      E.conj (((compositionMiddleProjective C₁ χ).operator b :
        C₁.leftMultiplicitySpace χ →ₗ[ℂ]
          C₁.leftMultiplicitySpace χ)) =
        (C₂.leftMultiplicityProjective
          (compositionMiddleCharacter C₁ χ hχ)).operator b := by
    apply LinearMap.ext
    intro z
    change
      E (((compositionMiddleProjective C₁ χ).operator b) (E.symm z)) =
        (C₂.leftMultiplicityProjective
          (compositionMiddleCharacter C₁ χ hχ)).operator b z
    calc
      E (((compositionMiddleProjective C₁ χ).operator b) (E.symm z)) =
          (C₂.leftMultiplicityProjective
            (compositionMiddleCharacter C₁ χ hχ)).operator b
              (E (E.symm z)) :=
        compositionRecoveryLinearEquiv_intertwines
          C₁ C₂ hP χ hχ b (E.symm z)
      _ = (C₂.leftMultiplicityProjective
          (compositionMiddleCharacter C₁ χ hχ)).operator b z := by simp
  change LinearMap.trace ℂ _ _ = LinearMap.trace ℂ _ _
  rw [← hconj]
  exact LinearMap.trace_conj' _ E

/-- Pointwise functoriality of the transported irreducible character for
composable witnesses with a literally shared middle projective lift. -/
theorem rightMultiplicityCharacter_compose_of_projective_eq
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U S W Y)
    (hP : C₁.rightProjective = C₂.leftProjective)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (C₁.compose_of_projective_eq C₂ hP).rightMultiplicityCharacter χ hχ =
      C₂.rightMultiplicityCharacter
        (C₁.rightMultiplicityCharacter χ hχ)
        (C₁.rightMultiplicityCharacter_liesOver χ hχ) := by
  apply IrreducibleCharacter.ext
  funext d
  rw [(C₁.compose_of_projective_eq C₂ hP).rightMultiplicityCharacter_values,
    C₂.rightMultiplicityCharacter_values]
  change
    ((C₁.compose_of_projective_eq C₂ hP).rightTensorRepresentation
      ((C₁.compose_of_projective_eq C₂ hP).leftMultiplicityProjective χ)
      ((C₁.compose_of_projective_eq C₂ hP).leftMultiplicity_hasInverseFactorSet
        χ)).character d =
      (C₂.rightTensorRepresentation
        (C₂.leftMultiplicityProjective
          (compositionMiddleCharacter C₁ χ hχ))
        (C₂.leftMultiplicity_hasInverseFactorSet
          (compositionMiddleCharacter C₁ χ hχ))).character d
  rw [(C₁.compose_of_projective_eq C₂ hP).rightTensorRepresentation_character,
    C₂.rightTensorRepresentation_character]
  change
    C₂.rightProjective.traceFunction d *
        (C₁.leftMultiplicityProjective χ).traceFunction
          (C₁.embedding (C₂.embedding d)) =
      C₂.rightProjective.traceFunction d *
        (C₂.leftMultiplicityProjective
          (compositionMiddleCharacter C₁ χ hχ)).traceFunction
            (C₂.embedding d)
  rw [compositionalMultiplicity_trace_eq
    C₁ C₂ hP χ hχ (C₂.embedding d)]

/-- Application form of all-character functoriality. -/
@[simp]
theorem centralCharacterEquiv_compose_of_projective_eq_apply
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U S W Y)
    (hP : C₁.rightProjective = C₂.leftProjective)
    (χ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      T.normalSubgroup.subtype T.character) :
    (C₁.compose_of_projective_eq C₂ hP).centralCharacterEquiv χ =
      C₂.centralCharacterEquiv (C₁.centralCharacterEquiv χ) := by
  apply Subtype.ext
  exact
    rightMultiplicityCharacter_compose_of_projective_eq
      C₁ C₂ hP χ.1 χ.2

/-- Extensional composition law for the all-character equivalences. -/
theorem centralCharacterEquiv_compose_of_projective_eq
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U S W Y)
    (hP : C₁.rightProjective = C₂.leftProjective) :
    (C₁.compose_of_projective_eq C₂ hP).centralCharacterEquiv =
      C₁.centralCharacterEquiv.trans C₂.centralCharacterEquiv := by
  ext χ
  exact
    centralCharacterEquiv_compose_of_projective_eq_apply
      C₁ C₂ hP χ

/-- Application form of prime-to-`p` functoriality. -/
@[simp]
theorem centralPPrimeCharacterEquiv_compose_of_projective_eq_apply
    {p : ℕ} (hp : p.Prime)
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U S W Y)
    (hP : C₁.rightProjective = C₂.leftProjective)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p)
    (hS : S.character.IsPPrimeDegree p)
    (χ :
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character) :
    (C₁.compose_of_projective_eq C₂ hP).centralPPrimeCharacterEquiv
        hp hT hS χ =
      C₂.centralPPrimeCharacterEquiv hp hU hS
        (C₁.centralPPrimeCharacterEquiv hp hT hU χ) := by
  apply Subtype.ext
  exact
    centralCharacterEquiv_compose_of_projective_eq_apply
      C₁ C₂ hP χ.1

/-- Extensional composition law for prime-to-`p` equivalences. -/
theorem centralPPrimeCharacterEquiv_compose_of_projective_eq
    {p : ℕ} (hp : p.Prime)
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U S W Y)
    (hP : C₁.rightProjective = C₂.leftProjective)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p)
    (hS : S.character.IsPPrimeDegree p) :
    (C₁.compose_of_projective_eq C₂ hP).centralPPrimeCharacterEquiv
        hp hT hS =
      (C₁.centralPPrimeCharacterEquiv hp hT hU).trans
        (C₂.centralPPrimeCharacterEquiv hp hU hS) := by
  ext χ
  exact
    centralPPrimeCharacterEquiv_compose_of_projective_eq_apply
      hp C₁ C₂ hP hT hU hS χ

end Composition

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
