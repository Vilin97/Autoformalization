/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralIsomorphism
import McKayConjecture.CharacterTriple.ProjectiveRestriction
import McKayConjecture.CharacterTriple.ProjectiveTensor

/-!
# The tensor construction attached to a central character-triple isomorphism

A central-isomorphism witness identifies the factor set of its two associated
projective representations on the embedded right ambient group.  Therefore
any projective representation on the left with the inverse factor set can be
restricted across the embedding and tensored with the right associated lift.
Both tensor products are honest linear representations.

This file implements that construction and its exact character and degree
formulas.  It does not assert irreducibility or surjectivity: those are the
substantive multiplicity-space and Clifford-theory steps in the character
triple correspondence.
-/

noncomputable section

open scoped TensorProduct

universe u v

namespace McKayConjecture
namespace CharacterTriple
namespace CentralIsomorphismWitness

variable {A : Type u} {B : Type v} [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W Z : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup Z] [Module ℂ Z] [Module.Finite ℂ Z] [Nontrivial Z]

namespace ProjectiveRepresentation

variable {L : Type*} [Group L]

omit [Finite A] [Module.Finite ℂ V] [Nontrivial V]
  [Module.Finite ℂ Z] [Nontrivial Z] in
/-- Inverse-factor compatibility is preserved by pullback along a group
homomorphism. -/
theorem HasInverseFactorSet.comap
    {P : ProjectiveRepresentation ℂ A V}
    {Q : ProjectiveRepresentation ℂ A Z}
    (hPQ : P.HasInverseFactorSet Q) (f : L →* A) :
    (P.comap f).HasInverseFactorSet (Q.comap f) := by
  intro g h
  exact hPQ (f g) (f h)

omit [Finite A] [Module.Finite ℂ V] [Nontrivial V] in
/-- Pulling back a projective representation precomposes its trace
function. -/
theorem traceFunction_comap
    (P : ProjectiveRepresentation ℂ A V) (f : L →* A) :
    (P.comap f).traceFunction = P.traceFunction ∘ f := by
  rfl

end ProjectiveRepresentation

end CentralIsomorphismWitness

namespace FactorMatchedIsomorphismWitness

local notation "CentralIsomorphismWitness" =>
  FactorMatchedIsomorphismWitness

variable {A : Type u} {B : Type v} [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W Z : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup Z] [Module ℂ Z] [Module.Finite ℂ Z] [Nontrivial Z]

omit [Module.Finite ℂ Z] [Nontrivial Z] in
/-- Factor-set agreement in a central-isomorphism witness transfers an
inverse-factor projective representation from the left triple to the right
triple. -/
theorem right_hasInverseFactorSet
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) :
    C.rightProjective.HasInverseFactorSet (Q.comap C.embedding) := by
  intro b c
  change Q.factor (C.embedding b) (C.embedding c) =
    (C.rightProjective.factor b c)⁻¹
  rw [hQ, C.factor_agreement]

/-- The honest left ambient action obtained by cancelling the associated
factor set against `Q`. -/
def leftTensorAction
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) :
    A →* ((V ⊗[ℂ] Z) ≃ₗ[ℂ] (V ⊗[ℂ] Z)) :=
  C.leftProjective.cancelTensorLinearAction Q hQ

/-- The honest right ambient action obtained by restricting `Q` across the
central-isomorphism embedding and cancelling the common factor set. -/
def rightTensorAction
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) :
    B →* ((W ⊗[ℂ] Z) ≃ₗ[ℂ] (W ⊗[ℂ] Z)) :=
  C.rightProjective.cancelTensorLinearAction
    (Q.comap C.embedding) (C.right_hasInverseFactorSet Q hQ)

omit [Module.Finite ℂ Z] [Nontrivial Z] in
@[simp]
theorem leftTensorAction_apply
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) (a : A) :
    C.leftTensorAction Q hQ a =
      TensorProduct.congr (C.leftProjective.operator a) (Q.operator a) :=
  rfl

omit [Module.Finite ℂ Z] [Nontrivial Z] in
@[simp]
theorem rightTensorAction_apply
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) (b : B) :
    C.rightTensorAction Q hQ b =
      TensorProduct.congr (C.rightProjective.operator b)
        (Q.operator (C.embedding b)) :=
  rfl

/-- The bundled ordinary representation on the left ambient group. -/
def leftTensorRepresentation
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) :
    Representation ℂ A (V ⊗[ℂ] Z) :=
  linearRepresentationOfAction (C.leftTensorAction Q hQ)

/-- The bundled ordinary representation on the right ambient group. -/
def rightTensorRepresentation
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) :
    Representation ℂ B (W ⊗[ℂ] Z) :=
  linearRepresentationOfAction (C.rightTensorAction Q hQ)

omit [Nontrivial Z] in
/-- Exact projective-trace formula for the left tensor construction. -/
theorem leftTensorRepresentation_character
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) :
    (C.leftTensorRepresentation Q hQ).character =
      C.leftProjective.traceFunction * Q.traceFunction :=
  C.leftProjective.cancelTensorLinearAction_character Q hQ

omit [Nontrivial Z] in
/-- Exact projective-trace formula for the right tensor construction. -/
theorem rightTensorRepresentation_character
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) :
    (C.rightTensorRepresentation Q hQ).character =
      C.rightProjective.traceFunction *
        (Q.traceFunction ∘ C.embedding) := by
  funext b
  exact LinearMap.trace_tensorProduct'
    (C.rightProjective.operator b : W →ₗ[ℂ] W)
    (Q.operator (C.embedding b) : Z →ₗ[ℂ] Z)

omit [Nontrivial Z] in
/-- The two tensor constructions have the same multiplicity-space factor in
their degrees.  This is the cross-multiplied degree-ratio identity used in
central character-triple correspondences. -/
theorem tensorDegrees_cross
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) :
    Module.finrank ℂ W *
        (C.leftTensorRepresentation Q hQ).character 1 =
      Module.finrank ℂ V *
        (C.rightTensorRepresentation Q hQ).character 1 := by
  rw [Representation.char_one, Representation.char_one]
  rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct]
  norm_cast
  ac_rfl

end FactorMatchedIsomorphismWitness

namespace CentralIsomorphismWitness

variable {A : Type u} {B : Type v} [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W Z : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup Z] [Module ℂ Z] [Module.Finite ℂ Z] [Nontrivial Z]

export FactorMatchedIsomorphismWitness
  (leftTensorAction rightTensorAction
    leftTensorAction_apply rightTensorAction_apply tensorDegrees_cross)

omit [Module.Finite ℂ Z] [Nontrivial Z] in
theorem right_hasInverseFactorSet
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) :
    C.rightProjective.HasInverseFactorSet (Q.comap C.embedding) :=
  C.toFactorMatchedIsomorphismWitness.right_hasInverseFactorSet Q hQ

/-- Compatibility wrapper for the stronger central witness. -/
def leftTensorRepresentation
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) :
    Representation ℂ A (V ⊗[ℂ] Z) :=
  C.toFactorMatchedIsomorphismWitness.leftTensorRepresentation Q hQ

/-- Compatibility wrapper for the stronger central witness. -/
def rightTensorRepresentation
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) :
    Representation ℂ B (W ⊗[ℂ] Z) :=
  C.toFactorMatchedIsomorphismWitness.rightTensorRepresentation Q hQ

omit [Nontrivial Z] in
/-- Compatibility wrapper for the stronger central witness. -/
theorem leftTensorRepresentation_character
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) :
    (C.leftTensorRepresentation Q hQ).character =
      C.leftProjective.traceFunction * Q.traceFunction :=
  C.toFactorMatchedIsomorphismWitness
    |>.leftTensorRepresentation_character Q hQ

omit [Nontrivial Z] in
/-- Compatibility wrapper for the stronger central witness. -/
theorem rightTensorRepresentation_character
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q) :
    (C.rightTensorRepresentation Q hQ).character =
      C.rightProjective.traceFunction *
        (Q.traceFunction ∘ C.embedding) :=
  C.toFactorMatchedIsomorphismWitness
    |>.rightTensorRepresentation_character Q hQ

end CentralIsomorphismWitness

namespace AssociatedProjectiveRepresentation

variable {A : Type u} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- On the normal subgroup, the projective trace function of an associated
lift is the prescribed irreducible character. -/
theorem traceFunction_normal
    (R : AssociatedProjectiveRepresentation T V P)
    (x : T.normalSubgroup) :
    P.traceFunction (x : A) = T.character.values x := by
  have hx := congrFun R.restriction_character x
  change LinearMap.trace ℂ V (R.restriction x) =
    T.character.values x at hx
  rw [R.restriction_apply] at hx
  exact hx

/-- The associated representation space has dimension equal to the degree of
the normal-subgroup character it affords. -/
theorem finrank_eq_character_degree
    (R : AssociatedProjectiveRepresentation T V P) :
    Module.finrank ℂ V = T.character.degree := by
  apply Nat.cast_injective (R := ℂ)
  have h := congrFun R.restriction_character (1 : T.normalSubgroup)
  simpa only [FDRep.char_one, IrreducibleCharacter.value_one] using h

end AssociatedProjectiveRepresentation

namespace ProjectiveRepresentation

variable {A : Type u} [Finite A] [Group A]
variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

/-- A projective multiplicity representation is trivial on the normal
subgroup when every normal-subgroup element has identity lift. -/
def IsTrivialOnNormal
    (T : CharacterTriple A)
    (Q : ProjectiveRepresentation ℂ A Z) : Prop :=
  ∀ x : T.normalSubgroup, Q.operator (x : A) = 1

end ProjectiveRepresentation

namespace FactorMatchedIsomorphismWitness

local notation "CentralIsomorphismWitness" =>
  FactorMatchedIsomorphismWitness

variable {A : Type u} {B : Type v} [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W Z : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup Z] [Module ℂ Z] [Module.Finite ℂ Z] [Nontrivial Z]

omit [Module.Finite ℂ Z] [Nontrivial Z] in
/-- Triviality of the multiplicity lift on the left normal subgroup
transports to the embedded right normal subgroup. -/
theorem right_isTrivialOnNormal
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (htriv : Q.IsTrivialOnNormal T) :
    (Q.comap C.embedding).IsTrivialOnNormal U := by
  intro m
  let x : T.normalSubgroup :=
    ⟨C.embedding (m : B), C.map_rightNormal_le_leftNormal
      ⟨m, m.property, rfl⟩⟩
  exact htriv x

omit [Nontrivial Z] in
/-- On the left normal subgroup, the cancelled tensor character is the
prescribed character multiplied by the multiplicity-space dimension. -/
theorem leftTensorRepresentation_character_on_normal
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T)
    (x : T.normalSubgroup) :
    (C.leftTensorRepresentation Q hQ).character (x : A) =
      T.character.values x * Module.finrank ℂ Z := by
  rw [C.leftTensorRepresentation_character]
  change C.leftProjective.traceFunction (x : A) *
      Q.traceFunction (x : A) =
    T.character.values x * Module.finrank ℂ Z
  rw [C.leftAssociated.traceFunction_normal x]
  change T.character.values x *
      LinearMap.trace ℂ Z (Q.operator (x : A)) =
    T.character.values x * Module.finrank ℂ Z
  rw [htriv x]
  exact congrArg (T.character.values x * ·)
    (LinearMap.trace_one ℂ Z)

omit [Nontrivial Z] in
/-- On the right normal subgroup, the transported tensor character is the
right prescribed character with the same multiplicity. -/
theorem rightTensorRepresentation_character_on_normal
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T)
    (m : U.normalSubgroup) :
    (C.rightTensorRepresentation Q hQ).character (m : B) =
      U.character.values m * Module.finrank ℂ Z := by
  rw [C.rightTensorRepresentation_character]
  change C.rightProjective.traceFunction (m : B) *
      Q.traceFunction (C.embedding (m : B)) =
    U.character.values m * Module.finrank ℂ Z
  rw [C.rightAssociated.traceFunction_normal m]
  change U.character.values m *
      LinearMap.trace ℂ Z (Q.operator (C.embedding (m : B))) =
    U.character.values m * Module.finrank ℂ Z
  have hm :
      Q.operator (C.embedding (m : B)) = 1 :=
    C.right_isTrivialOnNormal Q htriv m
  rw [hm]
  exact congrArg (U.character.values m * ·)
    (LinearMap.trace_one ℂ Z)

omit [Module.Finite ℂ Z] [Nontrivial Z] in
/-- If the two normal-subgroup characters have `p'`-degree, the left and
right tensor constructions have `p'`-dimension simultaneously.  Thus the
central-triple tensor transport preserves the degree condition relevant to
McKay correspondences. -/
theorem tensorDimension_isPPrime_iff
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    (¬p ∣ Module.finrank ℂ (V ⊗[ℂ] Z)) ↔
      ¬p ∣ Module.finrank ℂ (W ⊗[ℂ] Z) := by
  have hV : ¬p ∣ Module.finrank ℂ V := by
    rw [C.leftAssociated.finrank_eq_character_degree]
    exact hT
  have hW : ¬p ∣ Module.finrank ℂ W := by
    rw [C.rightAssociated.finrank_eq_character_degree]
    exact hU
  simp only [Module.finrank_tensorProduct, hp.dvd_mul, not_or, hV, hW]

end FactorMatchedIsomorphismWitness

namespace CentralIsomorphismWitness

variable {A : Type u} {B : Type v} [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W Z : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup Z] [Module ℂ Z] [Module.Finite ℂ Z] [Nontrivial Z]

export FactorMatchedIsomorphismWitness
  (leftTensorRepresentation_character_on_normal
    rightTensorRepresentation_character_on_normal
    tensorDimension_isPPrime_iff)

omit [Module.Finite ℂ Z] [Nontrivial Z] in
/-- Compatibility wrapper for the stronger central witness. -/
theorem right_isTrivialOnNormal
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (htriv : Q.IsTrivialOnNormal T) :
    (Q.comap C.embedding).IsTrivialOnNormal U :=
  C.toFactorMatchedIsomorphismWitness.right_isTrivialOnNormal Q htriv

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
