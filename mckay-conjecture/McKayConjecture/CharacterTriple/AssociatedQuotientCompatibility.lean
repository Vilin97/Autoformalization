/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralKernelTriviality
import McKayConjecture.CharacterTriple.ProjectiveQuotientDescent

/-!
# Exact quotient compatibility of associated projective representations

An associated projective representation already has factor one whenever
either input lies in the normal subgroup of its character triple.  If the
normal character is trivial on a smaller subgroup `Z`, its chosen associated
operators are identity on `Z` as well.  Hence the exact chosen operators,
not merely their projective-linear classes, satisfy the hypotheses of
`ProjectiveRepresentation.quotientDescent`.

This shows that representation-level kernel triviality is the narrow
condition needed for projective descent; no independent factor-set or
operator hypothesis has to be assumed.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

variable {A : Type u} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- Character triviality on a subgroup of the triple's normal subgroup
forces exact quotient compatibility on its image in the ambient group. -/
theorem isQuotientCompatible_of_trivialOn
    (R : AssociatedProjectiveRepresentation T V P)
    (Z : Subgroup T.normalSubgroup)
    (htrivial : T.character.TrivialOn Z) :
    P.IsQuotientCompatible
      (Z.map T.normalSubgroup.subtype) := by
  have hrestriction :
      FDRep.IsTrivialOn R.fdRestriction Z :=
    (IrreducibleCharacter.trivialOn_iff_of_character_eq
      Z T.character R.fdRestriction
        R.fdRestriction_character).mp htrivial
  refine
    { factor_normal_left := ?_
      factor_normal_right := ?_
      operator_normal := ?_ }
  · intro z a
    obtain ⟨x, hxZ, hx⟩ := z.property
    simpa [← hx] using R.factor_normal_left x a
  · intro a z
    obtain ⟨x, hxZ, hx⟩ := z.property
    simpa [← hx] using R.factor_normal_right a x
  · intro z
    obtain ⟨x, hxZ, hx⟩ := z.property
    apply LinearEquiv.ext
    intro v
    change P.operator (z : A) v = v
    rw [← hx]
    change P.operator (x : A) v = v
    have hoperator :
        P.operator (x : A) = R.restriction x :=
      (R.restriction_apply x).symm
    rw [hoperator]
    have hv :=
      LinearMap.congr_fun (hrestriction ⟨x, hxZ⟩) v
    exact hv

end AssociatedProjectiveRepresentation

namespace CentralIsomorphismWitness

variable {A : Type u} {B : Type} [Finite A] [Finite B]
variable [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]

/-- Exact quotient compatibility of the left associated projective
representation, derived solely from triviality of the left normal
character. -/
theorem leftIsQuotientCompatible_of_trivialOn
    (C : CentralIsomorphismWitness T U V W)
    (Z : Subgroup T.normalSubgroup)
    (htrivial : T.character.TrivialOn Z) :
    C.leftProjective.IsQuotientCompatible
      (Z.map T.normalSubgroup.subtype) :=
  C.leftAssociated.isQuotientCompatible_of_trivialOn Z htrivial

/-- Exact quotient compatibility of the right associated projective
representation, derived solely from triviality of the right normal
character. -/
theorem rightIsQuotientCompatible_of_trivialOn
    (C : CentralIsomorphismWitness T U V W)
    (Z : Subgroup U.normalSubgroup)
    (htrivial : U.character.TrivialOn Z) :
    C.rightProjective.IsQuotientCompatible
      (Z.map U.normalSubgroup.subtype) :=
  C.rightAssociated.isQuotientCompatible_of_trivialOn Z htrivial

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
