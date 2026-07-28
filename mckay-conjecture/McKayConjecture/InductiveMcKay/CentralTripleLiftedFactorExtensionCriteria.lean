/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ExtensionFromDegree
import McKayConjecture.InductiveMcKay.CentralTripleLiftedFactorExtensionTriples

/-!
# Numerical criteria for a lifted target extension

For the target factor extension in a lifted character-triple comparison,
the exact normal-restriction assertion is equivalent to two smaller
claims: the target character has positive restriction multiplicity over
the prescribed normal character, and their degrees are equal.

This does not prove either Dade--Glauberman--Nagao claim.  It gives a
faithful interface for proving them separately.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace LiftedFactorCorrespondence

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}
variable
  (R : AssociatedProjectiveRepresentation T V P)
  (F : R.AssociatedFiniteFactorNormalization)
  (g : CentralRestrictionGroupData T U e)

/-- The exact target-normal extension property is equivalent to lying over
the prescribed target normal character with no degree increase. -/
theorem targetNormalExtension_iff_liesOver_and_degree_eq
    (ψ :
      IrreducibleCharacter
        (TargetFactorCentralExtensionGroup R F g)) :
    IrreducibleCharacter.IsExtensionAlong
        (targetNormalLift R F g) U.character ψ ↔
      CliffordCorrespondence.LiesOverAlong
          (targetNormalLift R F g) U.character ψ ∧
        ψ.degree = U.character.degree := by
  constructor
  · intro h
    exact ⟨h.liesOver, h.degree_eq⟩
  · rintro ⟨hover, hdegree⟩
    exact
      IrreducibleCharacter.IsExtensionAlong.of_liesOver_of_degree_eq
        hover hdegree

/-- A target identified as the image of a complete lifted witness lies
over the prescribed target normal character. -/
theorem IsLiftedExtensionImage.liesOver
    {ψ :
      IrreducibleCharacter
        (TargetFactorCentralExtensionGroup R F g)}
    (hψ : IsLiftedExtensionImage R F g ψ) :
    CliffordCorrespondence.LiesOverAlong
      (targetNormalLift R F g) U.character ψ :=
  (hψ.extendsTargetNormalCharacter R F g).liesOver

/-- A target identified as the image of a complete lifted witness has
exactly the degree of the prescribed target normal character. -/
theorem IsLiftedExtensionImage.degree_eq
    {ψ :
      IrreducibleCharacter
        (TargetFactorCentralExtensionGroup R F g)}
    (hψ : IsLiftedExtensionImage R F g ψ) :
    ψ.degree = U.character.degree :=
  (hψ.extendsTargetNormalCharacter R F g).degree_eq

end LiftedFactorCorrespondence
end InductiveMcKay
end McKayConjecture
