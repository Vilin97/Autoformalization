/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.SubgroupRestriction
import McKayConjecture.InductiveMcKay.CentralExtensionAutomorphismLift

/-!
# Restricting an upstairs triple witness to lifted automorphisms

Let `A → Q` be a central extension and fix a coherent lift of the
automorphisms of `Q` stabilizing a Sylow subgroup.  For a character `χ` of
`Q`, the stabilizer of its inflation in `A` can be larger than the lifted
copy of the stabilizer of `χ`.  Before quotienting a character-triple
witness, one must therefore restrict both of its semidirect ambient groups
to that lifted copy.

The two pullback subgroups below are defined by requiring the right
semidirect coordinate to lie in the range of the stabilizer lift.  They
contain the full normal coordinates, and the canonical intermediate
embedding restricts to an injective homomorphism between them.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace InductiveMcKay
namespace SylowAutomorphismLift

open GroupTheory
open CharacterTriple

variable {A : Type u} {Q : Type v}
variable [Group A] [Group Q] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable {E : CentralExtension A Q} {S : Sylow p Q}
variable
  (L : SylowAutomorphismLift E S)
  (d : LocalInductiveMcKayData (E.sylowLift S))
  (χ : PPrimeIrreducibleCharacter Q p)

/-- The inflated upstairs character paired with a downstairs character. -/
abbrev inflatedCharacter
    (E : CentralExtension A Q)
    (χ : PPrimeIrreducibleCharacter Q p) :
    PPrimeIrreducibleCharacter A p :=
  (E.pPrimeInflationEquiv p χ).1

/-- The range of the chosen lift of the downstairs character stabilizer in
the full upstairs character stabilizer. -/
abbrev characterStabilizerLiftRange :
    Subgroup
      (PPrimeCharacterStabilizer
        (E.sylowLift S) (inflatedCharacter E χ)) :=
  MonoidHom.range (L.characterStabilizerLift χ)

/-- The subgroup of the upstairs ambient semidirect product whose
automorphism coordinate comes from downstairs. -/
abbrev ambientLiftPullback :
    Subgroup
      (A ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer
          (E.sylowLift S) (inflatedCharacter E χ)) :=
  (characterStabilizerLiftRange L χ).comap
    SemidirectProduct.rightHom

/-- The analogous pullback subgroup in the upstairs intermediate
semidirect product. -/
abbrev intermediateLiftPullback :
    Subgroup
      (d.toEquivariant.intermediate ⋊[
        d.toEquivariant.stabilizerIntermediateAction
          (inflatedCharacter E χ)]
      PPrimeCharacterStabilizer
          (E.sylowLift S) (inflatedCharacter E χ)) :=
  (characterStabilizerLiftRange L χ).comap
    SemidirectProduct.rightHom

/-- The whole normal coordinate of the upstairs ambient triple lies in the
lifted-stabilizer pullback. -/
theorem ambientNormal_le_liftPullback :
    (EquivariantLocalCorrespondence.ambientTriple
        (inflatedCharacter E χ)).normalSubgroup ≤
      ambientLiftPullback L χ := by
  rintro x ⟨a, rfl⟩
  change
    (1 : PPrimeCharacterStabilizer
      (E.sylowLift S) (inflatedCharacter E χ)) ∈
        characterStabilizerLiftRange L χ
  exact Subgroup.one_mem _

/-- The whole normal coordinate of the upstairs intermediate triple lies
in the lifted-stabilizer pullback. -/
theorem intermediateNormal_le_liftPullback :
    (d.toEquivariant.intermediateTriple
        (inflatedCharacter E χ)).normalSubgroup ≤
      intermediateLiftPullback L d χ := by
  rintro x ⟨a, rfl⟩
  change
    (1 : PPrimeCharacterStabilizer
      (E.sylowLift S) (inflatedCharacter E χ)) ∈
        characterStabilizerLiftRange L χ
  exact Subgroup.one_mem _

/-- Restriction of the canonical semidirect embedding to the two
lifted-stabilizer pullbacks. -/
def restrictedSemidirectEmbedding :
    intermediateLiftPullback L d χ →*
      ambientLiftPullback L χ :=
  (((d.toEquivariant.semidirectEmbedding
      (inflatedCharacter E χ)).domRestrict
        (intermediateLiftPullback L d χ)).codRestrict
    (ambientLiftPullback L χ)
    (by
      intro x
      exact x.property))

@[simp]
theorem restrictedSemidirectEmbedding_coe
    (x : intermediateLiftPullback L d χ) :
    ((restrictedSemidirectEmbedding L d χ x :
        ambientLiftPullback L χ) :
      A ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer
          (E.sylowLift S) (inflatedCharacter E χ)) =
      d.toEquivariant.semidirectEmbedding
        (inflatedCharacter E χ) x :=
  rfl

/-- The restricted canonical embedding remains injective. -/
theorem restrictedSemidirectEmbedding_injective :
    Function.Injective
      (restrictedSemidirectEmbedding L d χ) := by
  intro x y hxy
  apply Subtype.ext
  apply
    d.toEquivariant.semidirectEmbedding_injective
      (inflatedCharacter E χ)
  exact congrArg Subtype.val hxy

/-- The upstairs ambient character triple restricted to the selected
automorphism lifts. -/
abbrev restrictedAmbientTriple :
    CharacterTriple (ambientLiftPullback L χ) :=
  (EquivariantLocalCorrespondence.ambientTriple
      (inflatedCharacter E χ)).restrictTo
    (ambientLiftPullback L χ)
    (ambientNormal_le_liftPullback L χ)

/-- The upstairs intermediate character triple restricted to the selected
automorphism lifts. -/
abbrev restrictedIntermediateTriple :
    CharacterTriple (intermediateLiftPullback L d χ) :=
  (d.toEquivariant.intermediateTriple
      (inflatedCharacter E χ)).restrictTo
    (intermediateLiftPullback L d χ)
    (intermediateNormal_le_liftPullback L d χ)

end SylowAutomorphismLift
end InductiveMcKay
end McKayConjecture
