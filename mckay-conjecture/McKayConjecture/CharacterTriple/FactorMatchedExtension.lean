/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ExtensionFromDegree
import McKayConjecture.CharacterTriple.CentralCharacterBijection

/-!
# Exact extensions under factor-matched character-triple comparison

A factor-matched character-triple witness transports the same projective
multiplicity space on both sides.  If a character on either side is an exact
extension of the distinguished normal character, that multiplicity space has
dimension one.  The transported character is therefore an exact extension on
the other side.

No centralizer-containment or scalar-agreement hypothesis is used here.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FactorMatchedIsomorphismWitness

variable {G H V W : Type}
variable [Group G] [Finite G] [Group H] [Finite H]
variable {S : CharacterTriple G} {T : CharacterTriple H}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]

/-- An exact extension has one-dimensional source multiplicity space.
This only uses factor-matched data. -/
theorem leftMultiplicitySpace_finrank_eq_one_of_isExtension
    (C : FactorMatchedIsomorphismWitness S T V W)
    (chi : IrreducibleCharacter G)
    (hchi :
      IrreducibleCharacter.IsExtensionAlong
        S.normalSubgroup.subtype S.character chi) :
    Module.finrank ℂ (C.leftMultiplicitySpace chi) = 1 := by
  let hover := hchi.liesOver
  have hdim :=
    C.leftMultiplicityTensor_finrank chi hover
  have hdim' :
      S.character.degree *
          Module.finrank ℂ (C.leftMultiplicitySpace chi) =
        S.character.degree * 1 := by
    simpa only [Module.finrank_tensorProduct,
      C.leftAssociated.finrank_eq_character_degree,
      hchi.degree_eq, mul_one] using hdim
  exact
    Nat.eq_of_mul_eq_mul_left
      S.character.degree_pos hdim'

/-- The symmetric one-dimensionality statement on the target side. -/
theorem rightMultiplicitySpace_finrank_eq_one_of_isExtension
    (C : FactorMatchedIsomorphismWitness S T V W)
    (psi : IrreducibleCharacter H)
    (hpsi :
      IrreducibleCharacter.IsExtensionAlong
        T.normalSubgroup.subtype T.character psi) :
    Module.finrank ℂ (C.rightMultiplicitySpace psi) = 1 := by
  let hover := hpsi.liesOver
  have hdim :=
    C.rightMultiplicityTensor_finrank psi hover
  have hdim' :
      T.character.degree *
          Module.finrank ℂ (C.rightMultiplicitySpace psi) =
        T.character.degree * 1 := by
    simpa only [Module.finrank_tensorProduct,
      C.rightAssociated.finrank_eq_character_degree,
      hpsi.degree_eq, mul_one] using hdim
  exact
    Nat.eq_of_mul_eq_mul_left
      T.character.degree_pos hdim'

/-- A factor-matched character-triple comparison transports existence of
exact extensions in both directions. -/
theorem exists_extension_iff
    (C : FactorMatchedIsomorphismWitness S T V W) :
    (∃ chi : IrreducibleCharacter G,
        IrreducibleCharacter.IsExtensionAlong
          S.normalSubgroup.subtype S.character chi) ↔
      ∃ psi : IrreducibleCharacter H,
        IrreducibleCharacter.IsExtensionAlong
          T.normalSubgroup.subtype T.character psi := by
  constructor
  · rintro ⟨chi, hchi⟩
    let hover := hchi.liesOver
    let psi := C.rightMultiplicityCharacter chi hover
    have hdegree : psi.degree = T.character.degree := by
      rw [C.rightMultiplicityCharacter_degree_eq chi hover,
        C.leftMultiplicitySpace_finrank_eq_one_of_isExtension
          chi hchi,
        mul_one]
    exact
      ⟨psi,
        IrreducibleCharacter.IsExtensionAlong.of_liesOver_of_degree_eq
          (C.rightMultiplicityCharacter_liesOver chi hover)
          hdegree⟩
  · rintro ⟨psi, hpsi⟩
    let hover := hpsi.liesOver
    let chi := C.leftMultiplicityCharacter psi hover
    have hdegree : chi.degree = S.character.degree := by
      rw [C.leftMultiplicityCharacter_degree_eq psi hover,
        C.rightMultiplicitySpace_finrank_eq_one_of_isExtension
          psi hpsi,
        mul_one]
    exact
      ⟨chi,
        IrreducibleCharacter.IsExtensionAlong.of_liesOver_of_degree_eq
          (C.leftMultiplicityCharacter_liesOver psi hover)
          hdegree⟩

end FactorMatchedIsomorphismWitness
end CharacterTriple
end McKayConjecture
