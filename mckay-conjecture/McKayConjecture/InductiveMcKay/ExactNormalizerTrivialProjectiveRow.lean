/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GallagherCorrespondence
import McKayConjecture.Character.DegreeOneLinear
import McKayConjecture.Character.Trivial
import McKayConjecture.CharacterTriple.ProjectiveObstructionExtension
import McKayConjecture.InductiveMcKay.ExactNormalizerProjectiveRowAdapter
import Mathlib.GroupTheory.IsPerfect

/-!
# The trivial exact-normalizer projective row

The trivial characters on the two canonical semidirect products are honest
extensions of a matched pair of trivial normal-subgroup characters.  Their
associated projective representations have factor one, and their projective
traces and dimensions are both one.  This file packages those observations
through the factor-and-trace exact-normalizer row adapter.

The resulting row constructor deliberately asks only that the two matched
ordinary characters are intrinsically trivial.  It is therefore independent
of any display order or external character-table naming convention.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple

namespace IrreducibleCharacter

variable {A B : Type}
variable [Group A] [Group B]

/-- The trivial character of a target group extends the trivial character of
the source along every homomorphism. -/
theorem trivial_isExtensionAlong (f : B →* A) :
    IsExtensionAlong f (trivial B) (trivial A) := by
  intro b
  rfl

/-- A perfect group has no nontrivial degree-one irreducible character. -/
theorem eq_trivial_of_degree_one
    [Group.IsPerfect A]
    (χ : IrreducibleCharacter A)
    (hχ : χ.degree = 1) :
    χ = trivial A := by
  let linearParameter :=
    linearParameterOfDegreeOne χ hχ
  have linearParameter_eq_one :
      linearParameter = 1 := by
    apply MonoidHom.ext
    intro a
    apply MonoidHom.mem_ker.mp
    exact
      Abelianization.commutator_subset_ker linearParameter
        Group.IsPerfect.mem_commutator
  rw [← linear_linearParameterOfDegreeOne χ hχ]
  exact
    (linear_eq_trivial_iff linearParameter).mpr
      linearParameter_eq_one

/-- The factor-one projective representations afforded by two trivial honest
extensions have literally matching factors along every homomorphism. -/
theorem trivialExtension_factorAgreement
    (f : B →* A) (b c : B) :
    (extensionProjectiveRepresentation
        (ψ := trivial A)).factor (f b) (f c) =
      (extensionProjectiveRepresentation
        (ψ := trivial B)).factor b c := by
  rfl

/-- The projective traces of two trivial honest extensions satisfy the
cross-multiplied trace identity along every homomorphism. -/
theorem trivialExtension_traceCross
    (f : B →* A) (b : B) :
    LinearMap.trace ℂ (trivial A).realization
          ((extensionProjectiveRepresentation
            (ψ := trivial A)).operator (f b) :
            (trivial A).realization →ₗ[ℂ]
              (trivial A).realization) *
        (Module.finrank ℂ (trivial B).realization : ℂ) =
      LinearMap.trace ℂ (trivial B).realization
          ((extensionProjectiveRepresentation
            (ψ := trivial B)).operator b :
            (trivial B).realization →ₗ[ℂ]
              (trivial B).realization) *
        (Module.finrank ℂ (trivial A).realization : ℂ) := by
  change
    (trivial A).realization.character (f b) *
        (Module.finrank ℂ (trivial B).realization : ℂ) =
      (trivial B).realization.character b *
        (Module.finrank ℂ (trivial A).realization : ℂ)
  rw [(trivial A).realization_character,
    (trivial B).realization_character,
    (trivial A).realization_finrank,
    (trivial B).realization_finrank]
  rfl

end IrreducibleCharacter

namespace InductiveMcKay

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} {P : Sylow p G}

namespace ExactNormalizerProjectiveRowData

/-- A matched pair of intrinsically trivial characters supplies its complete
exact-normalizer projective row.

The proof uses the honest trivial characters on the two canonical semidirect
products.  Their association certificates are obtained by restriction, while
factor agreement and the centralizer trace identity are the generic trivial
extension lemmas above. -/
def ofTrivialCharacters
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p)
    (ambientCharacter_eq_trivial :
      χ.1 = IrreducibleCharacter.trivial G)
    (localCharacter_eq_trivial :
      (e.toExactNormalizerLocalCorrespondence.localCharacter χ).1 =
        IrreducibleCharacter.trivial
          e.toExactNormalizerLocalCorrespondence.intermediate) :
    ExactNormalizerProjectiveRowData e χ := by
  let d := e.toExactNormalizerLocalCorrespondence
  let leftExtension :=
    IrreducibleCharacter.trivial
      (G ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer P χ)
  let rightExtension :=
    IrreducibleCharacter.trivial
      (d.intermediate ⋊[d.stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer P χ)
  have leftExtends :
      IrreducibleCharacter.IsExtensionAlong
        (EquivariantLocalCorrespondence.ambientTriple
          (P := P) χ).normalSubgroup.subtype
        (EquivariantLocalCorrespondence.ambientTriple
          (P := P) χ).character
        leftExtension := by
    intro x
    change (1 : ℂ) = χ.1.values x.1.left
    rw [ambientCharacter_eq_trivial]
    rfl
  have rightExtends :
      IrreducibleCharacter.IsExtensionAlong
        (d.intermediateTriple χ).normalSubgroup.subtype
        (d.intermediateTriple χ).character
        rightExtension := by
    intro x
    change
      (1 : ℂ) =
        (d.localCharacter χ).1.values x.1.left
    rw [localCharacter_eq_trivial]
    rfl
  let leftProjective :=
    IrreducibleCharacter.extensionProjectiveRepresentation
      (ψ := leftExtension)
  let rightProjective :=
    IrreducibleCharacter.extensionProjectiveRepresentation
      (ψ := rightExtension)
  letI : Nontrivial leftExtension.realization :=
    CliffordRestriction.nontrivial_of_simple leftExtension.realization
  letI : Nontrivial rightExtension.realization :=
    CliffordRestriction.nontrivial_of_simple rightExtension.realization
  have leftAssociated :
      AssociatedProjectiveRepresentation
        (EquivariantLocalCorrespondence.ambientTriple
          (P := P) χ)
        leftExtension.realization leftProjective := by
    rw [← IrreducibleCharacter.extensionCharacterTriple_eq
      leftExtension leftExtends]
    exact
      IrreducibleCharacter.extensionAssociatedProjectiveRepresentation
        leftExtends
  have rightAssociated :
      AssociatedProjectiveRepresentation
        (d.intermediateTriple χ)
        rightExtension.realization rightProjective := by
    rw [← IrreducibleCharacter.extensionCharacterTriple_eq
      rightExtension rightExtends]
    exact
      IrreducibleCharacter.extensionAssociatedProjectiveRepresentation
        rightExtends
  exact
    ofAssociatedFactorAgreementTraceCross e χ
      leftProjective leftAssociated rightProjective rightAssociated
      (by
        intro h k
        exact
          IrreducibleCharacter.trivialExtension_factorAgreement
            (d.semidirectEmbedding χ) h k)
      (by
        intro h _
        exact
          IrreducibleCharacter.trivialExtension_traceCross
            (d.semidirectEmbedding χ) h)

end ExactNormalizerProjectiveRowData

end InductiveMcKay
end McKayConjecture
