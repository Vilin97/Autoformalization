/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.NormalizedCharacterCertificate

/-!
# Separating certified character rows

Explicit character tables usually distinguish rows first by degree and then
by one or two character values.  This file records those elementary
consequences for `CharacterRowCertificate`, so generated finite-table proofs
need not unfold the packaging of irreducible characters.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterRowCertificate

variable {G : Type} [Group G] [Finite G]

/-- Two certified rows built from the same representation afford the same
irreducible character.  This lets a table-wide normalized certificate reuse
separation theorems proved for an earlier certificate package. -/
theorem irreducibleCharacter_eq_of_representation_eq
    (C D : CharacterRowCertificate G)
    (h : C.representation = D.representation) :
    C.irreducibleCharacter = D.irreducibleCharacter := by
  apply IrreducibleCharacter.ext
  rw [C.irreducibleCharacter_values,
    D.irreducibleCharacter_values, h]

/-- Equal certified irreducible characters have equal representation
dimensions. -/
theorem finrank_eq_of_irreducibleCharacter_eq
    (C D : CharacterRowCertificate G)
    (h : C.irreducibleCharacter = D.irreducibleCharacter) :
    Module.finrank ℂ C.representation =
      Module.finrank ℂ D.representation := by
  have hdegree :=
    congrArg (fun χ : IrreducibleCharacter G ↦ χ.degree) h
  simpa only [C.irreducibleCharacter_degree,
    D.irreducibleCharacter_degree] using hdegree

/-- Different dimensions separate two certified irreducible characters. -/
theorem irreducibleCharacter_ne_of_finrank_ne
    (C D : CharacterRowCertificate G)
    (h :
      Module.finrank ℂ C.representation ≠
        Module.finrank ℂ D.representation) :
    C.irreducibleCharacter ≠ D.irreducibleCharacter :=
  fun hcharacter ↦
    h (C.finrank_eq_of_irreducibleCharacter_eq D hcharacter)

/-- Equal certified irreducible characters agree at every group element. -/
theorem character_apply_eq_of_irreducibleCharacter_eq
    (C D : CharacterRowCertificate G)
    (g : G)
    (h : C.irreducibleCharacter = D.irreducibleCharacter) :
    C.representation.character g =
      D.representation.character g := by
  have hvalue :=
    congrArg
      (fun χ : IrreducibleCharacter G ↦ χ.values g) h
  simpa only [C.irreducibleCharacter_values_apply,
    D.irreducibleCharacter_values_apply] using hvalue

/-- A single different character value separates two certified irreducible
characters. -/
theorem irreducibleCharacter_ne_of_character_apply_ne
    (C D : CharacterRowCertificate G)
    (g : G)
    (h :
      C.representation.character g ≠
        D.representation.character g) :
    C.irreducibleCharacter ≠ D.irreducibleCharacter :=
  fun hcharacter ↦
    h (C.character_apply_eq_of_irreducibleCharacter_eq
      D g hcharacter)

end CharacterRowCertificate
end McKayConjecture
