/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RepresentationTheory.FinGroupCharZero
import McKayConjecture.Character.ClassFunctionGroupAlgebra
import McKayConjecture.Character.Construction

/-!
# Kernel-checked certificates for explicit character rows

An explicit character-table computation commonly starts with matrices for a
finite-dimensional complex representation.  This file packages the small
kernel-checked interface needed to turn such matrices into an
`IrreducibleCharacter`.

The substantive certificate is the normalized self-pairing identity.  Mathlib's
character-norm criterion then proves that the representation is simple.  Thus a
generated file may contain matrix entries and finite sums, but no assertion from
the program which generated them is trusted: the representation laws and norm
identity must both elaborate to Lean proofs.

The underlying mathlib simpleness criterion currently places the scalar field,
representation space, and group in the same universe.  Since the scalar field is
`ℂ`, this certificate is intentionally stated for explicit groups and matrix
spaces in `Type`.
-/

noncomputable section

open scoped BigOperators
open CategoryTheory

namespace McKayConjecture

variable {G : Type} [Group G] [Finite G]

/-- The unnormalized self-pairing sum of the character of `V`, using the
canonical finite structure supplied by `[Finite G]`. -/
def characterSelfPairingSum (V : FDRep ℂ G) : ℂ := by
  letI : Fintype G := Fintype.ofFinite G
  exact ∑ g : G, V.character g * V.character g⁻¹

theorem normalizedPairing_ofFDRep_self
    (V : FDRep ℂ G) :
    ClassFunction.normalizedPairing
        (ClassFunction.ofFDRep V)
        (ClassFunction.ofFDRep V) =
      (Nat.card G : ℂ)⁻¹ * characterSelfPairingSum V := by
  letI : Fintype G := Fintype.ofFinite G
  rfl

/-- A finite-dimensional complex representation is simple when its normalized
character self-pairing is one. -/
theorem simple_of_normalizedCharacterPairing_eq_one
    (V : FDRep ℂ G)
    (hnorm :
      ClassFunction.normalizedPairing
          (ClassFunction.ofFDRep V)
          (ClassFunction.ofFDRep V) =
        1) :
    Simple V := by
  letI : Fintype G := Fintype.ofFinite G
  rw [FDRep.simple_iff_char_is_norm_one]
  have hcard : (Nat.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [normalizedPairing_ofFDRep_self] at hnorm
  change
    (Nat.card G : ℂ)⁻¹ *
        characterSelfPairingSum V =
      1 at hnorm
  exact ((inv_mul_eq_one₀ hcard).mp hnorm).symm

/-- A character row certified by an explicit finite-dimensional
representation and a normalized character-norm calculation.

Both fields are ordinary Lean data.  In particular, constructing this structure
does not add a trusted table or a trusted irreducibility oracle. -/
structure CharacterRowCertificate (G : Type) [Group G] [Finite G] where
  /-- The finite-dimensional representation affording the row. -/
  representation : FDRep ℂ G
  /-- The kernel-checked normalized self-pairing calculation. -/
  normalizedSelfPairing :
    ClassFunction.normalizedPairing
        (ClassFunction.ofFDRep representation)
        (ClassFunction.ofFDRep representation) =
      1

namespace CharacterRowCertificate

variable (C : CharacterRowCertificate G)

/-- The certified representation is simple. -/
theorem simple : Simple C.representation :=
  simple_of_normalizedCharacterPairing_eq_one
    C.representation C.normalizedSelfPairing

/-- The irreducible character afforded by a certified row. -/
def irreducibleCharacter : IrreducibleCharacter G := by
  letI : Simple C.representation := C.simple
  exact IrreducibleCharacter.ofSimple C.representation

@[simp]
theorem irreducibleCharacter_values :
    C.irreducibleCharacter.values =
      C.representation.character := by
  letI : Simple C.representation := C.simple
  rfl

@[simp]
theorem irreducibleCharacter_values_apply (g : G) :
    C.irreducibleCharacter.values g =
      C.representation.character g := by
  rw [C.irreducibleCharacter_values]

@[simp]
theorem irreducibleCharacter_degree :
    C.irreducibleCharacter.degree =
      Module.finrank ℂ C.representation := by
  letI : Simple C.representation := C.simple
  rfl

/-- A certified row whose representation dimension is prime to `p`, packaged
as a `p'`-degree irreducible character. -/
def pPrimeIrreducibleCharacter
    (p : ℕ)
    (hdegree : ¬p ∣ Module.finrank ℂ C.representation) :
    PPrimeIrreducibleCharacter G p :=
  ⟨C.irreducibleCharacter, by
    rw [IrreducibleCharacter.IsPPrimeDegree,
      C.irreducibleCharacter_degree]
    exact hdegree⟩

@[simp]
theorem pPrimeIrreducibleCharacter_degree
    (p : ℕ)
    (hdegree : ¬p ∣ Module.finrank ℂ C.representation) :
    (C.pPrimeIrreducibleCharacter p hdegree).1.degree =
      Module.finrank ℂ C.representation :=
  C.irreducibleCharacter_degree

/-- Build a row certificate directly from an unbundled representation.
This is the entry point intended for presentation-generator matrices. -/
def ofRepresentation
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V)
    (hnorm :
      ClassFunction.normalizedPairing
          (ClassFunction.ofFDRep (FDRep.of ρ))
          (ClassFunction.ofFDRep (FDRep.of ρ)) =
        1) :
    CharacterRowCertificate G where
  representation := FDRep.of ρ
  normalizedSelfPairing := hnorm

/-- Build a row certificate from the equivalent unnormalized character sum.
This form is convenient when a finite presentation has been exhaustively
enumerated and the generated proof evaluates the sum explicitly. -/
def ofCharacterSum
    (V : FDRep ℂ G)
    (hnorm :
      characterSelfPairingSum V =
        (Nat.card G : ℂ)) :
    CharacterRowCertificate G where
  representation := V
  normalizedSelfPairing := by
    rw [normalizedPairing_ofFDRep_self, hnorm]
    exact inv_mul_cancel₀
      (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- Build a row certificate from an unbundled representation and its
unnormalized character sum. -/
def ofRepresentationCharacterSum
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V)
    (hnorm :
      characterSelfPairingSum (FDRep.of ρ) =
        (Nat.card G : ℂ)) :
    CharacterRowCertificate G :=
  ofCharacterSum (FDRep.of ρ) hnorm

end CharacterRowCertificate
end McKayConjecture
