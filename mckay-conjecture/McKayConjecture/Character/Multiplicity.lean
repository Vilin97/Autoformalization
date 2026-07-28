/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Induction

/-!
# Character inner products and multiplicities

The normalized character pairing computes the dimension of an intertwiner
space.  This file packages that dimension as the multiplicity used in
Clifford and induction arguments.
-/

noncomputable section

open CategoryTheory

universe u

namespace McKayConjecture

variable {G : Type u} [Group G]

namespace ClassFunction

/-- The standard normalized bilinear character pairing, with the second
argument evaluated at inverses. -/
def characterPairing [Fintype G]
    (f k : ClassFunction G) : ℂ :=
  (Nat.card G : ℂ)⁻¹ *
    ∑ g : G, f g * k g⁻¹

@[simp]
theorem characterPairing_apply [Fintype G]
    (f k : ClassFunction G) :
    ClassFunction.characterPairing f k =
      (Nat.card G : ℂ)⁻¹ *
        ∑ g : G, f g * k g⁻¹ :=
  rfl

end ClassFunction

namespace FDRep

/-- The multiplicity of `V` in `W`, defined as the complex dimension of the
space of equivariant linear maps `V → W`. -/
def multiplicity (V W : FDRep ℂ G) : ℕ :=
  Module.finrank ℂ (V ⟶ W)

@[simp]
theorem multiplicity_eq_finrank (V W : FDRep ℂ G) :
    FDRep.multiplicity V W = Module.finrank ℂ (V ⟶ W) :=
  rfl

/-- For a finite group, the normalized character pairing computes
multiplicity. -/
theorem characterPairing_eq_multiplicity
    [Fintype G] (V W : FDRep ℂ G) :
    ClassFunction.characterPairing
        (FDRep.characterClassFunction W)
        (FDRep.characterClassFunction V) =
      (FDRep.multiplicity V W : ℂ) := by
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  simpa [ClassFunction.characterPairing, multiplicity,
    mul_comm] using
    FDRep.scalar_product_char_eq_finrank_equivariant V W

open Classical in
/-- Schur's lemma computes multiplicity between simple objects. -/
theorem multiplicity_simple_simple
    (V W : FDRep ℂ G) [Simple V] [Simple W] :
    FDRep.multiplicity V W =
      if Nonempty (V ≅ W) then 1 else 0 := by
  classical
  exact FDRep.finrank_hom_simple_simple V W

@[simp]
theorem multiplicity_self
    (V : FDRep ℂ G) [Simple V] :
    FDRep.multiplicity V V = 1 := by
  rw [multiplicity_simple_simple]
  simp

theorem multiplicity_eq_zero_of_not_isomorphic
    (V W : FDRep ℂ G) [Simple V] [Simple W]
    (h : ¬Nonempty (V ≅ W)) :
    FDRep.multiplicity V W = 0 := by
  classical
  rw [multiplicity_simple_simple]
  simp [h]

theorem multiplicity_eq_one_of_isomorphic
    (V W : FDRep ℂ G) [Simple V] [Simple W]
    (h : Nonempty (V ≅ W)) :
    FDRep.multiplicity V W = 1 := by
  classical
  rw [multiplicity_simple_simple]
  simp [h]

end FDRep

namespace IrreducibleCharacter

/-- Multiplicity of an irreducible character in a finite-dimensional
representation. -/
def multiplicity (χ : IrreducibleCharacter G) (V : FDRep ℂ G) : ℕ :=
  FDRep.multiplicity χ.realization V

@[simp]
theorem multiplicity_realization_self
    (χ : IrreducibleCharacter G) :
    IrreducibleCharacter.multiplicity χ χ.realization = 1 :=
  FDRep.multiplicity_self χ.realization

/-- The multiplicity can be read directly from character values. -/
theorem characterPairing_eq_multiplicity
    [Fintype G] (χ : IrreducibleCharacter G) (V : FDRep ℂ G) :
    ClassFunction.characterPairing
        (FDRep.characterClassFunction V)
        χ.toClassFunction =
      (IrreducibleCharacter.multiplicity χ V : ℂ) := by
  simpa [multiplicity, χ.realization_character] using
    FDRep.characterPairing_eq_multiplicity
      χ.realization V

end IrreducibleCharacter
end McKayConjecture
