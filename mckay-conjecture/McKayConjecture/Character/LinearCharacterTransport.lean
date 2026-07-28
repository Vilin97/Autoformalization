/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Hom.End

/-!
# Transport of multiplicative linear characters

A group equivalence transports homomorphisms into any target monoid by
precomposition.  This is the raw multiplicative-linear-character analogue
of transport for irreducible characters.
-/

noncomputable section

namespace McKayConjecture

variable {G H A : Type} [Group G] [Group H] [Monoid A]

/-- Precomposition with a group equivalence gives an equivalence of
monoid-hom spaces. -/
def monoidHomPrecompMulEquiv (e : H ≃* G) :
    (G →* A) ≃ (H →* A) where
  toFun χ := χ.comp e.toMonoidHom
  invFun χ := χ.comp e.symm.toMonoidHom
  left_inv χ := by
    ext g
    simp
  right_inv χ := by
    ext h
    simp

@[simp]
theorem monoidHomPrecompMulEquiv_apply
    (e : H ≃* G) (χ : G →* A) (h : H) :
    monoidHomPrecompMulEquiv e χ h = χ (e h) :=
  rfl

end McKayConjecture
