/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Automorphism

/-!
# Inner automorphisms act trivially on ordinary characters
-/

noncomputable section

open CategoryTheory

universe u

namespace McKayConjecture

variable {G : Type u} [Group G]

namespace IrreducibleCharacter

/-- Irreducible character values are constant on conjugacy classes. -/
theorem values_eq_of_isConj
    (χ : IrreducibleCharacter G) {x y : G}
    (hxy : IsConj x y) :
    χ.values x = χ.values y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
  obtain ⟨V, _, hV, _⟩ := χ.isIrreducible
  rw [← congrFun hV (g * x * g⁻¹),
    ← congrFun hV x]
  exact (V.char_conj x g).symm

/-- Inner automorphisms fix every irreducible character. -/
@[simp]
theorem conj_smul (g : G) (χ : IrreducibleCharacter G) :
    MulAut.conj g • χ = χ := by
  apply IrreducibleCharacter.ext
  funext x
  simp only [smul_values, MulAut.conj_symm_apply]
  obtain ⟨V, _, hV, _⟩ := χ.isIrreducible
  have hconj := V.char_conj x g⁻¹
  simp only [inv_inv] at hconj
  rw [← congrFun hV (g⁻¹ * x * g),
    ← congrFun hV x]
  exact hconj

end IrreducibleCharacter

/-- Inner automorphisms also fix the subtype of characters of
`p'`-degree. -/
@[simp]
theorem pPrime_conj_smul (p : ℕ) (g : G)
    (χ : PPrimeIrreducibleCharacter G p) :
    MulAut.conj g • χ = χ := by
  apply Subtype.ext
  exact IrreducibleCharacter.conj_smul g χ.1

end McKayConjecture
