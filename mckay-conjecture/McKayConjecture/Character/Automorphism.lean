/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Transport

/-!
# Automorphisms acting on irreducible characters

Group automorphisms act on characters by the usual contragredient convention
`(a • χ)(g) = χ(a⁻¹(g))`.  Character degrees, and consequently the
`p'`-degree condition, are invariant under this action.
-/

noncomputable section

universe u

namespace McKayConjecture

variable {G : Type u} [Group G]

namespace IrreducibleCharacter

/-- The natural left action of group automorphisms on irreducible
characters. -/
instance : MulAction (MulAut G) (IrreducibleCharacter G) where
  smul a χ := χ.comap a.symm
  one_smul χ := by
    ext
    rfl
  mul_smul a b χ := by
    ext
    rfl

@[simp]
theorem smul_values (a : MulAut G) (χ : IrreducibleCharacter G) (g : G) :
    (a • χ).values g = χ.values (a.symm g) :=
  rfl

@[simp]
theorem smul_degree (a : MulAut G) (χ : IrreducibleCharacter G) :
    (a • χ).degree = χ.degree :=
  rfl

@[simp]
theorem isPPrimeDegree_smul_iff (p : ℕ) (a : MulAut G)
    (χ : IrreducibleCharacter G) :
    (a • χ).IsPPrimeDegree p ↔ χ.IsPPrimeDegree p :=
  Iff.rfl

end IrreducibleCharacter

/-- The automorphism action restricts to the irreducible characters of
`p'`-degree. -/
instance (p : ℕ) :
    MulAction (MulAut G) (PPrimeIrreducibleCharacter G p) where
  smul a χ := ⟨a • χ.1, χ.2⟩
  one_smul χ := by
    apply Subtype.ext
    change (1 : MulAut G) • χ.1 = χ.1
    exact one_smul _ _
  mul_smul a b χ := by
    apply Subtype.ext
    change (a * b) • χ.1 = a • b • χ.1
    exact mul_smul _ _ _

@[simp]
theorem pPrime_smul_coe (p : ℕ) (a : MulAut G)
    (χ : PPrimeIrreducibleCharacter G p) :
    (a • χ).1 = a • χ.1 :=
  rfl

end McKayConjecture
