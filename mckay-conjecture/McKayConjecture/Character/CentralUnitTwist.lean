/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralUnit
import McKayConjecture.Character.Twist

/-!
# Central units under linear twists

Twisting an irreducible character by a linear character multiplies its
canonical scalar at every central element by the value of that linear
character.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type*} [Group G]

@[simp]
theorem twist_centralUnit
    (lam : G →* ℂˣ)
    (χ : IrreducibleCharacter G)
    (z : G)
    (hz : z ∈ Subgroup.center G) :
    (twist lam χ).centralUnit z hz =
      lam z * χ.centralUnit z hz := by
  apply Units.ext
  have hdegree :
      ((twist lam χ).degree : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (twist lam χ).degree_ne_zero
  apply mul_right_cancel₀ hdegree
  calc
    ((twist lam χ).centralUnit z hz : ℂ) *
          ((twist lam χ).degree : ℂ) =
        (twist lam χ).values z :=
      ((twist lam χ).values_eq_centralUnit_mul_degree z hz).symm
    _ = (lam z : ℂ) * χ.values z := by
      rw [twist_values]
    _ =
        ((lam z * χ.centralUnit z hz : ℂˣ) : ℂ) *
          ((twist lam χ).degree : ℂ) := by
      rw [χ.values_eq_centralUnit_mul_degree z hz,
        twist_degree]
      simp [mul_assoc]

end IrreducibleCharacter
end McKayConjecture
