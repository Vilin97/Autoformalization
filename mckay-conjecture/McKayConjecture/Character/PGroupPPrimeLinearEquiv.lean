/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DegreeOneLinear
import McKayConjecture.Character.PGroupPPrimeLinear

/-!
# Linear parametrization for finite `p`-groups

Combining linearity of prime-to-`p` irreducible characters of a finite
`p`-group with the determinant parametrization gives an explicit
equivalence with multiplicative complex characters.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- Prime-to-`p` irreducible characters of a finite `p`-group are exactly
its linear characters. -/
def pGroupPPrimeLinearEquiv
    (hG : IsPGroup p G) :
    PPrimeIrreducibleCharacter G p ≃
      (G →* ℂˣ) where
  toFun χ :=
    linearParameterOfDegreeOne χ.1
      (degree_eq_one_of_isPGroup_of_isPPrimeDegree hG χ.1 χ.2)
  invFun lam :=
    ⟨linear lam, linear_isPPrimeDegree lam p⟩
  left_inv χ := by
    apply Subtype.ext
    exact
      linear_linearParameterOfDegreeOne χ.1
        (degree_eq_one_of_isPGroup_of_isPPrimeDegree
          hG χ.1 χ.2)
  right_inv lam := by
    apply linear_injective
    exact
      linear_linearParameterOfDegreeOne
        (linear lam) (linear_degree lam)

end IrreducibleCharacter
end McKayConjecture
