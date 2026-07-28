/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordCorrespondence

/-!
# Prime-to-`p` degrees in Clifford induction

Clifford induction from the inertia group multiplies character degree by
the inertia index.  This file records the corresponding exact criterion for
prime-to-`p` degree.  Keeping the arithmetic statement separate from the
construction of the Clifford correspondence makes it reusable both before
and after the full correspondence is packaged as an equivalence.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CliffordCorrespondence

variable {G : Type} [Fintype G] [Group G]
variable (N : Subgroup G) [N.Normal]
variable (θ : IrreducibleCharacter N)

/-- A Clifford induction known to be simple has prime-to-`p` degree exactly
when both the inertia index and the source degree are prime to `p`. -/
theorem inducedIrreducibleCharacter_isPPrimeDegree_iff
    {p : ℕ} (hp : p.Prime)
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hsimple : Simple (inertiaInduction (G := G) N θ ψ.realization)) :
    (inducedIrreducibleCharacter (G := G) N θ ψ hsimple).IsPPrimeDegree p ↔
      ¬p ∣ (IrreducibleCharacter.inertia N θ).index ∧
        ψ.IsPPrimeDegree p := by
  rw [IrreducibleCharacter.IsPPrimeDegree,
    inducedIrreducibleCharacter_degree,
    hp.dvd_mul, not_or,
    IrreducibleCharacter.IsPPrimeDegree]

/-- If the inertia index is prime to `p`, Clifford induction preserves
prime-to-`p` degree. -/
theorem inducedIrreducibleCharacter_isPPrimeDegree_iff_of_index
    {p : ℕ} (hp : p.Prime)
    (hindex : ¬p ∣ (IrreducibleCharacter.inertia N θ).index)
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hsimple : Simple (inertiaInduction (G := G) N θ ψ.realization)) :
    (inducedIrreducibleCharacter (G := G) N θ ψ hsimple).IsPPrimeDegree p ↔
      ψ.IsPPrimeDegree p := by
  simpa [hindex] using
    (inducedIrreducibleCharacter_isPPrimeDegree_iff
      N θ hp ψ hsimple)

end CliffordCorrespondence
end McKayConjecture
