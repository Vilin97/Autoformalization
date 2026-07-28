/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalar
import McKayConjecture.CharacterTriple.AssociatedExistence

/-!
# Scalar actions for a two-element center

For a group whose center consists of the identity and one distinguished
element, a single character-value calculation determines the scalar by
which every central element acts in the canonical realization.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple

/-- If the center is `{1,c}` and the value at `c` is a prescribed unit
times the degree, then the canonical realization has precisely that
central scalar action. -/
theorem irreducibleCharacter_realizationAction_eq_of_twoPointCenter
    {G : Type*} [Group G] [Finite G]
    (χ : IrreducibleCharacter G)
    (c : G)
    (centralUnit : G → ℂˣ)
    (hcenter :
      ∀ z : G, z ∈ Subgroup.center G →
        z = 1 ∨ z = c)
    (hunit_one : centralUnit 1 = 1)
    (hvalue :
      χ.values c =
        (centralUnit c : ℂ) * (χ.degree : ℂ))
    (z : G) (hz : z ∈ Subgroup.center G) :
    AssociatedExistence.realizationAction χ z =
      scalarLinearEquiv ℂ χ.realization
        (centralUnit z) := by
  rcases hcenter z hz with hz_one | hz_c
  · subst z
    rw [hunit_one]
    simp
  · subst z
    have hc_center : c ∈ Subgroup.center G := hz
    obtain ⟨u, hu⟩ :=
      χ.exists_realization_scalar_of_mem_center c hc_center
    have htrace :=
      χ.values_eq_scalar_mul_degree c (u : ℂ) hu
    have hu_eq : u = (centralUnit c : ℂ) := by
      apply
        mul_right_cancel₀
          (Nat.cast_ne_zero.mpr χ.degree_ne_zero)
      exact htrace.symm.trans hvalue
    ext v
    have hv := LinearMap.congr_fun hu v
    change
      χ.realization.ρ c v =
        (centralUnit c : ℂ) • v
    change
      χ.realization.ρ c v =
        (u : ℂ) • v at hv
    simpa [hu_eq] using hv

end McKayConjecture
