/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalar

/-!
# Normalized character values on central products

The normalized value `χ(z) / χ(1)` is the scalar by which a central
element acts.  Consequently it is multiplicative on products of central
elements.  The cross-multiplied form below avoids division.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type*} [Group G]

/-- Central character values are multiplicative after normalizing by the
degree. -/
theorem values_mul_mul_degree_of_mem_center
    (χ : IrreducibleCharacter G)
    (a b : G)
    (ha : a ∈ Subgroup.center G)
    (hb : b ∈ Subgroup.center G) :
    χ.values (a * b) * (χ.degree : ℂ) =
      χ.values a * χ.values b := by
  obtain ⟨ca, hca⟩ :=
    χ.exists_realization_scalar_of_mem_center a ha
  obtain ⟨cb, hcb⟩ :=
    χ.exists_realization_scalar_of_mem_center b hb
  have hcab :
      χ.realization.ρ (a * b) =
        (ca * cb) •
          (LinearMap.id :
            Module.End ℂ χ.realization) := by
    rw [map_mul, hca, hcb]
    apply LinearMap.ext
    intro x
    simp [Module.End.mul_apply, smul_smul, mul_comm]
  rw [χ.values_eq_scalar_mul_degree a ca hca,
    χ.values_eq_scalar_mul_degree b cb hcb,
    χ.values_eq_scalar_mul_degree (a * b)
      (ca * cb) hcab]
  ring

end IrreducibleCharacter
end McKayConjecture
