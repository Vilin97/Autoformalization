/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FiniteOrderTrace
import McKayConjecture.Character.Realization

/-!
# Character values at inverse elements

For a complex representation of a finite group, the value of its character
at `g⁻¹` is the complex conjugate of its value at `g`.  The result does not
require irreducibility.
-/

noncomputable section

open scoped ComplexConjugate

universe u v

namespace Representation

variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/--
The character of any finite-dimensional complex representation of a finite
group takes complex-conjugate values on inverse elements.
-/
@[simp]
theorem character_inv_eq_conj
    (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = conj (ρ.character g) := by
  apply LinearMap.trace_inverse_eq_conj_trace_of_isOfFinOrder
  · rw [← map_mul, mul_inv_cancel, map_one]
  · exact ρ.isOfFinOrder (isOfFinOrder_of_finite g)

end Representation

namespace FDRep

variable {G : Type u} [Group G] [Finite G]

/--
The `FDRep` form of the inverse/conjugate character identity.
-/
@[simp]
theorem character_inv_eq_conj (V : FDRep ℂ G) (g : G) :
    V.character g⁻¹ = conj (V.character g) :=
  Representation.character_inv_eq_conj V.ρ g

end FDRep

namespace McKayConjecture.IrreducibleCharacter

variable {G : Type u} [Group G] [Finite G]

/--
An ordinary irreducible character of a finite group takes
complex-conjugate values on inverse elements.
-/
@[simp]
theorem value_inv_eq_conj (χ : IrreducibleCharacter G) (g : G) :
    χ.values g⁻¹ = conj (χ.values g) := by
  simpa only [χ.realization_character] using
    FDRep.character_inv_eq_conj χ.realization g

end McKayConjecture.IrreducibleCharacter
