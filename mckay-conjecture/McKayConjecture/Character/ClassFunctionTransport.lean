/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionPairing

/-!
# Transport of class functions across group equivalences

Relabelling a finite group by a multiplication equivalence transports its
class functions linearly and preserves the normalized character pairing.
-/

noncomputable section

namespace McKayConjecture
namespace ClassFunction

universe u v

variable {G : Type u} {H : Type v}
variable [Group G] [Group H]

/-- Pull a class function back along a group equivalence. -/
def comapLinearEquiv (e : H ≃* G) :
    ClassFunction G ≃ₗ[ℂ] ClassFunction H where
  toFun f :=
    ⟨fun h ↦ f (e h), by
      intro h x
      simp only [map_mul, map_inv]
      exact ClassFunction.conj_apply f (e h) (e x)⟩
  map_add' f k := by
    ext h
    rfl
  map_smul' c f := by
    ext h
    rfl
  invFun f :=
    ⟨fun g ↦ f (e.symm g), by
      intro g x
      simp only [map_mul, map_inv]
      exact ClassFunction.conj_apply f (e.symm g) (e.symm x)⟩
  left_inv f := by
    ext g
    simp
  right_inv f := by
    ext h
    simp

@[simp]
theorem comapLinearEquiv_apply
    (e : H ≃* G) (f : ClassFunction G) (h : H) :
    comapLinearEquiv e f h = f (e h) :=
  rfl

/-- Relabelling a finite group preserves the normalized class-function
pairing. -/
theorem normalizedPairing_comapLinearEquiv
    [Finite G] [Finite H]
    (e : H ≃* G)
    (f k : ClassFunction G) :
    normalizedPairing
        (comapLinearEquiv e f)
        (comapLinearEquiv e k) =
      normalizedPairing f k := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype H := Fintype.ofFinite H
  rw [normalizedPairing, LinearMap.mk₂_apply,
    normalizedPairing, LinearMap.mk₂_apply]
  rw [Nat.card_congr e.toEquiv]
  simp only [comapLinearEquiv_apply, map_inv]
  exact congrArg
    (fun z : ℂ ↦ (Nat.card G : ℂ)⁻¹ * z)
    (e.toEquiv.sum_comp
      (fun g : G ↦ f g * k g⁻¹))

end ClassFunction
end McKayConjecture
