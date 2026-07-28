/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSet

/-!
# The abelian group of factor sets

Multiplicative factor sets with fixed domain and coefficients form an
abelian group under pointwise multiplication.  Tensor products of projective
representations multiply factor sets, while contragredients invert them, so a
bundled group structure makes cancellation statements exact and reusable.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

variable {G : Type u} {A : Type v} [Monoid G] [CommGroup A]

/-- Pointwise product of two factor sets. -/
protected def mul (α β : FactorSet G A) : FactorSet G A where
  toFun g h := α g h * β g h
  cocycle' g h k := by
    calc
      (α (g * h) k * β (g * h) k) * (α g h * β g h) =
          (α (g * h) k * α g h) *
            (β (g * h) k * β g h) := by ac_rfl
      _ = (α h k * α g (h * k)) *
            (β h k * β g (h * k)) := by
              rw [α.cocycle, β.cocycle]
      _ = (α h k * β h k) *
            (α g (h * k) * β g (h * k)) := by ac_rfl

/-- Pointwise inverse of a factor set. -/
protected def inv (α : FactorSet G A) : FactorSet G A where
  toFun g h := (α g h)⁻¹
  cocycle' g h k := by
    have hc := congrArg Inv.inv (α.cocycle g h k)
    simpa only [mul_inv_rev, mul_comm] using hc

instance instCommGroup : CommGroup (FactorSet G A) where
  mul := FactorSet.mul
  one := FactorSet.one
  inv := FactorSet.inv
  mul_assoc α β γ := by
    ext g h
    exact mul_assoc _ _ _
  one_mul α := by
    ext g h
    exact one_mul _
  mul_one α := by
    ext g h
    exact mul_one _
  inv_mul_cancel α := by
    ext g h
    exact inv_mul_cancel _
  mul_comm α β := by
    ext g h
    exact mul_comm _ _

@[simp]
theorem mul_apply (α β : FactorSet G A) (g h : G) :
    (α * β) g h = α g h * β g h :=
  rfl

@[simp]
theorem inv_apply (α : FactorSet G A) (g h : G) :
    α⁻¹ g h = (α g h)⁻¹ :=
  rfl

@[simp]
theorem one_eq_protected_one :
    (1 : FactorSet G A) = FactorSet.one :=
  rfl

/-- Pointwise multiplication preserves normalization. -/
theorem IsNormalized.mul {α β : FactorSet G A}
    (hα : α.IsNormalized) (hβ : β.IsNormalized) :
    (α * β).IsNormalized := by
  constructor
  · intro g
    simp [hα.1 g, hβ.1 g]
  · intro g
    simp [hα.2 g, hβ.2 g]

/-- Pointwise inversion preserves normalization. -/
theorem IsNormalized.inv {α : FactorSet G A}
    (hα : α.IsNormalized) :
    α⁻¹.IsNormalized := by
  constructor
  · intro g
    simp [hα.1 g]
  · intro g
    simp [hα.2 g]

end FactorSet
end CharacterTriple
end McKayConjecture
