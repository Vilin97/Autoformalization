/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Fintype.BigOperators

/-!
# Invariant weighted sums for actions of finite `p`-groups

The usual fixed-point congruence for a finite `p`-group action extends to
weighted sums whenever the weight is constant on orbits.  We prove this by
replacing an element of weight `n` by `n` labelled copies and applying the
ordinary fixed-point congruence.
-/

open scoped BigOperators

namespace McKayConjecture

namespace PGroupInvariantSum

variable {P α : Type*} [Group P] [MulAction P α]

/-- The finite set obtained by replacing `a` by `f a` labelled copies. -/
def Copies (f : α → ℕ) :=
  {x : α × ℕ // x.2 < f x.1}

/-- Labelled copies are equivalent to the corresponding dependent sum of
finite sets. -/
def copiesEquivSigmaFin (f : α → ℕ) :
    Copies f ≃ Σ a : α, Fin (f a) where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv x := rfl
  right_inv x := rfl

/-- An orbit-invariant weight induces an action on its labelled copies. -/
@[instance_reducible] def copiesMulAction
    (f : α → ℕ)
    (hf : ∀ g : P, ∀ a : α, f (g • a) = f a) :
    MulAction P (Copies f) where
  smul g x :=
    ⟨(g • x.1.1, x.1.2), by
      rw [hf g x.1.1]
      exact x.2⟩
  one_smul x := by
    apply Subtype.ext
    change (1 • x.1.1, x.1.2) = x.1
    rw [one_smul]
  mul_smul g h x := by
    apply Subtype.ext
    change ((g * h) • x.1.1, x.1.2) =
      (g • h • x.1.1, x.1.2)
    rw [mul_smul]

theorem natCard_copies
    [Fintype α] (f : α → ℕ) :
    Nat.card (Copies f) = ∑ a : α, f a := by
  classical
  letI : Fintype (Copies f) :=
    Fintype.ofEquiv (Σ a : α, Fin (f a))
      (copiesEquivSigmaFin f).symm
  rw [Nat.card_congr (copiesEquivSigmaFin f)]
  simp [Nat.card_eq_fintype_card]

/-- For the copy action, a fixed labelled copy is exactly a labelled copy
of a fixed element of the original action. -/
def fixedPointsCopiesEquiv
    (f : α → ℕ)
    (hf : ∀ g : P, ∀ a : α, f (g • a) = f a) :
    letI := copiesMulAction f hf
    MulAction.fixedPoints P (Copies f) ≃
      Σ a : MulAction.fixedPoints P α, Fin (f a.1) := by
  letI := copiesMulAction f hf
  refine
    { toFun := fun x =>
        ⟨⟨x.1.1.1, ?_⟩, ⟨x.1.1.2, x.1.2⟩⟩
      invFun := fun x =>
        ⟨⟨(x.1.1, x.2.1), x.2.2⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply MulAction.mem_fixedPoints.mpr
    intro g
    have hx := (MulAction.mem_fixedPoints.mp x.2 g)
    exact congrArg (fun y : Copies f ↦ y.1.1) hx
  · apply MulAction.mem_fixedPoints.mpr
    intro g
    apply Subtype.ext
    apply Prod.ext
    · exact MulAction.mem_fixedPoints.mp x.1.2 g
    · rfl
  · intro x
    rfl
  · intro x
    rfl

theorem natCard_fixedPoints_copies
    [Fintype α]
    (f : α → ℕ)
    (hf : ∀ g : P, ∀ a : α, f (g • a) = f a) :
    letI := Fintype.ofFinite (MulAction.fixedPoints P α)
    letI := copiesMulAction f hf
    Nat.card (MulAction.fixedPoints P (Copies f)) =
      ∑ a : MulAction.fixedPoints P α, f a.1 := by
  letI := Fintype.ofFinite (MulAction.fixedPoints P α)
  letI := copiesMulAction f hf
  classical
  rw [Nat.card_congr (fixedPointsCopiesEquiv f hf)]
  simp [Nat.card_eq_fintype_card]

/-- A weight constant on orbits has total sum congruent modulo `p` to its
sum over the fixed points. -/
theorem sum_modEq_sum_fixedPoints
    {p : ℕ}
    [Finite P] [Fintype α] [Fact p.Prime]
    (hP : IsPGroup p P)
    (f : α → ℕ)
    (hf : ∀ g : P, ∀ a : α, f (g • a) = f a) :
    letI := Fintype.ofFinite (MulAction.fixedPoints P α)
    (∑ a : α, f a) ≡
      ∑ a : MulAction.fixedPoints P α, f a.1 [MOD p] := by
  letI := Fintype.ofFinite (MulAction.fixedPoints P α)
  letI := copiesMulAction f hf
  letI : Fintype (Copies f) :=
    Fintype.ofEquiv (Σ a : α, Fin (f a))
      (copiesEquivSigmaFin f).symm
  rw [← natCard_copies f, ← natCard_fixedPoints_copies f hf]
  exact hP.card_modEq_card_fixedPoints (Copies f)

end PGroupInvariantSum

end McKayConjecture
