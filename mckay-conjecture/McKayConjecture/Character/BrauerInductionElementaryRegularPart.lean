/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionRegularFiber
import McKayConjecture.Character.PRegularDecompositionUniqueness

/-!
# Regular parts in a displayed elementary group

In a `p`-elementary direct product `D × P`, the canonical `p`-regular
part of an element is exactly its `D`-coordinate.  Consequently the
regular-fibre class function at `a ∈ D` is supported on elements whose
canonical `p`-regular part is `a`.

This intrinsic support description is what lets the centralizer
construction distinguish the `p`-regular conjugacy classes of the
ambient group.
-/

noncomputable section

namespace McKayConjecture

universe u

namespace PElementaryDecomposition

variable {p : ℕ} {E : Type u} [Group E]

/-- An element of the displayed cyclic factor is `p`-regular when
regarded in the whole elementary group. -/
theorem cyclicElement_isPRegular
    (D : PElementaryDecomposition p E)
    (c : D.cyclicPart) :
    IsPRegular p (c : E) := by
  rw [IsPRegular]
  change
    p.Coprime
      (orderOf (D.cyclicPart.subtype c))
  rw [
    orderOf_injective D.cyclicPart.subtype
      D.cyclicPart.subtype_injective]
  exact
    Nat.Coprime.of_dvd_right
      (orderOf_dvd_natCard c)
      D.cyclicPart_coprime

/-- An element of the displayed `p`-factor is a `p`-element when
regarded in the whole elementary group. -/
theorem pElement_isPElement
    (D : PElementaryDecomposition p E)
    (t : D.pPart) :
    IsPElement p (t : E) := by
  have ht : IsPElement p t :=
    D.isPGroup t
  exact ht.map p D.pPart.subtype

variable [Finite E] [Fact p.Prime]

/-- The canonical `p`-regular part of an element of an elementary group
is its coordinate in the displayed cyclic factor. -/
theorem chosen_regularPart_eq_cyclicCoordinate
    (D : PElementaryDecomposition p E)
    (x : E) :
    (PRegularDecomposition.chosen p x).regularPart =
      ((D.multiplicationEquiv.symm x).1 : E) := by
  let z := D.multiplicationEquiv.symm x
  have hx :
      (z.1 : E) * (z.2 : E) = x := by
    exact D.multiplicationEquiv.apply_symm_apply x
  calc
    (PRegularDecomposition.chosen p x).regularPart =
        (PRegularDecomposition.chosen
          p ((z.1 : E) * (z.2 : E))).regularPart := by
      rw [hx]
    _ = (z.1 : E) :=
      PRegularDecomposition.chosen_regularPart_mul_rev
        (D.pElement_isPElement z.2)
        (D.cyclicElement_isPRegular z.1)
        (D.commute z.1 z.2)

end PElementaryDecomposition

namespace ClassFunction

variable {p : ℕ} {E : Type} [Group E]
variable [Finite E] [Fact p.Prime]

/-- The regular-fibre function vanishes away from the prescribed
canonical `p`-regular part. -/
theorem regularFiber_apply_eq_zero_of_regularPart_ne
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart) (m : ℕ) (x : E)
    (hx :
      (PRegularDecomposition.chosen p x).regularPart ≠
        (a : E)) :
    regularFiber D a m x = 0 := by
  apply regularFiber_apply_of_cyclicCoordinate_ne
  intro hcoordinate
  apply hx
  rw [D.chosen_regularPart_eq_cyclicCoordinate,
    hcoordinate]

/-- A nonzero value of the regular-fibre function determines the
canonical `p`-regular part. -/
theorem regularPart_eq_of_regularFiber_apply_ne_zero
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart) (m : ℕ) (x : E)
    (hx : regularFiber D a m x ≠ 0) :
    (PRegularDecomposition.chosen p x).regularPart =
      (a : E) := by
  by_contra hne
  exact
    hx
      (regularFiber_apply_eq_zero_of_regularPart_ne
        D a m x hne)

end ClassFunction
end McKayConjecture
