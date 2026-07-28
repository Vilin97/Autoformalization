/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Cardinality of a conjugacy class

This file records the orbit--stabilizer formula for conjugation in a
form phrased directly with `ConjClasses` and a singleton centralizer.
-/

noncomputable section

namespace McKayConjecture

/-- The cardinality of the conjugacy class of `x`, multiplied by the
cardinality of its centralizer, is the order of the ambient group. -/
theorem card_conjClass_mul_card_centralizer
    {H : Type} [Group H] [Finite H] (x : H) :
    Nat.card (ConjClasses.mk x).carrier *
        Nat.card (Subgroup.centralizer ({x} : Set H)) =
      Nat.card H := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  have h :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (ConjAct H) x
  simp only [Nat.card_eq_fintype_card]
  change
    Fintype.card (ConjClasses.mk x).carrier *
        Fintype.card (Subgroup.centralizer ({x} : Set H)) =
      Fintype.card H
  calc
    _ =
        Fintype.card (ConjClasses.mk x).carrier *
          Fintype.card
            (MulAction.stabilizer (ConjAct H) x) := by
      congr 1
      simpa only [Nat.card_eq_fintype_card] using
        Subgroup.nat_card_centralizer_nat_card_stabilizer x
    _ = Fintype.card (ConjAct H) := by
      simpa only [ConjAct.orbit_eq_carrier_conjClasses] using h
    _ = Fintype.card H :=
      Fintype.card_congr
        ConjAct.toConjAct.toEquiv.symm

end McKayConjecture
