/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixThreeNormalizerCoordinateModel

/-!
# Conjugacy invariants for the three-normalizer coordinate model

This file isolates the small polynomial calculations used to classify
conjugacy in the order-`216` group
`3^(1+2) ⋊ C₈`.  Keeping these calculations separate avoids asking the
kernel to reduce a quotient of all `216` elements at once.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixThreeHeisenbergCoordinates

/-- The quadratic norm on the noncentral quotient of the Heisenberg
factor. -/
def alternatingSixThreeHeisenbergQuotientNorm
    (q : AlternatingSixThreeHeisenbergCoordinates) : ZMod 3 :=
  q.x ^ 2 + q.y ^ 2

/-- The three twisted-conjugacy invariants for the nontrivial powers of
the order-four action.  The values at residues zero and four are harmless
placeholders; those two cosets are classified by the Heisenberg orbit
invariant instead. -/
def alternatingSixThreeTwistedConjugacyInvariant
    (c : AlternatingSixThreeCyclicEight)
    (q : AlternatingSixThreeHeisenbergCoordinates) : ZMod 3 :=
  match (Multiplicative.toAdd c).val with
  | 1 | 5 =>
      q.z - q.x + q.y - q.x ^ 2 + q.x * q.y - q.y ^ 2
  | 2 | 6 =>
      q.z - q.x + q.y + q.x * q.y
  | _ =>
      q.z - q.x + q.y + q.x ^ 2 + q.x * q.y + q.y ^ 2

/-- The coordinate action is given by the four displayed polynomial
formulas, according to the residue modulo four. -/
def alternatingSixThreeHeisenbergCoordinateActionFormula
    (c : AlternatingSixThreeCyclicEight)
    (q : AlternatingSixThreeHeisenbergCoordinates) :
    AlternatingSixThreeHeisenbergCoordinates :=
  match (Multiplicative.toAdd c).val with
  | 0 | 4 => q
  | 1 | 5 =>
      ⟨q.z + q.x - q.x * q.y, -q.y, q.x⟩
  | 2 | 6 =>
      ⟨q.z + q.x - q.y, -q.x, -q.y⟩
  | _ =>
      ⟨q.z - q.y - q.x * q.y, q.y, -q.x⟩

/-- The explicit polynomial action formula agrees with the `ZMod
8`-indexed automorphism used in the semidirect product. -/
theorem alternatingSixThreeHeisenbergCoordinateAction_apply
    (c : AlternatingSixThreeCyclicEight)
    (q : AlternatingSixThreeHeisenbergCoordinates) :
    alternatingSixThreeHeisenbergCoordinateAction c q =
      alternatingSixThreeHeisenbergCoordinateActionFormula c q := by
  generalize hd : Multiplicative.toAdd c = d
  have hc : c = Multiplicative.ofAdd d := by
    apply Multiplicative.toAdd.injective
    exact hd
  subst c
  have hpower (n : ℕ) :
      alternatingSixThreeHeisenbergCoordinateAction
          (Multiplicative.ofAdd (n : ZMod 8)) =
        alternatingSixThreeHeisenbergCoordinateGenerator ^ n := by
    change
      QuaternionGroup.zmodPower
          alternatingSixThreeHeisenbergCoordinateGenerator
          alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
          (n : ZMod 8) =
        alternatingSixThreeHeisenbergCoordinateGenerator ^ n
    exact
      QuaternionGroup.zmodPower_natCast
        alternatingSixThreeHeisenbergCoordinateGenerator
        alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
        n
  have hval0 : (0 : ZMod 8).val = 0 := by decide
  have hval1 : (1 : ZMod 8).val = 1 := by decide
  have hval2 : (2 : ZMod 8).val = 2 := by decide
  have hval3 : (3 : ZMod 8).val = 3 := by decide
  have hval4 : (4 : ZMod 8).val = 4 := by decide
  have hval5 : (5 : ZMod 8).val = 5 := by decide
  have hval6 : (6 : ZMod 8).val = 6 := by decide
  have hval7 : (7 : ZMod 8).val = 7 := by decide
  have hdlt : d.val < 8 := ZMod.val_lt d
  have hdcast : d = (d.val : ZMod 8) := by
    apply ZMod.val_injective 8
    rw [ZMod.val_natCast]
    exact (Nat.mod_eq_of_lt hdlt).symm
  interval_cases hdv : d.val
  all_goals
    rw [hdcast]
  all_goals
    first
    | rw [hpower 0]
    | rw [hpower 1]
    | rw [hpower 2]
    | rw [hpower 3]
    | rw [hpower 4]
    | rw [hpower 5]
    | rw [hpower 6]
    | rw [hpower 7]
  all_goals
    simp [alternatingSixThreeHeisenbergCoordinateActionFormula,
      alternatingSixThreeHeisenbergCoordinateGenerator, pow_succ,
      hval0, hval1, hval2, hval3, hval4, hval5, hval6, hval7]
  all_goals
    first
    | ring
    | apply AlternatingSixThreeHeisenbergCoordinates.ext <;> ring

/-- A case principle exposing the eight concrete residues of the cyclic
factor without unfolding its implementation throughout later proofs. -/
theorem alternatingSixThreeCyclicEight_cases
    {P : AlternatingSixThreeCyclicEight → Prop}
    (h0 : P (Multiplicative.ofAdd (0 : ZMod 8)))
    (h1 : P (Multiplicative.ofAdd (1 : ZMod 8)))
    (h2 : P (Multiplicative.ofAdd (2 : ZMod 8)))
    (h3 : P (Multiplicative.ofAdd (3 : ZMod 8)))
    (h4 : P (Multiplicative.ofAdd (4 : ZMod 8)))
    (h5 : P (Multiplicative.ofAdd (5 : ZMod 8)))
    (h6 : P (Multiplicative.ofAdd (6 : ZMod 8)))
    (h7 : P (Multiplicative.ofAdd (7 : ZMod 8)))
    (c : AlternatingSixThreeCyclicEight) :
    P c := by
  let d : ZMod 8 := Multiplicative.toAdd c
  have hdlt : d.val < 8 := ZMod.val_lt d
  have hdcast : d = (d.val : ZMod 8) := by
    apply ZMod.val_injective 8
    rw [ZMod.val_natCast]
    exact (Nat.mod_eq_of_lt hdlt).symm
  rw [show c = Multiplicative.ofAdd d by rfl, hdcast]
  interval_cases hdv : d.val <;> assumption

@[simp]
theorem alternatingSixThreeCyclicEight_val_zero :
    (0 : ZMod 8).val = 0 := by
  decide

@[simp]
theorem alternatingSixThreeCyclicEight_val_one :
    (1 : ZMod 8).val = 1 := by
  decide

@[simp]
theorem alternatingSixThreeCyclicEight_val_two :
    (2 : ZMod 8).val = 2 := by
  decide

@[simp]
theorem alternatingSixThreeCyclicEight_val_three :
    (3 : ZMod 8).val = 3 := by
  decide

@[simp]
theorem alternatingSixThreeCyclicEight_val_four :
    (4 : ZMod 8).val = 4 := by
  decide

@[simp]
theorem alternatingSixThreeCyclicEight_val_five :
    (5 : ZMod 8).val = 5 := by
  decide

@[simp]
theorem alternatingSixThreeCyclicEight_val_six :
    (6 : ZMod 8).val = 6 := by
  decide

@[simp]
theorem alternatingSixThreeCyclicEight_val_seven :
    (7 : ZMod 8).val = 7 := by
  decide

@[simp]
theorem alternatingSixThreeZModThree_mul_two (a : ZMod 3) :
    a * 2 = -a := by
  rw [show (2 : ZMod 3) = -1 by decide, mul_neg, mul_one]

@[simp]
theorem alternatingSixThreeZModThree_two_mul (a : ZMod 3) :
    2 * a = -a := by
  rw [mul_comm, alternatingSixThreeZModThree_mul_two]

@[simp]
theorem alternatingSixThreeZModThree_two_zsmul (a : ZMod 3) :
    (2 : ℤ) • a = -a := by
  rw [← Int.cast_smul_eq_zsmul (R := ZMod 3)]
  change (2 : ZMod 3) * a = -a
  exact alternatingSixThreeZModThree_two_mul a

@[simp]
theorem alternatingSixThreeZModThree_neg_two_zsmul (a : ZMod 3) :
    (-2 : ℤ) • a = a := by
  rw [← Int.cast_smul_eq_zsmul (R := ZMod 3)]
  change ((-2 : ℤ) : ZMod 3) * a = a
  rw [show ((-2 : ℤ) : ZMod 3) = 1 by decide, one_mul]

/-- The quadratic quotient norm is fixed by the full cyclic action. -/
theorem alternatingSixThreeHeisenbergQuotientNorm_action
    (c : AlternatingSixThreeCyclicEight)
    (q : AlternatingSixThreeHeisenbergCoordinates) :
    alternatingSixThreeHeisenbergQuotientNorm
        (alternatingSixThreeHeisenbergCoordinateAction c q) =
      alternatingSixThreeHeisenbergQuotientNorm q := by
  apply alternatingSixThreeCyclicEight_cases (c := c)
  all_goals
    rw [alternatingSixThreeHeisenbergCoordinateAction_apply]
    simp [alternatingSixThreeHeisenbergCoordinateActionFormula,
      alternatingSixThreeHeisenbergQuotientNorm]
  all_goals
    try rw [show (2 : ZMod 3) = -1 by decide]
    ring

/-- The polynomial attached to a nontrivial action residue is unchanged
by applying the cyclic generator action. -/
theorem alternatingSixThreeTwistedConjugacyInvariant_action
    (c d : AlternatingSixThreeCyclicEight)
    (q : AlternatingSixThreeHeisenbergCoordinates)
    (hc0 : (Multiplicative.toAdd c).val ≠ 0)
    (hc4 : (Multiplicative.toAdd c).val ≠ 4) :
    alternatingSixThreeTwistedConjugacyInvariant c
        (alternatingSixThreeHeisenbergCoordinateAction d q) =
      alternatingSixThreeTwistedConjugacyInvariant c q := by
  revert hc0 hc4
  apply alternatingSixThreeCyclicEight_cases (c := c)
  · intro hc0
    simp at hc0
  · intro _ _
    apply alternatingSixThreeCyclicEight_cases (c := d)
    all_goals
      rw [alternatingSixThreeHeisenbergCoordinateAction_apply]
      simp [alternatingSixThreeHeisenbergCoordinateActionFormula,
        alternatingSixThreeTwistedConjugacyInvariant]
    all_goals
      try simp only [alternatingSixThreeZModThree_mul_two]
      try abel_nf
      try simp [mul_comm q.y q.x]
      try abel_nf
      try simp [mul_comm q.y q.x]
  · intro _ _
    apply alternatingSixThreeCyclicEight_cases (c := d)
    all_goals
      rw [alternatingSixThreeHeisenbergCoordinateAction_apply]
      simp [alternatingSixThreeHeisenbergCoordinateActionFormula,
        alternatingSixThreeTwistedConjugacyInvariant]
    all_goals
      try simp only [alternatingSixThreeZModThree_mul_two]
      try abel_nf
      try simp [mul_comm q.y q.x]
      try abel_nf
      try simp [mul_comm q.y q.x]
  · intro _ _
    apply alternatingSixThreeCyclicEight_cases (c := d)
    all_goals
      rw [alternatingSixThreeHeisenbergCoordinateAction_apply]
      simp [alternatingSixThreeHeisenbergCoordinateActionFormula,
        alternatingSixThreeTwistedConjugacyInvariant]
    all_goals
      try simp only [alternatingSixThreeZModThree_mul_two]
      try abel_nf
      try simp [mul_comm q.y q.x]
      try abel_nf
      try simp [mul_comm q.y q.x]
  · intro _ hc4
    simp at hc4
  · intro _ _
    apply alternatingSixThreeCyclicEight_cases (c := d)
    all_goals
      rw [alternatingSixThreeHeisenbergCoordinateAction_apply]
      simp [alternatingSixThreeHeisenbergCoordinateActionFormula,
        alternatingSixThreeTwistedConjugacyInvariant]
    all_goals
      try simp only [alternatingSixThreeZModThree_mul_two]
      try abel_nf
      try simp [mul_comm q.y q.x]
      try abel_nf
      try simp [mul_comm q.y q.x]
  · intro _ _
    apply alternatingSixThreeCyclicEight_cases (c := d)
    all_goals
      rw [alternatingSixThreeHeisenbergCoordinateAction_apply]
      simp [alternatingSixThreeHeisenbergCoordinateActionFormula,
        alternatingSixThreeTwistedConjugacyInvariant]
    all_goals
      try simp only [alternatingSixThreeZModThree_mul_two]
      try abel_nf
      try simp [mul_comm q.y q.x]
      try abel_nf
      try simp [mul_comm q.y q.x]
  · intro _ _
    apply alternatingSixThreeCyclicEight_cases (c := d)
    all_goals
      rw [alternatingSixThreeHeisenbergCoordinateAction_apply]
      simp [alternatingSixThreeHeisenbergCoordinateActionFormula,
        alternatingSixThreeTwistedConjugacyInvariant]
    all_goals
      try simp only [alternatingSixThreeZModThree_mul_two]
      try abel_nf
      try simp [mul_comm q.y q.x]
      try abel_nf
      try simp [mul_comm q.y q.x]

end GroupTheory
end McKayConjecture
