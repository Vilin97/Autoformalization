/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.Module
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverRewrite

/-!
# Relations among the central generators of the `6.A₆` presentation

Two closed rewrite paths, together with the two explicit lattice
relations in the presentation, generate a sublattice of index six in
`ℤ⁴`.  The integer row reductions are recorded explicitly below.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- A checked closed path yields the corresponding central relation. -/
theorem alternatingSixSchurWeight_eq_one_of_loop
    (loop : AlternatingSixRewriteLoop)
    (hvalid :
      AlternatingSixRewriteLoop.Valid
          alternatingSixRewriteRules loop = true)
    (hearlier :
      alternatingSixRewriteProofUsesEarlierRules
          188 loop.proof = true) :
    alternatingSixSchurWeight loop.weight = 1 := by
  simp only [AlternatingSixRewriteLoop.Valid] at hvalid
  obtain ⟨happlyBool, hweightBool⟩ :=
    Bool.and_eq_true_iff.mp hvalid
  have happly := of_decide_eq_true happlyBool
  have hweight := of_decide_eq_true hweightBool
  have hsound :=
    alternatingSixSchurApplyProof_sound
      loop.word loop.word loop.proof
      (fun atom hatom => by
        apply alternatingSixSchurAtomPattern_sound 188 le_rfl
        · intro j _
          exact alternatingSixSchurRewriteRule_sound j
        · intro hkind
          have hentry :=
            List.all_eq_true.mp hearlier atom hatom
          rcases Bool.or_eq_true_iff.mp hentry with
            hne | hlt
          · exact False.elim
              ((of_decide_eq_true hne) hkind)
          · exact of_decide_eq_true hlt)
      happly
  rw [hweight] at hsound
  apply mul_left_cancel
    (a := alternatingSixSchurWord loop.word)
  simpa using hsound.symm

/-- The first selected loop is accepted by the executable checker. -/
theorem alternatingSixRewriteKernelLoop1_valid :
    AlternatingSixRewriteLoop.Valid
        alternatingSixRewriteRules
        alternatingSixRewriteKernelLoop1 = true := by
  decide

/-- Rule citations in the first loop are in range. -/
theorem alternatingSixRewriteKernelLoop1_uses_rules :
    alternatingSixRewriteProofUsesEarlierRules
        188 alternatingSixRewriteKernelLoop1.proof = true := by
  decide

/-- The second selected loop is accepted by the executable checker. -/
theorem alternatingSixRewriteKernelLoop2_valid :
    AlternatingSixRewriteLoop.Valid
        alternatingSixRewriteRules
        alternatingSixRewriteKernelLoop2 = true := by
  decide

/-- Rule citations in the second loop are in range. -/
theorem alternatingSixRewriteKernelLoop2_uses_rules :
    alternatingSixRewriteProofUsesEarlierRules
        188 alternatingSixRewriteKernelLoop2.proof = true := by
  decide

/-- First closed-path relation, with weight `(-5,-5,0,2)`. -/
theorem alternatingSixSchurLoopRelationOne :
    alternatingSixSchurWeight ![(-5 : ℤ), -5, 0, 2] = 1 := by
  simpa [alternatingSixRewriteKernelLoop1] using
    alternatingSixSchurWeight_eq_one_of_loop
      alternatingSixRewriteKernelLoop1
      alternatingSixRewriteKernelLoop1_valid
      alternatingSixRewriteKernelLoop1_uses_rules

/-- Second closed-path relation, with weight `(-55,-25,24,-2)`. -/
theorem alternatingSixSchurLoopRelationTwo :
    alternatingSixSchurWeight ![(-55 : ℤ), -25, 24, -2] = 1 := by
  simpa [alternatingSixRewriteKernelLoop2] using
    alternatingSixSchurWeight_eq_one_of_loop
      alternatingSixRewriteKernelLoop2
      alternatingSixRewriteKernelLoop2_valid
      alternatingSixRewriteKernelLoop2_uses_rules

/-- The first defining lattice relation as a central weight. -/
theorem alternatingSixSchurLatticeRelationOne :
    alternatingSixSchurWeight ![(3 : ℤ), 0, -2, 1] = 1 := by
  have h :=
    alternatingSixSchurRelator_eq_one
      (show alternatingSixSchurLatticeRelatorOne ∈
          alternatingSixSchurRelators by
        simp [alternatingSixSchurRelators])
  simpa [alternatingSixSchurWeight,
    alternatingSixSchurWeightAdditive,
    alternatingSixSchurCentralK,
    alternatingSixSchurLatticeRelatorOne,
    alternatingSixSchurFreeK,
    alternatingSixSchurPresentedK,
    alternatingSixSchurPresentedGenerator,
    alternatingSixSchurGenerator,
    PresentedGroup.of, mul_assoc] using h

/-- The second defining lattice relation as a central weight. -/
theorem alternatingSixSchurLatticeRelationTwo :
    alternatingSixSchurWeight ![(0 : ℤ), 4, 3, -3] = 1 := by
  have h :=
    alternatingSixSchurRelator_eq_one
      (show alternatingSixSchurLatticeRelatorTwo ∈
          alternatingSixSchurRelators by
        simp [alternatingSixSchurRelators])
  simpa [alternatingSixSchurWeight,
    alternatingSixSchurWeightAdditive,
    alternatingSixSchurCentralK,
    alternatingSixSchurLatticeRelatorTwo,
    alternatingSixSchurFreeK,
    alternatingSixSchurPresentedK,
    alternatingSixSchurPresentedGenerator,
    alternatingSixSchurGenerator,
    PresentedGroup.of, mul_assoc] using h

/-- Multiplicative weight one is the same as additive weight zero. -/
theorem alternatingSixSchurWeightAdditive_eq_zero
    {weight : Fin 4 → ℤ}
    (hweight : alternatingSixSchurWeight weight = 1) :
    alternatingSixSchurWeightAdditive weight = 0 := by
  have hcenter :
      Additive.toMul
          (alternatingSixSchurWeightAdditive weight) =
        (1 :
          Subgroup.center
            AlternatingSixSchurPresentedGroup) := by
    apply Subtype.ext
    exact hweight
  have h := congrArg Additive.ofMul hcenter
  simpa using h

/-- Additive notation for the four central generators. -/
def alternatingSixSchurCentralKAdditive
    (i : Fin 4) :
    Additive
      (Subgroup.center AlternatingSixSchurPresentedGroup) :=
  Additive.ofMul (alternatingSixSchurCentralK i)

/-- The four lattice rows as additive equations. -/
theorem alternatingSixSchurAdditiveRelations :
    3 • alternatingSixSchurCentralKAdditive 0 -
          2 • alternatingSixSchurCentralKAdditive 2 +
          alternatingSixSchurCentralKAdditive 3 = 0 ∧
      4 • alternatingSixSchurCentralKAdditive 1 +
          3 • alternatingSixSchurCentralKAdditive 2 -
          3 • alternatingSixSchurCentralKAdditive 3 = 0 ∧
      -5 • alternatingSixSchurCentralKAdditive 0 -
          5 • alternatingSixSchurCentralKAdditive 1 +
          2 • alternatingSixSchurCentralKAdditive 3 = 0 ∧
      -55 • alternatingSixSchurCentralKAdditive 0 -
          25 • alternatingSixSchurCentralKAdditive 1 +
          24 • alternatingSixSchurCentralKAdditive 2 -
          2 • alternatingSixSchurCentralKAdditive 3 = 0 := by
  have h0 :=
    alternatingSixSchurWeightAdditive_eq_zero
      alternatingSixSchurLatticeRelationOne
  have h1 :=
    alternatingSixSchurWeightAdditive_eq_zero
      alternatingSixSchurLatticeRelationTwo
  have h2 :=
    alternatingSixSchurWeightAdditive_eq_zero
      alternatingSixSchurLoopRelationOne
  have h3 :=
    alternatingSixSchurWeightAdditive_eq_zero
      alternatingSixSchurLoopRelationTwo
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert h0 using 1 <;>
      simp [alternatingSixSchurWeightAdditive,
        alternatingSixSchurCentralKAdditive,
        sub_eq_add_neg, neg_smul] <;>
      abel
  · convert h1 using 1 <;>
      simp [alternatingSixSchurWeightAdditive,
        alternatingSixSchurCentralKAdditive,
        sub_eq_add_neg, neg_smul] <;>
      abel
  · convert h2 using 1 <;>
      simp [alternatingSixSchurWeightAdditive,
        alternatingSixSchurCentralKAdditive,
        sub_eq_add_neg, neg_smul] <;>
      abel
  · convert h3 using 1 <;>
      simp [alternatingSixSchurWeightAdditive,
        alternatingSixSchurCentralKAdditive,
        sub_eq_add_neg, neg_smul] <;>
      abel

/-- The four central generators reduce to one generator of exponent six. -/
theorem alternatingSixSchurCentralKAdditive_reduce :
    alternatingSixSchurCentralKAdditive 1 =
          3 • alternatingSixSchurCentralKAdditive 0 ∧
      alternatingSixSchurCentralKAdditive 2 =
          -alternatingSixSchurCentralKAdditive 0 ∧
      alternatingSixSchurCentralKAdditive 3 =
          alternatingSixSchurCentralKAdditive 0 ∧
      6 • alternatingSixSchurCentralKAdditive 0 = 0 := by
  let q0 := alternatingSixSchurCentralKAdditive 0
  let q1 := alternatingSixSchurCentralKAdditive 1
  let q2 := alternatingSixSchurCentralKAdditive 2
  let q3 := alternatingSixSchurCentralKAdditive 3
  let r0 := 3 • q0 - 2 • q2 + q3
  let r1 := 4 • q1 + 3 • q2 - 3 • q3
  let r2 := -5 • q0 - 5 • q1 + 2 • q3
  let r3 := -55 • q0 - 25 • q1 + 24 • q2 - 2 • q3
  have hr := alternatingSixSchurAdditiveRelations
  have hr0 : r0 = 0 := hr.1
  have hr1 : r1 = 0 := hr.2.1
  have hr2 : r2 = 0 := hr.2.2.1
  have hr3 : r3 = 0 := hr.2.2.2
  have hq1zero : q1 - 3 • q0 = 0 := by
    calc
      q1 - 3 • q0 =
          (-6 : ℤ) • r0 + 4 • r1 +
            8 • r2 - r3 := by
              dsimp [r0, r1, r2, r3]
              abel
      _ = 0 := by rw [hr0, hr1, hr2, hr3]; simp
  have hq2zero : q2 + q0 = 0 := by
    calc
      q2 + q0 =
          7 • r0 + 5 • r1 + 4 • r2 := by
            dsimp [r0, r1, r2]
            abel
      _ = 0 := by rw [hr0, hr1, hr2]; simp
  have hq3zero : q3 - q0 = 0 := by
    calc
      q3 - q0 =
          3 • r0 + 10 • r1 + 13 • r2 - r3 := by
            dsimp [r0, r1, r2, r3]
            abel
      _ = 0 := by rw [hr0, hr1, hr2, hr3]; simp
  have hq0six : 6 • q0 = 0 := by
    calc
      6 • q0 =
          12 • r0 - 5 • r2 + r3 := by
            dsimp [r0, r2, r3]
            abel
      _ = 0 := by rw [hr0, hr2, hr3]; simp
  dsimp [q0, q1, q2, q3] at *
  exact
    ⟨sub_eq_zero.mp hq1zero,
      ⟨eq_neg_of_add_eq_zero_left hq2zero,
        ⟨sub_eq_zero.mp hq3zero, hq0six⟩⟩⟩

/-- Every central weight is a multiple of `k₀`. -/
theorem alternatingSixSchurWeightAdditive_reduce
    (weight : Fin 4 → ℤ) :
    alternatingSixSchurWeightAdditive weight =
      (weight 0 + 3 * weight 1 - weight 2 + weight 3) •
        alternatingSixSchurCentralKAdditive 0 := by
  obtain ⟨hk1, hk2, hk3, _⟩ :=
    alternatingSixSchurCentralKAdditive_reduce
  simp only [alternatingSixSchurWeightAdditive,
    alternatingSixSchurCentralKAdditive] at *
  rw [hk1, hk2, hk3]
  module

end GroupTheory
end McKayConjecture
