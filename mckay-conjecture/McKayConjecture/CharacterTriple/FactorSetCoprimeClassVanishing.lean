/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetFiniteGroupAnnihilation
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Coprime annihilators force a factor-set class to vanish

If two coprime natural numbers annihilate an element of an additive
commutative group, Bézout's identity forces the element itself to vanish.
For a factor-set class on a finite group, one of the two annihilators can
always be taken to be the order of the group.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple

/-- Two coprime natural-number annihilators force an element of an additive
commutative group to vanish. -/
theorem eq_zero_of_coprime_nsmul_eq_zero
    {M : Type} [AddCommGroup M] {x : M} {m n : ℕ}
    (hcoprime : Nat.Coprime m n)
    (hm : m • x = 0)
    (hn : n • x = 0) :
    x = 0 := by
  obtain ⟨a, b, hab⟩ := hcoprime.isCoprime
  have hm' : (m : ℤ) • x = 0 := by
    simpa only [natCast_zsmul] using hm
  have hn' : (n : ℤ) • x = 0 := by
    simpa only [natCast_zsmul] using hn
  calc
    x = (1 : ℤ) • x := by simp
    _ = (a * (m : ℤ) + b * (n : ℤ)) • x := by rw [hab]
    _ = a • ((m : ℤ) • x) + b • ((n : ℤ) • x) := by
      rw [add_smul, mul_smul, mul_smul]
    _ = 0 := by rw [hm', hn']; simp

namespace FactorSet

variable {G A : Type} [Group G] [Finite G] [CommGroup A]

/-- A factor-set class on a finite group vanishes if it is annihilated by a
natural number coprime to the group order. -/
theorem h2Class_eq_zero_of_coprime
    (α : FactorSet G A) (n : ℕ)
    (hcoprime : Nat.Coprime n (Nat.card G))
    (hn :
      letI := trivialMulDistribMulAction G A
      n • α.h2Class = 0) :
    letI := trivialMulDistribMulAction G A
    α.h2Class = 0 := by
  letI := trivialMulDistribMulAction G A
  exact
    eq_zero_of_coprime_nsmul_eq_zero
      hcoprime hn α.natCard_nsmul_h2Class_eq_zero

end FactorSet
end CharacterTriple
end McKayConjecture
