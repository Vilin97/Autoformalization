/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Endopermutation.RelativeSyzygyBasic
import Mathlib.GroupTheory.PGroup

/-!
# Relative syzygies for finite p-groups

If `P` is a finite `p`-group and `Q < P`, then the index of `Q` is
`p ^ n` for a positive exponent `n`.  Hence the relative syzygy
`Ω_{P/Q}(k)` has dimension `p ^ n - 1`.  In particular, its dimension
is positive and coprime to `p`.

The final section specializes these statements to the ordinary
augmentation ideal, corresponding to `Q = ⊥`.
-/

noncomputable section

namespace Representation

section Arithmetic

/-- A positive power of a prime, minus one, is coprime to that prime. -/
theorem primePow_sub_one_coprime
    {p n : ℕ}
    (hp : p.Prime)
    (hn : 0 < n) :
    Nat.Coprime (p ^ n - 1) p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hdvd
  have hpPow : p ∣ p ^ n :=
    dvd_pow_self p hn.ne'
  have hone : p ∣ 1 := by
    apply (Nat.dvd_add_iff_right hdvd).mpr
    simpa [Nat.sub_add_cancel
      (Nat.one_le_pow n p hp.pos)] using hpPow
  exact hp.not_dvd_one hone

/-- Equivalently, a prime does not divide one less than any of its
positive powers. -/
theorem prime_not_dvd_primePow_sub_one
    {p n : ℕ}
    (hp : p.Prime)
    (hn : 0 < n) :
    ¬p ∣ p ^ n - 1 :=
  hp.coprime_iff_not_dvd.mp
    (Nat.coprime_comm.mp
      (primePow_sub_one_coprime hp hn))

end Arithmetic

section PGroupIndex

variable {p : ℕ}
variable {P : Type*} [Group P] [Finite P]

/-- A proper subgroup of a finite `p`-group has index a positive power
of `p`. -/
theorem exists_pos_index_eq_primePow
    [Fact p.Prime]
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q ≠ ⊤) :
    ∃ n : ℕ, 0 < n ∧ Q.index = p ^ n := by
  obtain ⟨n, hn⟩ := hP.index Q
  refine ⟨n, ?_, hn⟩
  apply Nat.pos_of_ne_zero
  intro hn0
  apply hQ
  apply Subgroup.index_eq_one.mp
  simpa [hn0] using hn

/-- One less than the index of a proper subgroup is positive. -/
theorem index_sub_one_pos
    (Q : Subgroup P)
    (hQ : Q ≠ ⊤) :
    0 < Q.index - 1 :=
  Nat.sub_pos_of_lt
    (Subgroup.one_lt_index_of_ne_top hQ)

/-- In a finite `p`-group, one less than the index of a proper subgroup
is coprime to `p`. -/
theorem index_sub_one_coprime
    [Fact p.Prime]
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q ≠ ⊤) :
    Nat.Coprime (Q.index - 1) p := by
  obtain ⟨n, hn, hindex⟩ :=
    exists_pos_index_eq_primePow hP Q hQ
  rw [hindex]
  exact
    primePow_sub_one_coprime
      (Fact.out : p.Prime) hn

/-- In a finite `p`-group, `p` does not divide one less than the index
of a proper subgroup. -/
theorem prime_not_dvd_index_sub_one
    [Fact p.Prime]
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q ≠ ⊤) :
    ¬p ∣ Q.index - 1 :=
  (Fact.out : p.Prime).coprime_iff_not_dvd.mp
    (Nat.coprime_comm.mp
      (index_sub_one_coprime hP Q hQ))

end PGroupIndex

section RelativeSyzygyDimension

variable (k : Type*) [Field k]
variable {p : ℕ}
variable (P : Type*) [Group P] [Finite P]

/-- The dimension of a relative syzygy is one less than the subgroup
index. -/
theorem finrank_relativeSyzygy_eq_index_sub_one
    (Q : Subgroup P) :
    Module.finrank k (relativeSyzygy k P Q) =
      Q.index - 1 :=
  Nat.eq_sub_of_add_eq
    (finrank_relativeSyzygy_add_one_eq_index k P Q)

/-- The relative syzygy of a proper subgroup has positive dimension. -/
theorem finrank_relativeSyzygy_pos
    (Q : Subgroup P)
    (hQ : Q ≠ ⊤) :
    0 < Module.finrank k (relativeSyzygy k P Q) := by
  rw [finrank_relativeSyzygy_eq_index_sub_one]
  exact index_sub_one_pos Q hQ

/-- For a proper subgroup of a finite `p`-group, the relative-syzygy
dimension is one less than a positive power of `p`. -/
theorem exists_pos_finrank_relativeSyzygy_eq_primePow_sub_one
    [Fact p.Prime]
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q ≠ ⊤) :
    ∃ n : ℕ, 0 < n ∧
      Module.finrank k (relativeSyzygy k P Q) =
        p ^ n - 1 := by
  obtain ⟨n, hn, hindex⟩ :=
    exists_pos_index_eq_primePow hP Q hQ
  refine ⟨n, hn, ?_⟩
  rw [finrank_relativeSyzygy_eq_index_sub_one,
    hindex]

/-- For a proper subgroup of a finite `p`-group, the relative-syzygy
dimension is coprime to `p`. -/
theorem finrank_relativeSyzygy_coprime
    [Fact p.Prime]
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q ≠ ⊤) :
    Nat.Coprime
      (Module.finrank k (relativeSyzygy k P Q)) p := by
  rw [finrank_relativeSyzygy_eq_index_sub_one]
  exact index_sub_one_coprime hP Q hQ

/-- Equivalently, `p` does not divide the dimension of the relative
syzygy of a proper subgroup. -/
theorem prime_not_dvd_finrank_relativeSyzygy
    [Fact p.Prime]
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q ≠ ⊤) :
    ¬p ∣ Module.finrank k (relativeSyzygy k P Q) :=
  (Fact.out : p.Prime).coprime_iff_not_dvd.mp
    (Nat.coprime_comm.mp
      (finrank_relativeSyzygy_coprime
        k P hP Q hQ))

/-- Positivity and `p`-coprimality packaged together. -/
theorem finrank_relativeSyzygy_pos_and_coprime
    [Fact p.Prime]
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q ≠ ⊤) :
    0 < Module.finrank k (relativeSyzygy k P Q) ∧
      Nat.Coprime
        (Module.finrank k (relativeSyzygy k P Q)) p :=
  ⟨finrank_relativeSyzygy_pos k P Q hQ,
    finrank_relativeSyzygy_coprime k P hP Q hQ⟩

end RelativeSyzygyDimension

section Bottom

variable (k : Type*) [Field k]
variable {p : ℕ}
variable (P : Type*) [Group P] [Finite P]

/-- For the bottom subgroup, the relative-syzygy dimension is one less
than the order of the group. -/
theorem finrank_relativeSyzygy_bot_eq_card_sub_one :
    Module.finrank k
        (relativeSyzygy k P (⊥ : Subgroup P)) =
      Nat.card P - 1 := by
  rw [finrank_relativeSyzygy_eq_index_sub_one,
    Subgroup.index_bot]

/-- The ordinary augmentation ideal of a nontrivial finite group has
positive dimension. -/
theorem finrank_relativeSyzygy_bot_pos
    [Nontrivial P] :
    0 < Module.finrank k
      (relativeSyzygy k P (⊥ : Subgroup P)) :=
  finrank_relativeSyzygy_pos
    k P (⊥ : Subgroup P) bot_ne_top

/-- For a nontrivial finite `p`-group, the ordinary augmentation-ideal
dimension is one less than a positive power of `p`. -/
theorem exists_pos_finrank_relativeSyzygy_bot_eq_primePow_sub_one
    [Fact p.Prime]
    [Nontrivial P]
    (hP : IsPGroup p P) :
    ∃ n : ℕ, 0 < n ∧
      Module.finrank k
          (relativeSyzygy k P (⊥ : Subgroup P)) =
        p ^ n - 1 :=
  exists_pos_finrank_relativeSyzygy_eq_primePow_sub_one
    k P hP (⊥ : Subgroup P) bot_ne_top

/-- The ordinary augmentation-ideal dimension of a nontrivial finite
`p`-group is coprime to `p`. -/
theorem finrank_relativeSyzygy_bot_coprime
    [Fact p.Prime]
    [Nontrivial P]
    (hP : IsPGroup p P) :
    Nat.Coprime
      (Module.finrank k
        (relativeSyzygy k P (⊥ : Subgroup P))) p :=
  finrank_relativeSyzygy_coprime
    k P hP (⊥ : Subgroup P) bot_ne_top

/-- Equivalently, `p` does not divide the ordinary augmentation-ideal
dimension of a nontrivial finite `p`-group. -/
theorem prime_not_dvd_finrank_relativeSyzygy_bot
    [Fact p.Prime]
    [Nontrivial P]
    (hP : IsPGroup p P) :
    ¬p ∣ Module.finrank k
      (relativeSyzygy k P (⊥ : Subgroup P)) :=
  prime_not_dvd_finrank_relativeSyzygy
    k P hP (⊥ : Subgroup P) bot_ne_top

end Bottom

end Representation
