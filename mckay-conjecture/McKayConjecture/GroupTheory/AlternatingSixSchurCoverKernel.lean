/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverNormalForm
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverPerfect
import McKayConjecture.GroupTheory.UniversalCentralExtension

/-!
# The kernel of the explicit sixfold-cover presentation

The checked normal forms show that the projection kernel consists only of
central weights.  Cardinality comparison with `A₆` then bounds its order
by six.  The matching lower bound is supplied separately by finite
representations of the presentation.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- Projecting a word in the two noncentral Schur generators agrees with
evaluating the same word in the ordinary `A₆` presentation. -/
theorem alternatingSixSchurProjection_word
    (word : AlternatingSixRewriteWord) :
    alternatingSixSchurProjection
        (alternatingSixSchurWord word) =
      alternatingSixPresentationToAlternatingSix
        (alternatingSixPresentedWord word) := by
  induction word with
  | nil =>
      simp [alternatingSixSchurWord_nil,
        alternatingSixPresentedWord_nil]
  | cons letter word ih =>
      rcases letter with ⟨generator, positive⟩
      rw [show
          ((generator, positive) :: word) =
            [(generator, positive)] ++ word by rfl,
        alternatingSixSchurWord_append,
        alternatingSixPresentedWord_append,
        map_mul, map_mul, ih]
      fin_cases generator <;> cases positive
      · congr 1
      · congr 1
      · congr 1
      · congr 1

/-- Every central weight is killed by the projection to `A₆`. -/
@[simp]
theorem alternatingSixSchurProjection_weight
    (weight : Fin 4 → ℤ) :
    alternatingSixSchurProjection
        (alternatingSixSchurWeight weight) = 1 := by
  simp [alternatingSixSchurWeight,
    alternatingSixSchurWeightAdditive,
    alternatingSixSchurCentralK,
    alternatingSixSchurProjection_k]

/-- The ordinary 360-word table is bijective, not merely surjective. -/
theorem alternatingSixRewriteNormalElement_bijective :
    Function.Bijective
      alternatingSixRewriteNormalElement := by
  apply
    (Nat.bijective_iff_surjective_and_card
      alternatingSixRewriteNormalElement).mpr
  refine
    ⟨alternatingSixRewriteNormalElement_surjective, ?_⟩
  rw [Nat.card_fin,
    Nat.card_congr
      alternatingSixPresentedGroupEquivAlternatingSix.toEquiv,
    natCard_alternatingSix]

/-- The ordinary 360-word table has no duplicate entries. -/
theorem alternatingSixRewriteNormalElement_injective :
    Function.Injective
      alternatingSixRewriteNormalElement :=
  alternatingSixRewriteNormalElement_bijective.1

/-- The projection kernel of the Schur presentation is central. -/
theorem alternatingSixSchurProjection_ker_le_center :
    alternatingSixSchurProjection.ker ≤
      Subgroup.center AlternatingSixSchurPresentedGroup := by
  intro g hg
  obtain ⟨i, weight, hi⟩ :=
    alternatingSixSchurPresented_exists_weightedNormalForm g
  have hnormalProjection :
      alternatingSixSchurProjection
          (alternatingSixSchurNormalElement i) = 1 := by
    rw [MonoidHom.mem_ker, hi, map_mul,
      alternatingSixSchurProjection_weight,
      mul_one] at hg
    exact hg
  have hpresentation :
      alternatingSixRewriteNormalElement i = 1 := by
    apply
      alternatingSixPresentationToAlternatingSix_bijective.1
    simpa [alternatingSixSchurNormalElement,
      alternatingSixRewriteNormalElement,
      alternatingSixSchurProjection_word] using
        hnormalProjection
  have hi0 : i = 0 := by
    apply alternatingSixRewriteNormalElement_injective
    exact hpresentation.trans (by rfl)
  subst i
  have hnormalZero :
      alternatingSixSchurNormalElement 0 = 1 := by
    rfl
  rw [hnormalZero, one_mul] at hi
  rw [hi]
  exact alternatingSixSchurWeight_mem_center weight

/-- The explicit projection is a central extension of `A₆`. -/
def alternatingSixSchurCentralExtension :
    CentralExtension
      AlternatingSixSchurPresentedGroup AlternatingSix where
  projection := alternatingSixSchurProjection
  surjective := alternatingSixSchurProjection_surjective
  ker_le_center := alternatingSixSchurProjection_ker_le_center

/-- The kernel of the explicit central extension has order at most six. -/
theorem natCard_alternatingSixSchurProjection_ker_le :
    Nat.card alternatingSixSchurProjection.ker ≤ 6 := by
  have hrange :
      alternatingSixSchurProjection.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      alternatingSixSchurProjection_surjective
  have hproduct :
      Nat.card alternatingSixSchurProjection.ker * 360 =
        Nat.card AlternatingSixSchurPresentedGroup := by
    calc
      Nat.card alternatingSixSchurProjection.ker * 360 =
          Nat.card alternatingSixSchurProjection.ker *
            Nat.card alternatingSixSchurProjection.range := by
              rw [hrange, Subgroup.card_top,
                natCard_alternatingSix]
      _ =
          Nat.card alternatingSixSchurProjection.ker *
            alternatingSixSchurProjection.ker.index := by
              rw [Subgroup.index_ker]
      _ = Nat.card AlternatingSixSchurPresentedGroup :=
        alternatingSixSchurProjection.ker.card_mul_index
  have hmul :
      Nat.card alternatingSixSchurProjection.ker * 360 ≤
        2160 := by
    rw [hproduct]
    exact natCard_alternatingSixSchurPresentedGroup_le
  apply Nat.le_of_mul_le_mul_right
    (c := 360)
  · simpa using hmul
  · norm_num

end GroupTheory
end McKayConjecture
