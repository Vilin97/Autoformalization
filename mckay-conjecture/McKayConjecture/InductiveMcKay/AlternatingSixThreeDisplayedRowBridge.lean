/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientPPrimeCharacterEnumeration
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientConcreteLocalRowIndexData

/-!
# Display-order bridge for the three-local `A₆` rows

The ambient arithmetic table and the proved actual three-normalizer table each
come with a twelve-row display order.  This file aligns equal display
positions.  The local order is the actual character-table order: its eight
linear rows precede its four degree-four rows.

This is an explicit and reproducible row-index equivalence, but display order
alone does **not** prove that it is a McKay character matching.  In fact no
ambient/local equivalence can preserve ordinary character degree: ambient
prime-to-three degrees include `5`, `8`, and `10`, whereas every local
prime-to-three degree is `1` or `4`.  The obstruction is proved below so that
this combinatorial bridge cannot accidentally be promoted to a
degree-preserving claim.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- Align the existing ambient and actual-normalizer display orders.

This definition records an explicit indexing convention, not a proved McKay
matching. -/
def alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv :
    AlternatingSixAmbientPPrimeRowIndex 3 ≃
      AlternatingSixThreeConcreteNormalizerRow :=
  alternatingSixAmbientThreePPrimeRowIndexEquiv.symm.trans
    alternatingSixThreeConcreteNormalizerRowIndexEquiv

@[simp]
theorem alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered
    (i : Fin 12) :
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
        (alternatingSixAmbientThreePPrimeRowIndexEquiv i) =
      alternatingSixThreeConcreteNormalizerRowIndexEquiv i := by
  simp [alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv]

/-- The display-order bridge is the unique equivalence carrying every
ambient displayed position to the same local displayed position.  This is
canonicity relative to the two recorded orders, not canonicity as a McKay
character correspondence. -/
theorem alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_unique
    (e :
      AlternatingSixAmbientPPrimeRowIndex 3 ≃
        AlternatingSixThreeConcreteNormalizerRow)
    (h :
      ∀ i : Fin 12,
        e (alternatingSixAmbientThreePPrimeRowIndexEquiv i) =
          alternatingSixThreeConcreteNormalizerRowIndexEquiv i) :
    e = alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv := by
  apply Equiv.ext
  intro r
  let i : Fin 12 :=
    alternatingSixAmbientThreePPrimeRowIndexEquiv.symm r
  have hir :
      alternatingSixAmbientThreePPrimeRowIndexEquiv i = r :=
    alternatingSixAmbientThreePPrimeRowIndexEquiv.apply_symm_apply r
  rw [← hir]
  exact
    (h i).trans
      (alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered i).symm

@[simp]
theorem alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_row01 :
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
        ⟨.row01, by decide⟩ =
      Sum.inl 0 := by
  simpa [alternatingSixAmbientThreePPrimeRowIndexEquiv,
    alternatingSixThreeConcreteNormalizerRowIndexEquiv] using
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered
      (0 : Fin 12)

@[simp]
theorem alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_row06 :
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
        ⟨.row06, by decide⟩ =
      Sum.inl 1 := by
  simpa [alternatingSixAmbientThreePPrimeRowIndexEquiv,
    alternatingSixThreeConcreteNormalizerRowIndexEquiv] using
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered
      (1 : Fin 12)

@[simp]
theorem alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_row07 :
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
        ⟨.row07, by decide⟩ =
      Sum.inl 2 := by
  simpa [alternatingSixAmbientThreePPrimeRowIndexEquiv,
    alternatingSixThreeConcreteNormalizerRowIndexEquiv] using
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered
      (2 : Fin 12)

@[simp]
theorem alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_row08 :
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
        ⟨.row08, by decide⟩ =
      Sum.inl 3 := by
  simpa [alternatingSixAmbientThreePPrimeRowIndexEquiv,
    alternatingSixThreeConcreteNormalizerRowIndexEquiv] using
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered
      (3 : Fin 12)

@[simp]
theorem alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_row09 :
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
        ⟨.row09, by decide⟩ =
      Sum.inl 4 := by
  simpa [alternatingSixAmbientThreePPrimeRowIndexEquiv,
    alternatingSixThreeConcreteNormalizerRowIndexEquiv] using
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered
      (4 : Fin 12)

@[simp]
theorem alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_row16 :
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
        ⟨.row16, by decide⟩ =
      Sum.inl 5 := by
  simpa [alternatingSixAmbientThreePPrimeRowIndexEquiv,
    alternatingSixThreeConcreteNormalizerRowIndexEquiv] using
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered
      (5 : Fin 12)

@[simp]
theorem alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_row17 :
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
        ⟨.row17, by decide⟩ =
      Sum.inl 6 := by
  simpa [alternatingSixAmbientThreePPrimeRowIndexEquiv,
    alternatingSixThreeConcreteNormalizerRowIndexEquiv] using
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered
      (6 : Fin 12)

@[simp]
theorem alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_row18 :
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
        ⟨.row18, by decide⟩ =
      Sum.inl 7 := by
  simpa [alternatingSixAmbientThreePPrimeRowIndexEquiv,
    alternatingSixThreeConcreteNormalizerRowIndexEquiv] using
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered
      (7 : Fin 12)

@[simp]
theorem alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_row19 :
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
        ⟨.row19, by decide⟩ =
      Sum.inr (0, 0) := by
  simpa [alternatingSixAmbientThreePPrimeRowIndexEquiv,
    alternatingSixThreeConcreteNormalizerRowIndexEquiv] using
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered
      (8 : Fin 12)

@[simp]
theorem alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_row23 :
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
        ⟨.row23, by decide⟩ =
      Sum.inr (0, 1) := by
  simpa [alternatingSixAmbientThreePPrimeRowIndexEquiv,
    alternatingSixThreeConcreteNormalizerRowIndexEquiv] using
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered
      (9 : Fin 12)

@[simp]
theorem alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_row24 :
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
        ⟨.row24, by decide⟩ =
      Sum.inr (1, 0) := by
  simpa [alternatingSixAmbientThreePPrimeRowIndexEquiv,
    alternatingSixThreeConcreteNormalizerRowIndexEquiv] using
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered
      (10 : Fin 12)

@[simp]
theorem alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_row25 :
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
        ⟨.row25, by decide⟩ =
      Sum.inr (1, 1) := by
  simpa [alternatingSixAmbientThreePPrimeRowIndexEquiv,
    alternatingSixThreeConcreteNormalizerRowIndexEquiv] using
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered
      (11 : Fin 12)

/-- The proved actual-normalizer character enumeration, indexed through
the displayed ambient row positions.  No equivariance or projective
compatibility is inferred from its definition. -/
def alternatingSixThreeDisplayedOrderActualLocalCharacterEnumeration :
    AlternatingSixAmbientPPrimeRowIndex 3 ≃
      PPrimeIrreducibleCharacter
        AlternatingSixUniversalCoverThreeNormalizer 3 :=
  alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv.trans
    AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv

@[simp]
theorem alternatingSixThreeDisplayedOrderActualLocalCharacterEnumeration_apply
    (r : AlternatingSixAmbientPPrimeRowIndex 3) :
    alternatingSixThreeDisplayedOrderActualLocalCharacterEnumeration r =
      AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
          (alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv r) :=
  rfl

@[simp]
theorem alternatingSixThreeDisplayedOrderActualLocalCharacterEnumeration_ordered
    (i : Fin 12) :
    alternatingSixThreeDisplayedOrderActualLocalCharacterEnumeration
        (alternatingSixAmbientThreePPrimeRowIndexEquiv i) =
      AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
          (alternatingSixThreeConcreteNormalizerRowIndexEquiv i) := by
  simp [alternatingSixThreeDisplayedOrderActualLocalCharacterEnumeration]

/-- Degree of the actual-normalizer character represented by a concrete
local row. -/
def alternatingSixThreeConcreteNormalizerRowDegree
    (r : AlternatingSixThreeConcreteNormalizerRow) : ℕ :=
  (AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
      r).1.degree

@[simp]
theorem alternatingSixThreeConcreteNormalizerRowDegree_linear
    (j : Fin 8) :
    alternatingSixThreeConcreteNormalizerRowDegree (Sum.inl j) = 1 := by
  rw [alternatingSixThreeConcreteNormalizerRowDegree,
    AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv_degree]
  exact
    AlternatingSixThreeNormalizer.coordinateLinearCharacter_degree j

@[simp]
theorem alternatingSixThreeConcreteNormalizerRowDegree_four
    (r : Fin 2 × Fin 2) :
    alternatingSixThreeConcreteNormalizerRowDegree (Sum.inr r) = 4 := by
  rw [alternatingSixThreeConcreteNormalizerRowDegree,
    AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv_degree]
  exact
    AlternatingSixThreeNormalizer.degreeFourCharacter_degree r.1 r.2

/-- The degree list of the ambient prime-to-three rows in the recorded
display order. -/
theorem alternatingSixThreeDisplayedAmbientDegree
    (i : Fin 12) :
    (alternatingSixAmbientThreePPrimeRowIndexEquiv i).1.dimension =
      ![1, 4, 4, 5, 5, 8, 8, 8, 8, 10, 10, 10] i := by
  fin_cases i <;> rfl

/-- The degree list of the actual local prime-to-three characters in their
proved table order. -/
theorem alternatingSixThreeDisplayedLocalDegree
    (i : Fin 12) :
    alternatingSixThreeConcreteNormalizerRowDegree
        (alternatingSixThreeConcreteNormalizerRowIndexEquiv i) =
      ![1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4] i := by
  fin_cases i <;>
    simp [alternatingSixThreeConcreteNormalizerRowIndexEquiv]

/-- No bijection between these row sets can preserve ordinary character
degree.  The ambient degree-five row already gives an obstruction because
all local prime-to-three degrees are one or four. -/
theorem no_alternatingSixThreeAmbientLocalRowEquiv_preserves_degree
    (e :
      AlternatingSixAmbientPPrimeRowIndex 3 ≃
        AlternatingSixThreeConcreteNormalizerRow) :
    ¬ ∀ r,
        r.1.dimension =
          alternatingSixThreeConcreteNormalizerRowDegree (e r) := by
  intro h
  let r :
      AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row08, by decide⟩
  have hr := h r
  rcases he : e r with j | q
  · rw [he,
      alternatingSixThreeConcreteNormalizerRowDegree_linear] at hr
    norm_num [r, AlternatingSixAmbientOrdinaryRow.dimension] at hr
  · rw [he,
      alternatingSixThreeConcreteNormalizerRowDegree_four] at hr
    norm_num [r, AlternatingSixAmbientOrdinaryRow.dimension] at hr

end InductiveMcKay
end McKayConjecture
