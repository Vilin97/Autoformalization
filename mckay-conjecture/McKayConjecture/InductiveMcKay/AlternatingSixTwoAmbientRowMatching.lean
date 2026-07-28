/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientConcreteLocalRowIndexData
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientPPrimeRowIndexData

/-!
# A central-block ordering of the two-local `6.A₆` rows

The twelve odd-dimensional rows in the generated ambient table split into
three four-row blocks according to their recorded order-three central-scalar
pattern.  The concrete normalizer table is indexed by
`Fin 3 × (Fin 2 × Fin 2)`: its first coordinate is the cyclic-three
character and its last two coordinates enumerate the four linear
quaternion characters.

This file aligns those two *row orders*.  Unlike the arbitrary cardinality
alignment, the first coordinate of the local row records the ambient
central-scalar block, and the ordinary table order is retained inside each
block.

The construction is deliberately called a row-order matching rather than a
McKay correspondence.  The present normalizer equivalence chooses an
abstract isomorphism from `C₃` to the central complement, so identifying the
three block labels with actual central-character values still needs a
generator-normalized comparison.  Stabilizer equivariance and projective
factor compatibility are also not asserted here.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- The central-block order of the twelve odd-dimensional ambient rows:
the four trivial-central rows, the four positive order-three rows, and the
four negative order-three rows. -/
def alternatingSixAmbientTwoCentralBlockIndex
    (r : AlternatingSixAmbientPPrimeRowIndex 2) : Fin 12 :=
  match r.1 with
  | .row01 => 0
  | .row08 => 1
  | .row09 => 2
  | .row20 => 3
  | .row02 => 4
  | .row03 => 5
  | .row21 => 6
  | .row30 => 7
  | .row04 => 8
  | .row05 => 9
  | .row22 => 10
  | .row31 => 11
  | _ => 0

/-- The central-block order is a complete enumeration of the arithmetic
odd-dimensional ambient row subtype. -/
def alternatingSixAmbientTwoCentralBlockIndexEquiv :
    AlternatingSixAmbientPPrimeRowIndex 2 ≃ Fin 12 where
  toFun := alternatingSixAmbientTwoCentralBlockIndex
  invFun :=
    ![⟨.row01, by decide⟩,
      ⟨.row08, by decide⟩,
      ⟨.row09, by decide⟩,
      ⟨.row20, by decide⟩,
      ⟨.row02, by decide⟩,
      ⟨.row03, by decide⟩,
      ⟨.row21, by decide⟩,
      ⟨.row30, by decide⟩,
      ⟨.row04, by decide⟩,
      ⟨.row05, by decide⟩,
      ⟨.row22, by decide⟩,
      ⟨.row31, by decide⟩]
  left_inv := by
    rintro ⟨r, hr⟩
    apply Subtype.ext
    cases r <;>
      norm_num [AlternatingSixAmbientOrdinaryRow.dimension] at hr <;>
      rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-- Arithmetic lexicographic index of a concrete row
`(cyclic-three coordinate, quaternion sign pair)`. -/
def alternatingSixTwoConcreteNormalizerRowLexIndexEquiv :
    AlternatingSixTwoConcreteNormalizerRow ≃ Fin 12 :=
  (Equiv.prodCongr (Equiv.refl (Fin 3)) finProdFinEquiv).trans
    finProdFinEquiv

/-- Explicit central-block row-order matching between the arithmetic
ambient odd rows and the concrete normalizer rows.

This is a candidate finite row matching.  It is not yet an equivariant
McKay character correspondence. -/
def alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow :
    AlternatingSixAmbientPPrimeRowIndex 2 ≃
      AlternatingSixTwoConcreteNormalizerRow :=
  alternatingSixAmbientTwoCentralBlockIndexEquiv.trans
    alternatingSixTwoConcreteNormalizerRowLexIndexEquiv.symm

/-! ### Forward computation rules -/

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row01 :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        ⟨.row01, by decide⟩ =
      (0, (0, 0)) := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row08 :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        ⟨.row08, by decide⟩ =
      (0, (0, 1)) := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row09 :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        ⟨.row09, by decide⟩ =
      (0, (1, 0)) := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row20 :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        ⟨.row20, by decide⟩ =
      (0, (1, 1)) := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row02 :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        ⟨.row02, by decide⟩ =
      (1, (0, 0)) := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row03 :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        ⟨.row03, by decide⟩ =
      (1, (0, 1)) := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row21 :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        ⟨.row21, by decide⟩ =
      (1, (1, 0)) := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row30 :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        ⟨.row30, by decide⟩ =
      (1, (1, 1)) := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row04 :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        ⟨.row04, by decide⟩ =
      (2, (0, 0)) := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row05 :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        ⟨.row05, by decide⟩ =
      (2, (0, 1)) := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row22 :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        ⟨.row22, by decide⟩ =
      (2, (1, 0)) := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row31 :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        ⟨.row31, by decide⟩ =
      (2, (1, 1)) := by
  rfl

/-! ### Reverse computation rules -/

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_symm_zero_zero_zero :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow.symm
        (0, (0, 0)) =
      ⟨.row01, by decide⟩ := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_symm_zero_zero_one :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow.symm
        (0, (0, 1)) =
      ⟨.row08, by decide⟩ := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_symm_zero_one_zero :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow.symm
        (0, (1, 0)) =
      ⟨.row09, by decide⟩ := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_symm_zero_one_one :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow.symm
        (0, (1, 1)) =
      ⟨.row20, by decide⟩ := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_symm_one_zero_zero :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow.symm
        (1, (0, 0)) =
      ⟨.row02, by decide⟩ := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_symm_one_zero_one :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow.symm
        (1, (0, 1)) =
      ⟨.row03, by decide⟩ := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_symm_one_one_zero :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow.symm
        (1, (1, 0)) =
      ⟨.row21, by decide⟩ := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_symm_one_one_one :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow.symm
        (1, (1, 1)) =
      ⟨.row30, by decide⟩ := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_symm_two_zero_zero :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow.symm
        (2, (0, 0)) =
      ⟨.row04, by decide⟩ := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_symm_two_zero_one :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow.symm
        (2, (0, 1)) =
      ⟨.row05, by decide⟩ := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_symm_two_one_zero :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow.symm
        (2, (1, 0)) =
      ⟨.row22, by decide⟩ := by
  rfl

@[simp] theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_symm_two_one_one :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow.symm
        (2, (1, 1)) =
      ⟨.row31, by decide⟩ := by
  rfl

/-! ### Invariants visible before character-level equivariance -/

/-- The three central-block labels attached to the six scalar patterns.
Only the first three cases occur on odd-dimensional ambient rows. -/
def alternatingSixTwoScalarPatternBlock :
    AlternatingSixAmbientScalarPattern → Fin 3
  | .trivial => 0
  | .orderThreePositive => 1
  | .orderThreeNegative => 2
  | .orderTwo => 0
  | .orderSixPositive => 1
  | .orderSixNegative => 2

/-- The proposed local row's cyclic-three coordinate is exactly the
central-scalar block recorded on the ambient row.  This is a statement
about the two explicit row orders, not yet an equality of central character
values in the actual normalizer. -/
theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_fst
    (r : AlternatingSixAmbientPPrimeRowIndex 2) :
    (alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow r).1 =
      alternatingSixTwoScalarPatternBlock r.1.scalarPattern := by
  rcases r with ⟨r, hr⟩
  cases r with
  | row01 =>
      simpa [AlternatingSixAmbientOrdinaryRow.scalarPattern,
        alternatingSixTwoScalarPatternBlock] using
        congrArg Prod.fst
          alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row01
  | row02 =>
      simpa [AlternatingSixAmbientOrdinaryRow.scalarPattern,
        alternatingSixTwoScalarPatternBlock] using
        congrArg Prod.fst
          alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row02
  | row03 =>
      simpa [AlternatingSixAmbientOrdinaryRow.scalarPattern,
        alternatingSixTwoScalarPatternBlock] using
        congrArg Prod.fst
          alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row03
  | row04 =>
      simpa [AlternatingSixAmbientOrdinaryRow.scalarPattern,
        alternatingSixTwoScalarPatternBlock] using
        congrArg Prod.fst
          alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row04
  | row05 =>
      simpa [AlternatingSixAmbientOrdinaryRow.scalarPattern,
        alternatingSixTwoScalarPatternBlock] using
        congrArg Prod.fst
          alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row05
  | row08 =>
      simpa [AlternatingSixAmbientOrdinaryRow.scalarPattern,
        alternatingSixTwoScalarPatternBlock] using
        congrArg Prod.fst
          alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row08
  | row09 =>
      simpa [AlternatingSixAmbientOrdinaryRow.scalarPattern,
        alternatingSixTwoScalarPatternBlock] using
        congrArg Prod.fst
          alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row09
  | row20 =>
      simpa [AlternatingSixAmbientOrdinaryRow.scalarPattern,
        alternatingSixTwoScalarPatternBlock] using
        congrArg Prod.fst
          alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row20
  | row21 =>
      simpa [AlternatingSixAmbientOrdinaryRow.scalarPattern,
        alternatingSixTwoScalarPatternBlock] using
        congrArg Prod.fst
          alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row21
  | row22 =>
      simpa [AlternatingSixAmbientOrdinaryRow.scalarPattern,
        alternatingSixTwoScalarPatternBlock] using
        congrArg Prod.fst
          alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row22
  | row30 =>
      simpa [AlternatingSixAmbientOrdinaryRow.scalarPattern,
        alternatingSixTwoScalarPatternBlock] using
        congrArg Prod.fst
          alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row30
  | row31 =>
      simpa [AlternatingSixAmbientOrdinaryRow.scalarPattern,
        alternatingSixTwoScalarPatternBlock] using
        congrArg Prod.fst
          alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row31
  | row06 | row07 | row10 | row11 | row12 | row13 | row14 | row15
  | row16 | row17 | row18 | row19 | row23 | row24 | row25
  | atlasTwelvePowerOne | atlasTwelvePowerTwo
  | atlasTwelvePowerSeven | atlasTwelvePowerEleven =>
      norm_num [AlternatingSixAmbientOrdinaryRow.dimension] at hr

/-- Every matched concrete normalizer row has degree one. -/
@[simp]
theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_local_degree
    (r : AlternatingSixAmbientPPrimeRowIndex 2) :
    (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv
      (alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        r)).1.degree = 1 :=
  alternatingSixTwoActualNormalizerPPrimeCharacterEquiv_degree _

/-- Ambient dimensions and matched local degrees have the same parity, as
both are odd.  Literal degree equality is false for every nontrivial ambient
row because all twelve local rows are linear. -/
theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_degree_mod_two
    (r : AlternatingSixAmbientPPrimeRowIndex 2) :
    r.1.dimension % 2 =
      (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv
        (alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
          r)).1.degree % 2 := by
  rw [
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_local_degree]
  have hodd := r.2
  omega

/-- A concrete check recording why this row matching must not be advertised
as degree preserving in the literal sense. -/
theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row02_degree_ne :
    AlternatingSixAmbientOrdinaryRow.dimension .row02 ≠
      (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv
        (alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
          ⟨.row02, by decide⟩)).1.degree := by
  simp [AlternatingSixAmbientOrdinaryRow.dimension]

end InductiveMcKay
end McKayConjecture
