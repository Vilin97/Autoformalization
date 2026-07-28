/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientConcreteLocalRowIndexData
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientRowIndexBridge

/-!
# A central-block-compatible row matching for the five-local `A₆` table

The center of `6.A₆` has six possible scalar characters.  On the concrete
five-normalizer model `C₃ × (C₅ ⋊ C₄)`, these are determined by the
`C₃` row and by the sign of the central involution in the dicyclic factor.
This file records that six-block decomposition and chooses an explicit
four-by-four matching inside each block.

The matching is substantially more structured than an arbitrary
cardinality equivalence: it preserves the advertised central block
constructor by constructor.  It is nevertheless only a candidate
five-local McKay matching until the ambient character enumeration and the
genuine Sylow-stabilizer action have been proved to induce the corresponding
row permutations.  No equivariance or projective-factor compatibility is
claimed here.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Whether the central involution in the dicyclic factor acts by `-1` on
the indicated concrete character row.

For a linear row `j`, its value is `(-1)^j`.  For the two-dimensional row
`k`, whose tenth-root parameter has exponent `k + 1`, its value is
`(-1)^(k+1)`. -/
def alternatingSixFiveDicyclicCentralIsNegative :
    CyclicFiveInversionSemidirect.CharacterRow → Bool
  | .linear j => ![false, true, false, true] j
  | .twoDimensional k => ![true, false, true, false] k

/-- The six central-scalar blocks on the concrete five-normalizer rows.

The order-three convention accounts for evaluation at the element `2` of
the cyclic-three factor.  Thus index `1` contributes the square of
`CyclicThree.primitiveThirdRoot`, called `orderThreePositive` in the
ambient matrix corpus, while index `2` contributes the primitive root
itself, called `orderThreeNegative`.  Multiplying by the negative
dicyclic central sign gives the corresponding order-six blocks. -/
def alternatingSixFiveConcreteNormalizerCentralBlock
    (r : AlternatingSixFiveConcreteNormalizerRow) :
    AlternatingSixAmbientScalarPattern :=
  if alternatingSixFiveDicyclicCentralIsNegative r.2 then
    ![.orderTwo, .orderSixPositive, .orderSixNegative] r.1
  else
    ![.trivial, .orderThreePositive, .orderThreeNegative] r.1

/-- An explicit within-central-block candidate matching from the legacy
twenty-four ambient row index to the proved concrete normalizer table.

Inside each central block, fixed rows are paired with linear local rows and
the visible ambient pairs are paired with the corresponding
two-dimensional (or paired linear) local rows.  Later automorphism-table
files must prove that these choices intertwine the genuine stabilizer
actions. -/
def alternatingSixFiveCentralBlockRowEquiv :
    AlternatingSixFiveAmbientRow ≃
      AlternatingSixFiveConcreteNormalizerRow :=
  Equiv.ofBijective
    (fun r =>
      match r with
      | .row01 =>
          (0, CyclicFiveInversionSemidirect.CharacterRow.linear 0)
      | .row02 =>
          (1, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 1)
      | .row03 =>
          (1, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 3)
      | .row04 =>
          (2, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 1)
      | .row05 =>
          (2, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 3)
      | .row06 =>
          (0, CyclicFiveInversionSemidirect.CharacterRow.linear 1)
      | .row07 =>
          (0, CyclicFiveInversionSemidirect.CharacterRow.linear 3)
      | .row10 =>
          (1, CyclicFiveInversionSemidirect.CharacterRow.linear 0)
      | .row11 =>
          (2, CyclicFiveInversionSemidirect.CharacterRow.linear 0)
      | .row12 =>
          (1, CyclicFiveInversionSemidirect.CharacterRow.linear 1)
      | .row13 =>
          (1, CyclicFiveInversionSemidirect.CharacterRow.linear 3)
      | .row14 =>
          (2, CyclicFiveInversionSemidirect.CharacterRow.linear 1)
      | .row15 =>
          (2, CyclicFiveInversionSemidirect.CharacterRow.linear 3)
      | .row16 =>
          (0, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 1)
      | .row17 =>
          (0, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 3)
      | .row18 =>
          (0, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 0)
      | .row19 =>
          (0, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 2)
      | .row20 =>
          (0, CyclicFiveInversionSemidirect.CharacterRow.linear 2)
      | .row21 =>
          (1, CyclicFiveInversionSemidirect.CharacterRow.linear 2)
      | .row22 =>
          (2, CyclicFiveInversionSemidirect.CharacterRow.linear 2)
      | .atlasTwelveOne =>
          (1, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 0)
      | .atlasTwelveTwo =>
          (2, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 0)
      | .atlasTwelveSeven =>
          (1, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 2)
      | .atlasTwelveEleven =>
          (2, CyclicFiveInversionSemidirect.CharacterRow.twoDimensional 2))
    (by decide)

/-- The explicit candidate matching preserves all six central blocks. -/
@[simp]
theorem alternatingSixFiveCentralBlockRowEquiv_preserves_centralBlock
    (r : AlternatingSixFiveAmbientRow) :
    alternatingSixFiveConcreteNormalizerCentralBlock
        (alternatingSixFiveCentralBlockRowEquiv r) =
      r.toAmbientRowIndex.scalarPattern := by
  cases r <;> rfl

/-- The same central-block-compatible candidate matching, with its ambient
side written as the arithmetic prime-to-five subtype of the consolidated
thirty-one-row corpus. -/
def alternatingSixAmbientFivePPrimeCentralBlockRowEquiv :
    AlternatingSixAmbientPPrimeRowIndex 5 ≃
      AlternatingSixFiveConcreteNormalizerRow :=
  alternatingSixFiveAmbientRowEquivPPrimeRowIndex.symm.trans
    alternatingSixFiveCentralBlockRowEquiv

/-- The arithmetic-subtype form of the candidate matching still preserves
the central block. -/
@[simp]
theorem
    alternatingSixAmbientFivePPrimeCentralBlockRowEquiv_preserves_centralBlock
    (r : AlternatingSixAmbientPPrimeRowIndex 5) :
    alternatingSixFiveConcreteNormalizerCentralBlock
        (alternatingSixAmbientFivePPrimeCentralBlockRowEquiv r) =
      r.1.scalarPattern := by
  rw [alternatingSixAmbientFivePPrimeCentralBlockRowEquiv,
    Equiv.trans_apply,
    alternatingSixFiveCentralBlockRowEquiv_preserves_centralBlock]
  have hval :=
    alternatingSixFiveAmbientRowEquivPPrimeRowIndex_val
      (alternatingSixFiveAmbientRowEquivPPrimeRowIndex.symm r)
  have hval' :
      r.1 =
        AlternatingSixFiveAmbientRow.toAmbientRowIndex
          (alternatingSixFiveAmbientRowEquivPPrimeRowIndex.symm r) := by
    simpa using hval
  exact congrArg AlternatingSixAmbientOrdinaryRow.scalarPattern hval'.symm

end InductiveMcKay
end McKayConjecture
