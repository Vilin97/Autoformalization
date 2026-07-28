/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientPPrimeRowIndexData
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientRows

/-!
# Bridge between the two ambient five-row index conventions

The older five-local matrix files use the dedicated type
`AlternatingSixFiveAmbientRow`.  The consolidated ambient corpus uses the
arithmetic subtype `AlternatingSixAmbientPPrimeRowIndex 5`.  This file
identifies the two conventions constructor by constructor.

The bridge concerns row names and dimensions only.  It makes no
irreducibility, character-completeness, equivariance, or projective claim.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

namespace AlternatingSixFiveAmbientRow

/-- The corresponding row name in the consolidated thirty-one-row
ambient corpus. -/
def toAmbientRowIndex :
    AlternatingSixFiveAmbientRow → AlternatingSixAmbientRowIndex
  | .row01 => .row01
  | .row02 => .row02
  | .row03 => .row03
  | .row04 => .row04
  | .row05 => .row05
  | .row06 => .row06
  | .row07 => .row07
  | .row10 => .row10
  | .row11 => .row11
  | .row12 => .row12
  | .row13 => .row13
  | .row14 => .row14
  | .row15 => .row15
  | .row16 => .row16
  | .row17 => .row17
  | .row18 => .row18
  | .row19 => .row19
  | .row20 => .row20
  | .row21 => .row21
  | .row22 => .row22
  | .atlasTwelveOne => .atlasTwelvePowerOne
  | .atlasTwelveTwo => .atlasTwelvePowerTwo
  | .atlasTwelveSeven => .atlasTwelvePowerSeven
  | .atlasTwelveEleven => .atlasTwelvePowerEleven

@[simp]
theorem toAmbientRowIndex_dimension
    (r : AlternatingSixFiveAmbientRow) :
    r.toAmbientRowIndex.dimension = r.dimension := by
  cases r <;> rfl

end AlternatingSixFiveAmbientRow

/-- Constructor-preserving equivalence from the legacy five-local row
index to the consolidated arithmetic prime-to-five subtype. -/
def alternatingSixFiveAmbientRowEquivPPrimeRowIndex :
    AlternatingSixFiveAmbientRow ≃
      AlternatingSixAmbientPPrimeRowIndex 5 :=
  AlternatingSixFiveAmbientRow.equivFin.trans
    alternatingSixAmbientFivePPrimeRowIndexEquiv

@[simp]
theorem alternatingSixFiveAmbientRowEquivPPrimeRowIndex_val
    (r : AlternatingSixFiveAmbientRow) :
    (alternatingSixFiveAmbientRowEquivPPrimeRowIndex r).1 =
      r.toAmbientRowIndex := by
  cases r <;> rfl

end InductiveMcKay
end McKayConjecture
