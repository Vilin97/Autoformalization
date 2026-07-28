/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverClassCounts
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyClasses

/-!
# Class sizes in the sixfold cover of `A₆`

The conjugacy certificate labels every one of the `360 × 6` coordinates.
This module checks that each label fiber has the advertised size.  Keeping
this finite computation separate lets character-norm proofs work with the
thirty-one class representatives rather than expand a sum over all 2160
group elements.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

/-- The finite coordinate fiber carrying one checked conjugacy-class label. -/
abbrev AlternatingSixSchurClassFiber (i : Fin 31) :=
  {g : AlternatingSixSchurCoordinates //
    alternatingSixSchurClassIndex g = i}

/-- Split coordinates into a ten-state block, an offset, and a central
coordinate. -/
def alternatingSixSchurClassCountCoordinatesEquiv :
    AlternatingSixSchurCoordinates ≃
      Fin 36 × (Fin 10 × Fin 6) where
  toFun coordinate :=
    let splitState :=
      (finProdFinEquiv : Fin 36 × Fin 10 ≃ Fin 360).symm
        coordinate.state
    (splitState.1,
      (splitState.2, (ZMod.finEquiv 6).symm coordinate.central))
  invFun coordinate :=
    alternatingSixSchurClassCountBlockCoordinate
      coordinate.1 coordinate.2
  left_inv coordinate := by
    apply AlternatingSixSchurCoordinates.ext
    · exact
        (finProdFinEquiv : Fin 36 × Fin 10 ≃ Fin 360)
          |>.apply_symm_apply coordinate.state
    · exact (ZMod.finEquiv 6).apply_symm_apply coordinate.central
  right_inv coordinate := by
    rcases coordinate with ⟨block, offset, central⟩
    have hsplit :
        (finProdFinEquiv : Fin 36 × Fin 10 ≃ Fin 360).symm
            ((finProdFinEquiv : Fin 36 × Fin 10 ≃ Fin 360)
              (block, offset)) =
          (block, offset) :=
      (finProdFinEquiv : Fin 36 × Fin 10 ≃ Fin 360)
        |>.symm_apply_apply (block, offset)
    change
      (let splitState :=
          (finProdFinEquiv : Fin 36 × Fin 10 ≃ Fin 360).symm
            ((finProdFinEquiv : Fin 36 × Fin 10 ≃ Fin 360)
              (block, offset));
          (splitState.1,
            (splitState.2,
              (ZMod.finEquiv 6).symm ((ZMod.finEquiv 6) central)))) =
        (block, (offset, central))
    have hcentral :
        (ZMod.finEquiv 6).symm ((ZMod.finEquiv 6) central) = central :=
      (ZMod.finEquiv 6).symm_apply_apply central
    rw [hsplit, hcentral]

/-- Split a checked class fiber into its 36 ten-state blocks. -/
def alternatingSixSchurClassFiberBlockEquiv (i : Fin 31) :
    AlternatingSixSchurClassFiber i ≃
      Σ block : Fin 36,
        AlternatingSixSchurClassCountBlockFiber block i :=
  (alternatingSixSchurClassCountCoordinatesEquiv.subtypeEquiv
      (fun coordinate ↦ by
        change
          alternatingSixSchurClassIndex coordinate = i ↔
            alternatingSixSchurClassIndex
              (alternatingSixSchurClassCountCoordinatesEquiv.symm
                (alternatingSixSchurClassCountCoordinatesEquiv
                  coordinate)) = i
        rw [Equiv.symm_apply_apply])).trans
    (Equiv.subtypeProdEquivSigmaSubtype
      (fun block coordinate ↦
        alternatingSixSchurClassIndex
            (alternatingSixSchurClassCountBlockCoordinate
              block coordinate) = i))

/-- The checked label fiber has the advertised conjugacy-class size. -/
theorem alternatingSixSchurClassFiber_card (i : Fin 31) :
    Fintype.card (AlternatingSixSchurClassFiber i) =
      alternatingSixSchurClassSize i := by
  calc
    Fintype.card (AlternatingSixSchurClassFiber i) =
        Fintype.card
          (Σ block : Fin 36,
            AlternatingSixSchurClassCountBlockFiber block i) :=
      Fintype.card_congr
        (alternatingSixSchurClassFiberBlockEquiv i)
    _ = ∑ block : Fin 36,
          Fintype.card
            (AlternatingSixSchurClassCountBlockFiber block i) :=
      Fintype.card_sigma
    _ = ∑ block : Fin 36,
          alternatingSixSchurClassCountBlock block i := by
      apply Finset.sum_congr rfl
      intro block _
      exact alternatingSixSchurClassCountBlockFiber_card block i
    _ = alternatingSixSchurClassSize i :=
      alternatingSixSchurClassCountBlock_sum i

end GroupTheory
end McKayConjecture
