/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterClassActionData

/-!
# Checked class action of the second outer automorphism

The homomorphism property reduces each representative to one of seven base
words and an inverted central coordinate.  The final class labels are
exhaustively checked against the finite conjugacy certificate.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- `alpha2` carries every source base word to the same word in its two
audited generator images. -/
theorem alternatingSixSchurAlphaTwoEndomorphism_outerClassBaseImage
    (base : Fin 7) :
    alternatingSixSchurAlphaTwoEndomorphism
        (alternatingSixSchurOuterClassBaseImage
          alternatingSixSchurOuterClassSourceA
          alternatingSixSchurOuterClassSourceB base) =
      alternatingSixSchurOuterClassBaseImage
        (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
        (alternatingSixSchurAlphaTwoGeneratorCoordinates 1)
        base := by
  fin_cases base <;>
    simp [alternatingSixSchurOuterClassBaseImage,
      alternatingSixSchurOuterClassSourceA,
      alternatingSixSchurOuterClassSourceB,
      alternatingSixSchurAlphaTwoEndomorphism_generator]

/-- `alpha2` negates every central coordinate. -/
theorem alternatingSixSchurAlphaTwoEndomorphism_central
    (central : Fin 6) :
    alternatingSixSchurAlphaTwoEndomorphism
        (alternatingSixSchurAuditedCoordinate 0
          (ZMod.finEquiv 6 central)) =
      alternatingSixSchurAuditedCoordinate 0
        (-(ZMod.finEquiv 6 central)) := by
  apply alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
  simp [alternatingSixSchurAlphaTwoGeneratorCoordinates,
    alternatingSixSchurAuditedCoordinate]

/-- Exact coordinate image of every checked representative under `alpha2`. -/
theorem
    alternatingSixSchurAlphaTwoEndomorphism_classRepresentative_apply
    (index : Fin 31) :
    alternatingSixSchurAlphaTwoEndomorphism
        (alternatingSixSchurClassRepresentative index) =
      alternatingSixSchurAlphaTwoClassRepresentativeImage index := by
  rw [
    alternatingSixSchurClassRepresentative_eq_outerBase_mul_central,
    map_mul,
    alternatingSixSchurAlphaTwoEndomorphism_outerClassBaseImage,
    alternatingSixSchurAlphaTwoEndomorphism_central
  ]
  rfl

/-- The `ab²` base word in the second generator images. -/
private theorem alternatingSixSchurAlphaTwoOuterClassBaseImage_four :
    alternatingSixSchurOuterClassBaseImage
        (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
        (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) 4 =
      alternatingSixSchurAuditedCoordinate 175 3 := by
  change
    (alternatingSixSchurAuditedCoordinate 317 1 *
        alternatingSixSchurAuditedCoordinate 52 4) *
        alternatingSixSchurAuditedCoordinate 52 4 =
      alternatingSixSchurAuditedCoordinate 175 3
  rw [show
    alternatingSixSchurAuditedCoordinate 317 1 *
        alternatingSixSchurAuditedCoordinate 52 4 =
      alternatingSixSchurAuditedCoordinate 284 2 by decide]
  decide

/-- The first long base word in the second generator images, evaluated in
small checked multiplication steps. -/
private theorem alternatingSixSchurAlphaTwoOuterClassBaseImage_five :
    alternatingSixSchurOuterClassBaseImage
        (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
        (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) 5 =
      alternatingSixSchurAuditedCoordinate 242 1 := by
  change
    (((((alternatingSixSchurAuditedCoordinate 317 1 *
          alternatingSixSchurAuditedCoordinate 52 4) *
        alternatingSixSchurAuditedCoordinate 317 1) *
      alternatingSixSchurAuditedCoordinate 52 4) *
    alternatingSixSchurAuditedCoordinate 52 4) *
    alternatingSixSchurAuditedCoordinate 317 1) *
        (alternatingSixSchurAuditedCoordinate 52 4)⁻¹ =
      alternatingSixSchurAuditedCoordinate 242 1
  rw [show
    alternatingSixSchurAuditedCoordinate 317 1 *
        alternatingSixSchurAuditedCoordinate 52 4 =
      alternatingSixSchurAuditedCoordinate 284 2 by decide]
  rw [show
    alternatingSixSchurAuditedCoordinate 284 2 *
        alternatingSixSchurAuditedCoordinate 317 1 =
      alternatingSixSchurAuditedCoordinate 298 0 by decide]
  rw [show
    alternatingSixSchurAuditedCoordinate 298 0 *
        alternatingSixSchurAuditedCoordinate 52 4 =
      alternatingSixSchurAuditedCoordinate 182 1 by decide]
  rw [show
    alternatingSixSchurAuditedCoordinate 182 1 *
        alternatingSixSchurAuditedCoordinate 52 4 =
      alternatingSixSchurAuditedCoordinate 139 2 by decide]
  rw [show
    alternatingSixSchurAuditedCoordinate 139 2 *
        alternatingSixSchurAuditedCoordinate 317 1 =
      alternatingSixSchurAuditedCoordinate 281 0 by decide]
  rw [show
    (alternatingSixSchurAuditedCoordinate 52 4)⁻¹ =
      alternatingSixSchurAuditedCoordinate 60 5 by decide]
  decide

/-- The second long base word in the second generator images, evaluated in
small checked multiplication steps. -/
private theorem alternatingSixSchurAlphaTwoOuterClassBaseImage_six :
    alternatingSixSchurOuterClassBaseImage
        (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
        (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) 6 =
      alternatingSixSchurAuditedCoordinate 310 1 := by
  change
    (((((alternatingSixSchurAuditedCoordinate 317 1 *
          alternatingSixSchurAuditedCoordinate 52 4) *
        alternatingSixSchurAuditedCoordinate 317 1) *
      (alternatingSixSchurAuditedCoordinate 52 4)⁻¹) *
    alternatingSixSchurAuditedCoordinate 317 1) *
    alternatingSixSchurAuditedCoordinate 52 4) *
        alternatingSixSchurAuditedCoordinate 52 4 =
      alternatingSixSchurAuditedCoordinate 310 1
  rw [show
    alternatingSixSchurAuditedCoordinate 317 1 *
        alternatingSixSchurAuditedCoordinate 52 4 =
      alternatingSixSchurAuditedCoordinate 284 2 by decide]
  rw [show
    alternatingSixSchurAuditedCoordinate 284 2 *
        alternatingSixSchurAuditedCoordinate 317 1 =
      alternatingSixSchurAuditedCoordinate 298 0 by decide]
  rw [show
    (alternatingSixSchurAuditedCoordinate 52 4)⁻¹ =
      alternatingSixSchurAuditedCoordinate 60 5 by decide]
  rw [show
    alternatingSixSchurAuditedCoordinate 298 0 *
        alternatingSixSchurAuditedCoordinate 60 5 =
      alternatingSixSchurAuditedCoordinate 219 3 by decide]
  rw [show
    alternatingSixSchurAuditedCoordinate 219 3 *
        alternatingSixSchurAuditedCoordinate 317 1 =
      alternatingSixSchurAuditedCoordinate 7 0 by decide]
  rw [show
    alternatingSixSchurAuditedCoordinate 7 0 *
        alternatingSixSchurAuditedCoordinate 52 4 =
      alternatingSixSchurAuditedCoordinate 143 4 by decide]
  decide

/-- Checked images of the six central translates of the `ab²` base word. -/
private theorem alternatingSixSchurAlphaTwoClassRepresentativeImage_21 :
    alternatingSixSchurAlphaTwoClassRepresentativeImage 21 =
      alternatingSixSchurAuditedCoordinate 175 3 := by
  change
    alternatingSixSchurOuterClassBaseImage
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) 4 *
        alternatingSixSchurAuditedCoordinate 0 0 =
      alternatingSixSchurAuditedCoordinate 175 3
  rw [alternatingSixSchurAlphaTwoOuterClassBaseImage_four]
  decide

private theorem alternatingSixSchurAlphaTwoClassRepresentativeImage_22 :
    alternatingSixSchurAlphaTwoClassRepresentativeImage 22 =
      alternatingSixSchurAuditedCoordinate 175 2 := by
  change
    alternatingSixSchurOuterClassBaseImage
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) 4 *
        alternatingSixSchurAuditedCoordinate 0 (-1) =
      alternatingSixSchurAuditedCoordinate 175 2
  rw [alternatingSixSchurAlphaTwoOuterClassBaseImage_four]
  decide

private theorem alternatingSixSchurAlphaTwoClassRepresentativeImage_23 :
    alternatingSixSchurAlphaTwoClassRepresentativeImage 23 =
      alternatingSixSchurAuditedCoordinate 175 1 := by
  change
    alternatingSixSchurOuterClassBaseImage
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) 4 *
        alternatingSixSchurAuditedCoordinate 0 (-2) =
      alternatingSixSchurAuditedCoordinate 175 1
  rw [alternatingSixSchurAlphaTwoOuterClassBaseImage_four]
  decide

private theorem alternatingSixSchurAlphaTwoClassRepresentativeImage_24 :
    alternatingSixSchurAlphaTwoClassRepresentativeImage 24 =
      alternatingSixSchurAuditedCoordinate 175 0 := by
  change
    alternatingSixSchurOuterClassBaseImage
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) 4 *
        alternatingSixSchurAuditedCoordinate 0 (-3) =
      alternatingSixSchurAuditedCoordinate 175 0
  rw [alternatingSixSchurAlphaTwoOuterClassBaseImage_four]
  decide

private theorem alternatingSixSchurAlphaTwoClassRepresentativeImage_25 :
    alternatingSixSchurAlphaTwoClassRepresentativeImage 25 =
      alternatingSixSchurAuditedCoordinate 175 5 := by
  change
    alternatingSixSchurOuterClassBaseImage
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) 4 *
        alternatingSixSchurAuditedCoordinate 0 (-4) =
      alternatingSixSchurAuditedCoordinate 175 5
  rw [alternatingSixSchurAlphaTwoOuterClassBaseImage_four]
  decide

private theorem alternatingSixSchurAlphaTwoClassRepresentativeImage_26 :
    alternatingSixSchurAlphaTwoClassRepresentativeImage 26 =
      alternatingSixSchurAuditedCoordinate 175 4 := by
  change
    alternatingSixSchurOuterClassBaseImage
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) 4 *
        alternatingSixSchurAuditedCoordinate 0 (-5) =
      alternatingSixSchurAuditedCoordinate 175 4
  rw [alternatingSixSchurAlphaTwoOuterClassBaseImage_four]
  decide

/-- Checked images of the four central translates of the two long base
words. -/
private theorem alternatingSixSchurAlphaTwoClassRepresentativeImage_27 :
    alternatingSixSchurAlphaTwoClassRepresentativeImage 27 =
      alternatingSixSchurAuditedCoordinate 242 1 := by
  change
    alternatingSixSchurOuterClassBaseImage
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) 5 *
        alternatingSixSchurAuditedCoordinate 0 0 =
      alternatingSixSchurAuditedCoordinate 242 1
  rw [alternatingSixSchurAlphaTwoOuterClassBaseImage_five]
  decide

private theorem alternatingSixSchurAlphaTwoClassRepresentativeImage_28 :
    alternatingSixSchurAlphaTwoClassRepresentativeImage 28 =
      alternatingSixSchurAuditedCoordinate 242 0 := by
  change
    alternatingSixSchurOuterClassBaseImage
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) 5 *
        alternatingSixSchurAuditedCoordinate 0 (-1) =
      alternatingSixSchurAuditedCoordinate 242 0
  rw [alternatingSixSchurAlphaTwoOuterClassBaseImage_five]
  decide

private theorem alternatingSixSchurAlphaTwoClassRepresentativeImage_29 :
    alternatingSixSchurAlphaTwoClassRepresentativeImage 29 =
      alternatingSixSchurAuditedCoordinate 310 1 := by
  change
    alternatingSixSchurOuterClassBaseImage
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) 6 *
        alternatingSixSchurAuditedCoordinate 0 0 =
      alternatingSixSchurAuditedCoordinate 310 1
  rw [alternatingSixSchurAlphaTwoOuterClassBaseImage_six]
  decide

private theorem alternatingSixSchurAlphaTwoClassRepresentativeImage_30 :
    alternatingSixSchurAlphaTwoClassRepresentativeImage 30 =
      alternatingSixSchurAuditedCoordinate 310 0 := by
  change
    alternatingSixSchurOuterClassBaseImage
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) 6 *
        alternatingSixSchurAuditedCoordinate 0 (-1) =
      alternatingSixSchurAuditedCoordinate 310 0
  rw [alternatingSixSchurAlphaTwoOuterClassBaseImage_six]
  decide

/-- The `ab²` central translates have the displayed `alpha2` labels. -/
private theorem alternatingSixSchurAlphaTwoClassIndex_21 :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoClassRepresentativeImage 21) =
      alternatingSixSchurAlphaTwoClassIndexAction 21 := by
  rw [alternatingSixSchurAlphaTwoClassRepresentativeImage_21]
  rfl

private theorem alternatingSixSchurAlphaTwoClassIndex_22 :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoClassRepresentativeImage 22) =
      alternatingSixSchurAlphaTwoClassIndexAction 22 := by
  rw [alternatingSixSchurAlphaTwoClassRepresentativeImage_22]
  rfl

private theorem alternatingSixSchurAlphaTwoClassIndex_23 :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoClassRepresentativeImage 23) =
      alternatingSixSchurAlphaTwoClassIndexAction 23 := by
  rw [alternatingSixSchurAlphaTwoClassRepresentativeImage_23]
  rfl

private theorem alternatingSixSchurAlphaTwoClassIndex_24 :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoClassRepresentativeImage 24) =
      alternatingSixSchurAlphaTwoClassIndexAction 24 := by
  rw [alternatingSixSchurAlphaTwoClassRepresentativeImage_24]
  rfl

private theorem alternatingSixSchurAlphaTwoClassIndex_25 :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoClassRepresentativeImage 25) =
      alternatingSixSchurAlphaTwoClassIndexAction 25 := by
  rw [alternatingSixSchurAlphaTwoClassRepresentativeImage_25]
  rfl

private theorem alternatingSixSchurAlphaTwoClassIndex_26 :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoClassRepresentativeImage 26) =
      alternatingSixSchurAlphaTwoClassIndexAction 26 := by
  rw [alternatingSixSchurAlphaTwoClassRepresentativeImage_26]
  rfl

/-- The first long-word representative has the displayed `alpha2` label.
This check is kept separate so reduction stays within Lean's stock recursion
depth. -/
private theorem alternatingSixSchurAlphaTwoClassIndex_longWord77 :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoClassRepresentativeImage 27) =
      alternatingSixSchurAlphaTwoClassIndexAction 27 := by
  rw [alternatingSixSchurAlphaTwoClassRepresentativeImage_27]
  rfl

/-- The second long-word representative has the displayed `alpha2` label.
This check is kept separate so reduction stays within Lean's stock recursion
depth. -/
private theorem alternatingSixSchurAlphaTwoClassIndex_longWord79 :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoClassRepresentativeImage 28) =
      alternatingSixSchurAlphaTwoClassIndexAction 28 := by
  rw [alternatingSixSchurAlphaTwoClassRepresentativeImage_28]
  rfl

private theorem alternatingSixSchurAlphaTwoClassIndex_29 :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoClassRepresentativeImage 29) =
      alternatingSixSchurAlphaTwoClassIndexAction 29 := by
  rw [alternatingSixSchurAlphaTwoClassRepresentativeImage_29]
  rfl

private theorem alternatingSixSchurAlphaTwoClassIndex_30 :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoClassRepresentativeImage 30) =
      alternatingSixSchurAlphaTwoClassIndexAction 30 := by
  rw [alternatingSixSchurAlphaTwoClassRepresentativeImage_30]
  rfl

/-- Exhaustive coordinate check of the displayed `alpha2` class table. -/
theorem
    alternatingSixSchurAlphaTwoClassRepresentativeImage_classIndex
    (index : Fin 31) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoClassRepresentativeImage index) =
      alternatingSixSchurAlphaTwoClassIndexAction index := by
  fin_cases index
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact alternatingSixSchurAlphaTwoClassIndex_21
  · exact alternatingSixSchurAlphaTwoClassIndex_22
  · exact alternatingSixSchurAlphaTwoClassIndex_23
  · exact alternatingSixSchurAlphaTwoClassIndex_24
  · exact alternatingSixSchurAlphaTwoClassIndex_25
  · exact alternatingSixSchurAlphaTwoClassIndex_26
  · exact alternatingSixSchurAlphaTwoClassIndex_longWord77
  · exact alternatingSixSchurAlphaTwoClassIndex_longWord79
  · exact alternatingSixSchurAlphaTwoClassIndex_29
  · exact alternatingSixSchurAlphaTwoClassIndex_30

/-- The proved coordinate automorphism induces the displayed `alpha2`
permutation on checked class indices. -/
theorem alternatingSixSchurAlphaTwoAutomorphism_classIndex_representative
    (index : Fin 31) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoAutomorphism
          (alternatingSixSchurClassRepresentative index)) =
      alternatingSixSchurAlphaTwoClassIndexAction index := by
  change
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoEndomorphism
          (alternatingSixSchurClassRepresentative index)) =
      alternatingSixSchurAlphaTwoClassIndexAction index
  rw [
    alternatingSixSchurAlphaTwoEndomorphism_classRepresentative_apply,
    alternatingSixSchurAlphaTwoClassRepresentativeImage_classIndex
  ]

/-- The second automorphism acts by the displayed permutation on the class
index of every coordinate. -/
theorem alternatingSixSchurAlphaTwoAutomorphism_classIndex
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoAutomorphism coordinate) =
      alternatingSixSchurAlphaTwoClassIndexAction
        (alternatingSixSchurClassIndex coordinate) := by
  let conjugator :=
    alternatingSixSchurClassConjugator coordinate
  have hmap :
      alternatingSixSchurAlphaTwoAutomorphism conjugator *
            alternatingSixSchurAlphaTwoAutomorphism
              (alternatingSixSchurClassRepresentative
                (alternatingSixSchurClassIndex coordinate)) *
            (alternatingSixSchurAlphaTwoAutomorphism conjugator)⁻¹ =
        alternatingSixSchurAlphaTwoAutomorphism coordinate := by
    simpa only [map_mul, map_inv] using
      congrArg alternatingSixSchurAlphaTwoAutomorphism
        (alternatingSixSchurClassConjugator_spec coordinate)
  have hinvariant :=
    alternatingSixSchurClassIndex_conjugation_invariant
      (alternatingSixSchurAlphaTwoAutomorphism conjugator)
      (alternatingSixSchurAlphaTwoAutomorphism
        (alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex coordinate)))
  rw [hmap] at hinvariant
  exact hinvariant.trans
    (alternatingSixSchurAlphaTwoAutomorphism_classIndex_representative
      (alternatingSixSchurClassIndex coordinate))

/-- The inverse of the second automorphism acts by the inverse displayed
permutation on class indices. -/
theorem alternatingSixSchurAlphaTwoAutomorphism_symm_classIndex
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoAutomorphism.symm coordinate) =
      alternatingSixSchurAlphaTwoClassIndexAction.symm
        (alternatingSixSchurClassIndex coordinate) := by
  apply alternatingSixSchurAlphaTwoClassIndexAction.injective
  rw [alternatingSixSchurAlphaTwoClassIndexAction.apply_symm_apply]
  simpa using
    (alternatingSixSchurAlphaTwoAutomorphism_classIndex
      (alternatingSixSchurAlphaTwoAutomorphism.symm coordinate)).symm

end GroupTheory
end McKayConjecture
