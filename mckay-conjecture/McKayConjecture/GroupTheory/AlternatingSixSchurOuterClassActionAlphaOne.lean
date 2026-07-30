/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterClassActionData

/-!
# Checked class action of the first outer automorphism

The homomorphism property reduces each representative to one of seven base
words and an inverted central coordinate.  The final class labels are
exhaustively checked against the finite conjugacy certificate.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- `alpha1` carries every source base word to the same word in its two
audited generator images. -/
theorem alternatingSixSchurAlphaOneEndomorphism_outerClassBaseImage
    (base : Fin 7) :
    alternatingSixSchurAlphaOneEndomorphism
        (alternatingSixSchurOuterClassBaseImage
          alternatingSixSchurOuterClassSourceA
          alternatingSixSchurOuterClassSourceB base) =
      alternatingSixSchurOuterClassBaseImage
        (alternatingSixSchurAlphaOneGeneratorCoordinates 0)
        (alternatingSixSchurAlphaOneGeneratorCoordinates 1)
        base := by
  fin_cases base <;>
    simp [alternatingSixSchurOuterClassBaseImage,
      alternatingSixSchurOuterClassSourceA,
      alternatingSixSchurOuterClassSourceB,
      alternatingSixSchurAlphaOneEndomorphism_generator]

/-- `alpha1` negates every central coordinate. -/
theorem alternatingSixSchurAlphaOneEndomorphism_central
    (central : Fin 6) :
    alternatingSixSchurAlphaOneEndomorphism
        (alternatingSixSchurAuditedCoordinate 0
          (ZMod.finEquiv 6 central)) =
      alternatingSixSchurAuditedCoordinate 0
        (-(ZMod.finEquiv 6 central)) := by
  apply alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
  simp [alternatingSixSchurAlphaOneGeneratorCoordinates,
    alternatingSixSchurAuditedCoordinate]

/-- Exact coordinate image of every checked representative under `alpha1`. -/
theorem
    alternatingSixSchurAlphaOneEndomorphism_classRepresentative_apply
    (index : Fin 31) :
    alternatingSixSchurAlphaOneEndomorphism
        (alternatingSixSchurClassRepresentative index) =
      alternatingSixSchurAlphaOneClassRepresentativeImage index := by
  rw [
    alternatingSixSchurClassRepresentative_eq_outerBase_mul_central,
    map_mul,
    alternatingSixSchurAlphaOneEndomorphism_outerClassBaseImage,
    alternatingSixSchurAlphaOneEndomorphism_central
  ]
  rfl

/-- The first long-word representative has the displayed `alpha1` label.
This check is kept separate so reduction stays within Lean's stock recursion
depth. -/
private theorem alternatingSixSchurAlphaOneClassIndex_longWord77 :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaOneClassRepresentativeImage 27) =
      alternatingSixSchurAlphaOneClassIndexAction 27 := by
  rfl

/-- The second long-word representative has the displayed `alpha1` label.
This check is kept separate so reduction stays within Lean's stock recursion
depth. -/
private theorem alternatingSixSchurAlphaOneClassIndex_longWord79 :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaOneClassRepresentativeImage 28) =
      alternatingSixSchurAlphaOneClassIndexAction 28 := by
  rfl

/-- Exhaustive coordinate check of the displayed `alpha1` class table. -/
theorem
    alternatingSixSchurAlphaOneClassRepresentativeImage_classIndex
    (index : Fin 31) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaOneClassRepresentativeImage index) =
      alternatingSixSchurAlphaOneClassIndexAction index := by
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
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact alternatingSixSchurAlphaOneClassIndex_longWord77
  · exact alternatingSixSchurAlphaOneClassIndex_longWord79
  · rfl
  · rfl

/-- The proved coordinate automorphism induces the displayed `alpha1`
permutation on checked class indices. -/
theorem alternatingSixSchurAlphaOneAutomorphism_classIndex_representative
    (index : Fin 31) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaOneAutomorphism
          (alternatingSixSchurClassRepresentative index)) =
      alternatingSixSchurAlphaOneClassIndexAction index := by
  change
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaOneEndomorphism
          (alternatingSixSchurClassRepresentative index)) =
      alternatingSixSchurAlphaOneClassIndexAction index
  rw [
    alternatingSixSchurAlphaOneEndomorphism_classRepresentative_apply,
    alternatingSixSchurAlphaOneClassRepresentativeImage_classIndex
  ]

/-- The first automorphism acts by the displayed permutation on the class
index of every coordinate. -/
theorem alternatingSixSchurAlphaOneAutomorphism_classIndex
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaOneAutomorphism coordinate) =
      alternatingSixSchurAlphaOneClassIndexAction
        (alternatingSixSchurClassIndex coordinate) := by
  let conjugator :=
    alternatingSixSchurClassConjugator coordinate
  have hmap :
      alternatingSixSchurAlphaOneAutomorphism conjugator *
            alternatingSixSchurAlphaOneAutomorphism
              (alternatingSixSchurClassRepresentative
                (alternatingSixSchurClassIndex coordinate)) *
            (alternatingSixSchurAlphaOneAutomorphism conjugator)⁻¹ =
        alternatingSixSchurAlphaOneAutomorphism coordinate := by
    simpa only [map_mul, map_inv] using
      congrArg alternatingSixSchurAlphaOneAutomorphism
        (alternatingSixSchurClassConjugator_spec coordinate)
  have hinvariant :=
    alternatingSixSchurClassIndex_conjugation_invariant
      (alternatingSixSchurAlphaOneAutomorphism conjugator)
      (alternatingSixSchurAlphaOneAutomorphism
        (alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex coordinate)))
  rw [hmap] at hinvariant
  exact hinvariant.trans
    (alternatingSixSchurAlphaOneAutomorphism_classIndex_representative
      (alternatingSixSchurClassIndex coordinate))

/-- The inverse of the first automorphism acts by the inverse displayed
permutation on class indices. -/
theorem alternatingSixSchurAlphaOneAutomorphism_symm_classIndex
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaOneAutomorphism.symm coordinate) =
      alternatingSixSchurAlphaOneClassIndexAction.symm
        (alternatingSixSchurClassIndex coordinate) := by
  apply alternatingSixSchurAlphaOneClassIndexAction.injective
  rw [alternatingSixSchurAlphaOneClassIndexAction.apply_symm_apply]
  simpa using
    (alternatingSixSchurAlphaOneAutomorphism_classIndex
      (alternatingSixSchurAlphaOneAutomorphism.symm coordinate)).symm

end GroupTheory
end McKayConjecture
