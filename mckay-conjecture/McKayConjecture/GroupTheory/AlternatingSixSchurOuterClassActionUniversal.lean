/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterClassActionAlphaOne
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterClassActionAlphaTwo

/-!
# Outer class actions on the canonical universal cover of `A₆`

The checked coordinate actions are transported to the canonical universal
cover.  The resulting API records their action both on the checked class
index and directly on the conjugacy-class quotient.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- Every element of the canonical universal cover is conjugate to the
transported representative selected by its checked class index. -/
theorem alternatingSixUniversalCover_isConj_classRepresentative
    (element : AlternatingSixUniversalCover) :
    IsConj element
      (alternatingSixUniversalCoverClassRepresentative
        (alternatingSixUniversalCoverClassIndex element)) := by
  obtain ⟨coordinate, rfl⟩ :=
    alternatingSixSchurCoordinatesEquivUniversalCover.surjective element
  have hcoordinate :
      IsConj coordinate
        (alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex coordinate)) :=
    (isConj_iff.mpr
      ⟨alternatingSixSchurClassConjugator coordinate,
        alternatingSixSchurClassConjugator_spec coordinate⟩).symm
  simpa [alternatingSixUniversalCoverClassRepresentative,
    alternatingSixUniversalCoverClassIndex] using
    alternatingSixSchurCoordinatesEquivUniversalCover.toMonoidHom.map_isConj
      hcoordinate

/-- The transported first automorphism acts by the checked first
permutation on every universal-cover class index. -/
theorem alternatingSixUniversalCoverAlphaOneAutomorphism_classIndex
    (element : AlternatingSixUniversalCover) :
    alternatingSixUniversalCoverClassIndex
        (alternatingSixUniversalCoverAlphaOneAutomorphism element) =
      alternatingSixSchurAlphaOneClassIndexAction
        (alternatingSixUniversalCoverClassIndex element) := by
  obtain ⟨coordinate, rfl⟩ :=
    alternatingSixSchurCoordinatesEquivUniversalCover.surjective element
  simpa [alternatingSixUniversalCoverClassIndex] using
    alternatingSixSchurAlphaOneAutomorphism_classIndex coordinate

/-- The inverse transported first automorphism acts by the inverse checked
permutation. -/
theorem alternatingSixUniversalCoverAlphaOneAutomorphism_symm_classIndex
    (element : AlternatingSixUniversalCover) :
    alternatingSixUniversalCoverClassIndex
        (alternatingSixUniversalCoverAlphaOneAutomorphism.symm element) =
      alternatingSixSchurAlphaOneClassIndexAction.symm
        (alternatingSixUniversalCoverClassIndex element) := by
  apply alternatingSixSchurAlphaOneClassIndexAction.injective
  rw [alternatingSixSchurAlphaOneClassIndexAction.apply_symm_apply]
  simpa using
    (alternatingSixUniversalCoverAlphaOneAutomorphism_classIndex
      (alternatingSixUniversalCoverAlphaOneAutomorphism.symm element)).symm

/-- The transported second automorphism acts by the checked second
permutation on every universal-cover class index. -/
theorem alternatingSixUniversalCoverAlphaTwoAutomorphism_classIndex
    (element : AlternatingSixUniversalCover) :
    alternatingSixUniversalCoverClassIndex
        (alternatingSixUniversalCoverAlphaTwoAutomorphism element) =
      alternatingSixSchurAlphaTwoClassIndexAction
        (alternatingSixUniversalCoverClassIndex element) := by
  obtain ⟨coordinate, rfl⟩ :=
    alternatingSixSchurCoordinatesEquivUniversalCover.surjective element
  simpa [alternatingSixUniversalCoverClassIndex] using
    alternatingSixSchurAlphaTwoAutomorphism_classIndex coordinate

/-- The inverse transported second automorphism acts by the inverse checked
permutation. -/
theorem alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_classIndex
    (element : AlternatingSixUniversalCover) :
    alternatingSixUniversalCoverClassIndex
        (alternatingSixUniversalCoverAlphaTwoAutomorphism.symm element) =
      alternatingSixSchurAlphaTwoClassIndexAction.symm
        (alternatingSixUniversalCoverClassIndex element) := by
  apply alternatingSixSchurAlphaTwoClassIndexAction.injective
  rw [alternatingSixSchurAlphaTwoClassIndexAction.apply_symm_apply]
  simpa using
    (alternatingSixUniversalCoverAlphaTwoAutomorphism_classIndex
      (alternatingSixUniversalCoverAlphaTwoAutomorphism.symm element)).symm

/-- The first transported automorphism sends each checked representative
into the conjugacy class indexed by the first displayed permutation. -/
theorem
    alternatingSixUniversalCoverAlphaOneAutomorphism_representative_isConj
    (index : Fin 31) :
    IsConj
      (alternatingSixUniversalCoverAlphaOneAutomorphism
        (alternatingSixUniversalCoverClassRepresentative index))
      (alternatingSixUniversalCoverClassRepresentative
        (alternatingSixSchurAlphaOneClassIndexAction index)) := by
  have h :=
    alternatingSixUniversalCover_isConj_classRepresentative
      (alternatingSixUniversalCoverAlphaOneAutomorphism
        (alternatingSixUniversalCoverClassRepresentative index))
  rw [alternatingSixUniversalCoverAlphaOneAutomorphism_classIndex,
    alternatingSixUniversalCoverClassIndex_representative] at h
  exact h

/-- The second transported automorphism sends each checked representative
into the conjugacy class indexed by the second displayed permutation. -/
theorem
    alternatingSixUniversalCoverAlphaTwoAutomorphism_representative_isConj
    (index : Fin 31) :
    IsConj
      (alternatingSixUniversalCoverAlphaTwoAutomorphism
        (alternatingSixUniversalCoverClassRepresentative index))
      (alternatingSixUniversalCoverClassRepresentative
        (alternatingSixSchurAlphaTwoClassIndexAction index)) := by
  have h :=
    alternatingSixUniversalCover_isConj_classRepresentative
      (alternatingSixUniversalCoverAlphaTwoAutomorphism
        (alternatingSixUniversalCoverClassRepresentative index))
  rw [alternatingSixUniversalCoverAlphaTwoAutomorphism_classIndex,
    alternatingSixUniversalCoverClassIndex_representative] at h
  exact h

/-- Quotient-level form of the first universal-cover class action. -/
theorem alternatingSixUniversalCoverAlphaOneAutomorphism_conjClasses_mk
    (element : AlternatingSixUniversalCover) :
    ConjClasses.map
        alternatingSixUniversalCoverAlphaOneAutomorphism.toMonoidHom
        (ConjClasses.mk element) =
      ConjClasses.mk
        (alternatingSixUniversalCoverClassRepresentative
          (alternatingSixSchurAlphaOneClassIndexAction
            (alternatingSixUniversalCoverClassIndex element))) := by
  change
    ConjClasses.mk
        (alternatingSixUniversalCoverAlphaOneAutomorphism element) =
      _
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  have h :=
    alternatingSixUniversalCover_isConj_classRepresentative
      (alternatingSixUniversalCoverAlphaOneAutomorphism element)
  rw [alternatingSixUniversalCoverAlphaOneAutomorphism_classIndex] at h
  exact h

/-- Quotient-level form of the inverse first universal-cover class action. -/
theorem
    alternatingSixUniversalCoverAlphaOneAutomorphism_symm_conjClasses_mk
    (element : AlternatingSixUniversalCover) :
    ConjClasses.map
        alternatingSixUniversalCoverAlphaOneAutomorphism.symm.toMonoidHom
        (ConjClasses.mk element) =
      ConjClasses.mk
        (alternatingSixUniversalCoverClassRepresentative
          (alternatingSixSchurAlphaOneClassIndexAction.symm
            (alternatingSixUniversalCoverClassIndex element))) := by
  change
    ConjClasses.mk
        (alternatingSixUniversalCoverAlphaOneAutomorphism.symm element) =
      _
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  have h :=
    alternatingSixUniversalCover_isConj_classRepresentative
      (alternatingSixUniversalCoverAlphaOneAutomorphism.symm element)
  rw [alternatingSixUniversalCoverAlphaOneAutomorphism_symm_classIndex] at h
  exact h

/-- Quotient-level form of the second universal-cover class action. -/
theorem alternatingSixUniversalCoverAlphaTwoAutomorphism_conjClasses_mk
    (element : AlternatingSixUniversalCover) :
    ConjClasses.map
        alternatingSixUniversalCoverAlphaTwoAutomorphism.toMonoidHom
        (ConjClasses.mk element) =
      ConjClasses.mk
        (alternatingSixUniversalCoverClassRepresentative
          (alternatingSixSchurAlphaTwoClassIndexAction
            (alternatingSixUniversalCoverClassIndex element))) := by
  change
    ConjClasses.mk
        (alternatingSixUniversalCoverAlphaTwoAutomorphism element) =
      _
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  have h :=
    alternatingSixUniversalCover_isConj_classRepresentative
      (alternatingSixUniversalCoverAlphaTwoAutomorphism element)
  rw [alternatingSixUniversalCoverAlphaTwoAutomorphism_classIndex] at h
  exact h

/-- Quotient-level form of the inverse second universal-cover class action. -/
theorem
    alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_conjClasses_mk
    (element : AlternatingSixUniversalCover) :
    ConjClasses.map
        alternatingSixUniversalCoverAlphaTwoAutomorphism.symm.toMonoidHom
        (ConjClasses.mk element) =
      ConjClasses.mk
        (alternatingSixUniversalCoverClassRepresentative
          (alternatingSixSchurAlphaTwoClassIndexAction.symm
            (alternatingSixUniversalCoverClassIndex element))) := by
  change
    ConjClasses.mk
        (alternatingSixUniversalCoverAlphaTwoAutomorphism.symm element) =
      _
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  have h :=
    alternatingSixUniversalCover_isConj_classRepresentative
      (alternatingSixUniversalCoverAlphaTwoAutomorphism.symm element)
  rw [alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_classIndex] at h
  exact h

end GroupTheory
end McKayConjecture
