/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteRootResidueKernel
import McKayConjecture.GroupTheory.CyclicComplexCharacterExtension

/-!
# A complex character compatible with cyclotomic residue reduction

Although a chosen cyclotomic residue field need not embed into a
previously chosen finite coefficient field with prescribed root values,
its multiplicative group always has a complex character recovering
the prime-to-`q` part of every reduced complex root.

The construction first factors the complex prime-to-`q` projection
through the range of residue reduction, using the equality of kernels.
The range character then extends to all residue-field units because
finite-field unit groups are cyclic and complex numbers contain all
roots of unity.  This is only a multiplicative homomorphism; no
additive or field compatibility is asserted or needed.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FiniteRootCoefficientRing

open Representation

variable (q n : ℕ) [Fact q.Prime] [NeZero n]

/-- The CRT prime-to-`q` projection, viewed in the complex unit group. -/
def complexPrimeToRootsProjection :
    rootsOfUnity n ℂ →* ℂˣ :=
  (rootsOfUnity n ℂ).subtype.comp
    (primeToRootsProjection q n)

@[simp]
theorem complexPrimeToRootsProjection_apply
    (z : rootsOfUnity n ℂ) :
    complexPrimeToRootsProjection q n z =
      (primeToRootsProjection q n z : ℂˣ) :=
  rfl

/-- The character on the range of residue reduction induced by the
complex prime-to-`q` projection. -/
def residueRangeComplexCharacter :
    (rootToResidueField q n).range →* ℂˣ :=
  MonoidHom.factorThroughRange
    (rootToResidueField q n)
    (complexPrimeToRootsProjection q n)
    (by
      intro z hz
      rw [MonoidHom.mem_ker] at hz ⊢
      rw [
        complexPrimeToRootsProjection_apply,
        primeToRootsProjection_eq_one_of_rootToResidueField_eq_one
          q n z hz]
      rfl)

@[simp]
theorem residueRangeComplexCharacter_root
    (z : rootsOfUnity n ℂ) :
    residueRangeComplexCharacter q n
        ((rootToResidueField q n).rangeRestrict z) =
      (primeToRootsProjection q n z : ℂˣ) := by
  exact
    MonoidHom.factorThroughRange_apply
      (rootToResidueField q n)
      (complexPrimeToRootsProjection q n)
      (by
        intro w hw
        rw [MonoidHom.mem_ker] at hw ⊢
        rw [
          complexPrimeToRootsProjection_apply,
          primeToRootsProjection_eq_one_of_rootToResidueField_eq_one
            q n w hw]
        rfl)
      z

/-- There exists a character on all units of the chosen residue field
whose pullback along root reduction is the complex prime-to-`q`
projection. -/
theorem exists_residueUnitsComplexCharacter :
    ∃ κ :
        (ResidueFieldAbovePrime q n)ˣ →* ℂˣ,
      κ.comp (rootToResidueField q n) =
        complexPrimeToRootsProjection q n := by
  obtain ⟨κ, hκ⟩ :=
    MonoidHom.exists_extension_to_complexUnits_of_isCyclic
      (rootToResidueField q n).range
      (residueRangeComplexCharacter q n)
  refine ⟨κ, MonoidHom.ext fun z ↦ ?_⟩
  change
    κ (rootToResidueField q n z) =
      complexPrimeToRootsProjection q n z
  calc
    κ (rootToResidueField q n z) =
        κ.domRestrict
          (rootToResidueField q n).range
          ((rootToResidueField q n).rangeRestrict z) :=
      rfl
    _ =
        residueRangeComplexCharacter q n
          ((rootToResidueField q n).rangeRestrict z) :=
      DFunLike.congr_fun hκ
        ((rootToResidueField q n).rangeRestrict z)
    _ = complexPrimeToRootsProjection q n z :=
      residueRangeComplexCharacter_root q n z

/-- A chosen multiplicative character from residue-field units to
complex units compatible with reduction of all complex `n`th roots. -/
def residueUnitsComplexCharacter :
    (ResidueFieldAbovePrime q n)ˣ →* ℂˣ :=
  Classical.choose
    (exists_residueUnitsComplexCharacter q n)

/-- The chosen residue-unit character recovers the prime-to-`q`
projection after root reduction. -/
@[simp]
theorem residueUnitsComplexCharacter_comp_rootToResidueField :
    (residueUnitsComplexCharacter q n).comp
        (rootToResidueField q n) =
      complexPrimeToRootsProjection q n :=
  Classical.choose_spec
    (exists_residueUnitsComplexCharacter q n)

@[simp]
theorem residueUnitsComplexCharacter_rootToResidueField
    (z : rootsOfUnity n ℂ) :
    residueUnitsComplexCharacter q n
        (rootToResidueField q n z) =
      (primeToRootsProjection q n z : ℂˣ) := by
  exact
    DFunLike.congr_fun
      (residueUnitsComplexCharacter_comp_rootToResidueField
        q n)
      z

end FiniteRootCoefficientRing
end CharacterTriple
end McKayConjecture
