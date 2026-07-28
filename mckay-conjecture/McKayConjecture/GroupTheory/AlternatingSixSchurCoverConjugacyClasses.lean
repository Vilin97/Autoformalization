/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyChecks
import McKayConjecture.GroupTheory.ConjugationInvariant

/-!
# Conjugacy classes of the sixfold cover of `A₆`

The generated certificate supplies 31 representatives, a label on every
coordinate, generator-invariance checks for that label, and an explicit
conjugator from the corresponding representative to every coordinate.

Generator invariance is promoted to invariance under the whole presented
group.  The representatives therefore give an equivalence with the
conjugacy-class quotient, first for the computable coordinate group and then
for the canonical universal cover.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

/-- The coordinate class label transported to the abstract presentation. -/
def alternatingSixSchurPresentedClassIndex
    (g : AlternatingSixSchurPresentedGroup) :
    Fin 31 :=
  alternatingSixSchurClassIndex
    (mulEquivPresentedGroup.symm g)

/-- The coordinate `⟨1,0⟩` is the presentation generator `a`. -/
theorem alternatingSixSchurCoordinateA_preimage :
    mulEquivPresentedGroup.symm
        alternatingSixSchurPresentedA =
      alternatingSixSchurCoordinateA := by
  apply mulEquivPresentedGroup.injective
  rw [MulEquiv.apply_symm_apply]
  change
    alternatingSixSchurPresentedA =
      evaluate alternatingSixSchurCoordinateA
  rfl

/-- The coordinate `⟨2,0⟩` is the presentation generator `b`. -/
theorem alternatingSixSchurCoordinateB_preimage :
    mulEquivPresentedGroup.symm
        alternatingSixSchurPresentedB =
      alternatingSixSchurCoordinateB := by
  apply mulEquivPresentedGroup.injective
  rw [MulEquiv.apply_symm_apply]
  change
    alternatingSixSchurPresentedB =
      evaluate alternatingSixSchurCoordinateB
  rfl

/-- The checked `a`-invariance places `a` in the invariant subgroup. -/
theorem alternatingSixSchurPresentedA_mem_classIndexInvariant :
    alternatingSixSchurPresentedA ∈
      conjugationInvariantSubgroup
        alternatingSixSchurPresentedClassIndex := by
  intro x
  simpa [alternatingSixSchurPresentedClassIndex,
    alternatingSixSchurCoordinateA_preimage] using
    alternatingSixSchurClassIndex_conjugateA
      (mulEquivPresentedGroup.symm x)

/-- The checked `b`-invariance places `b` in the invariant subgroup. -/
theorem alternatingSixSchurPresentedB_mem_classIndexInvariant :
    alternatingSixSchurPresentedB ∈
      conjugationInvariantSubgroup
        alternatingSixSchurPresentedClassIndex := by
  intro x
  simpa [alternatingSixSchurPresentedClassIndex,
    alternatingSixSchurCoordinateB_preimage] using
    alternatingSixSchurClassIndex_conjugateB
      (mulEquivPresentedGroup.symm x)

/-- Each central presentation generator preserves the class label. -/
theorem alternatingSixSchurPresentedK_mem_classIndexInvariant
    (i : Fin 4) :
    alternatingSixSchurPresentedK i ∈
      conjugationInvariantSubgroup
        alternatingSixSchurPresentedClassIndex := by
  intro x
  have hcommute :
      Commute (alternatingSixSchurPresentedK i) x :=
    (Subgroup.mem_center_iff.mp
      (alternatingSixSchurPresentedK_mem_center i) x).symm
  rw [hcommute.eq]
  simp

/-- All six generators of the Schur-cover presentation preserve the class
label. -/
theorem alternatingSixSchurPresentedGenerator_mem_classIndexInvariant
    (j : Fin 6) :
    alternatingSixSchurPresentedGenerator j ∈
      conjugationInvariantSubgroup
        alternatingSixSchurPresentedClassIndex := by
  fin_cases j
  · exact
      alternatingSixSchurPresentedA_mem_classIndexInvariant
  · exact
      alternatingSixSchurPresentedB_mem_classIndexInvariant
  · exact
      alternatingSixSchurPresentedK_mem_classIndexInvariant 0
  · exact
      alternatingSixSchurPresentedK_mem_classIndexInvariant 1
  · exact
      alternatingSixSchurPresentedK_mem_classIndexInvariant 2
  · exact
      alternatingSixSchurPresentedK_mem_classIndexInvariant 3

/-- The transported class label is invariant under conjugation by every
element of the presented group. -/
theorem alternatingSixSchurPresentedClassIndex_conjugation_invariant
    (g x : AlternatingSixSchurPresentedGroup) :
    alternatingSixSchurPresentedClassIndex
        (g * x * g⁻¹) =
      alternatingSixSchurPresentedClassIndex x := by
  have hclosure :
      Subgroup.closure
          (Set.range
            (PresentedGroup.of :
              Fin 6 → AlternatingSixSchurPresentedGroup)) ≤
        conjugationInvariantSubgroup
          alternatingSixSchurPresentedClassIndex :=
    (Subgroup.closure_le
      (conjugationInvariantSubgroup
        alternatingSixSchurPresentedClassIndex)).2 (by
      rintro _ ⟨j, rfl⟩
      exact
        alternatingSixSchurPresentedGenerator_mem_classIndexInvariant j)
  rw [PresentedGroup.closure_range_of] at hclosure
  exact hclosure (Subgroup.mem_top g) x

/-- The checked coordinate label is a genuine conjugacy invariant. -/
theorem alternatingSixSchurClassIndex_conjugation_invariant
    (g x : AlternatingSixSchurCoordinates) :
    alternatingSixSchurClassIndex (g * x * g⁻¹) =
      alternatingSixSchurClassIndex x := by
  have hg :
      mulEquivPresentedGroup.symm
          (mulEquivPresentedGroup g) = g :=
    mulEquivPresentedGroup.symm_apply_apply g
  have hx :
      mulEquivPresentedGroup.symm
          (mulEquivPresentedGroup x) = x :=
    mulEquivPresentedGroup.symm_apply_apply x
  simpa only [alternatingSixSchurPresentedClassIndex,
    map_mul, map_inv, hg, hx] using
    (alternatingSixSchurPresentedClassIndex_conjugation_invariant
      (mulEquivPresentedGroup g)
      (mulEquivPresentedGroup x))

/-- Every advertised representative has its own label. -/
theorem alternatingSixSchurClassIndex_representative
    (i : Fin 31) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurClassRepresentative i) = i := by
  fin_cases i <;> decide

/-- Send an advertised representative to its conjugacy class. -/
def alternatingSixSchurRepresentativeConjugacyClass
    (i : Fin 31) :
    ConjClasses AlternatingSixSchurCoordinates :=
  ConjClasses.mk
    (alternatingSixSchurClassRepresentative i)

/-- Distinct advertised representatives are not conjugate. -/
theorem alternatingSixSchurRepresentativeConjugacyClass_injective :
    Function.Injective
      alternatingSixSchurRepresentativeConjugacyClass := by
  intro i j hij
  have hconj :
      IsConj
        (alternatingSixSchurClassRepresentative i)
        (alternatingSixSchurClassRepresentative j) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hij
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hinvariant :=
    alternatingSixSchurClassIndex_conjugation_invariant g
      (alternatingSixSchurClassRepresentative i)
  rw [hg, alternatingSixSchurClassIndex_representative,
    alternatingSixSchurClassIndex_representative] at hinvariant
  exact hinvariant.symm

/-- The checked orbit witnesses show that every conjugacy class has an
advertised representative. -/
theorem alternatingSixSchurRepresentativeConjugacyClass_surjective :
    Function.Surjective
      alternatingSixSchurRepresentativeConjugacyClass := by
  intro conjugacyClass
  obtain ⟨coordinate, rfl⟩ :=
    ConjClasses.mk_surjective conjugacyClass
  refine
    ⟨alternatingSixSchurClassIndex coordinate, ?_⟩
  rw [alternatingSixSchurRepresentativeConjugacyClass,
    ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_iff.mpr
    ⟨alternatingSixSchurClassConjugator coordinate,
      alternatingSixSchurClassConjugator_spec coordinate⟩

/-- The 31 checked representatives are exactly the conjugacy classes of the
coordinate group. -/
def alternatingSixSchurCoordinateConjugacyClassEquiv :
    Fin 31 ≃ ConjClasses AlternatingSixSchurCoordinates :=
  Equiv.ofBijective
    alternatingSixSchurRepresentativeConjugacyClass
    ⟨alternatingSixSchurRepresentativeConjugacyClass_injective,
      alternatingSixSchurRepresentativeConjugacyClass_surjective⟩

/-- The coordinate sixfold cover has exactly 31 conjugacy classes. -/
theorem natCard_conjClasses_alternatingSixSchurCoordinates :
    Nat.card
        (ConjClasses AlternatingSixSchurCoordinates) = 31 := by
  rw [Nat.card_congr
    alternatingSixSchurCoordinateConjugacyClassEquiv.symm]
  simp

/-- Transport conjugacy classes from the coordinates to the abstract Schur
presentation. -/
def alternatingSixSchurPresentedConjugacyClassesEquiv :
    ConjClasses AlternatingSixSchurCoordinates ≃
      ConjClasses AlternatingSixSchurPresentedGroup :=
  conjugacyClassesEquivOfMulEquiv mulEquivPresentedGroup

/-- The computable Schur-cover coordinates are multiplicatively equivalent
to the canonical universal cover. -/
def alternatingSixSchurCoordinatesEquivUniversalCover :
    AlternatingSixSchurCoordinates ≃*
      AlternatingSixUniversalCover :=
  mulEquivPresentedGroup.trans
    (alternatingSixSchurUniversalCentralExtension.sourceEquiv
      alternatingSixUniversalCentralExtension)

/-- The presented sixfold cover has exactly 31 conjugacy classes. -/
theorem natCard_conjClasses_alternatingSixSchurPresentedGroup :
    Nat.card
        (ConjClasses AlternatingSixSchurPresentedGroup) = 31 := by
  calc
    Nat.card
          (ConjClasses AlternatingSixSchurPresentedGroup) =
        Nat.card
          (ConjClasses AlternatingSixSchurCoordinates) :=
      Nat.card_congr
        alternatingSixSchurPresentedConjugacyClassesEquiv.symm
    _ = 31 :=
      natCard_conjClasses_alternatingSixSchurCoordinates

/-- Transport conjugacy classes from the Schur presentation to the canonical
universal cover. -/
def alternatingSixUniversalCoverConjugacyClassesEquiv :
    ConjClasses AlternatingSixSchurPresentedGroup ≃
      ConjClasses AlternatingSixUniversalCover :=
  conjugacyClassesEquivOfMulEquiv
    (alternatingSixSchurUniversalCentralExtension.sourceEquiv
      alternatingSixUniversalCentralExtension)

/-- The canonical universal cover of `A₆` has exactly 31 conjugacy classes. -/
theorem natCard_conjClasses_alternatingSixUniversalCover :
    Nat.card
        (ConjClasses AlternatingSixUniversalCover) = 31 := by
  calc
    Nat.card
          (ConjClasses AlternatingSixUniversalCover) =
        Nat.card
          (ConjClasses AlternatingSixSchurPresentedGroup) :=
      Nat.card_congr
        alternatingSixUniversalCoverConjugacyClassesEquiv.symm
    _ = 31 :=
      natCard_conjClasses_alternatingSixSchurPresentedGroup

end GroupTheory
end McKayConjecture
