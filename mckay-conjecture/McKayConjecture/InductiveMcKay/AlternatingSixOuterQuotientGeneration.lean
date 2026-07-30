/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterClassActionAlphaOne
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterClassActionAlphaTwo
import McKayConjecture.GroupTheory.OrderFourGeneration
import McKayConjecture.InductiveMcKay.AlternatingSixOuterSylowAdjustment
import McKayConjecture.InductiveMcKay.OuterAutomorphismClassInvariant

/-!
# The outer-quotient generation boundary for the universal cover of `A₆`

The checked conjugacy-class actions prove in Lean that the identity, the two
canonical outer classes, and their product are four distinct elements.  Thus
only the upper bound of four outer classes remains as a classification input.

The remaining upper-bound proposition is deliberately named rather than
asserted.  GAP verifies exact cardinality four by computing automorphism-
group and inner-automorphism-group orders `1440` and `360`, but that external
computation is not itself a kernel proof of the classification of all
automorphisms.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev universalCover :=
  AlternatingSixUniversalCover

private abbrev outerQuotient :=
  OuterAutomorphismQuotient universalCover

/-- The outer class of the first checked automorphism. -/
def alternatingSixUniversalCoverAlphaOneOuterClass :
    outerQuotient :=
  QuotientGroup.mk'
    (InnerAutomorphismSubgroup universalCover)
    alternatingSixUniversalCoverAlphaOneAutomorphism

/-- The outer class of the second checked automorphism. -/
def alternatingSixUniversalCoverAlphaTwoOuterClass :
    outerQuotient :=
  QuotientGroup.mk'
    (InnerAutomorphismSubgroup universalCover)
    alternatingSixUniversalCoverAlphaTwoAutomorphism

/-- The transported class index is invariant under conjugation in the
canonical universal cover. -/
theorem alternatingSixUniversalCoverClassIndex_conjugation_invariant
    (g x : universalCover) :
    alternatingSixUniversalCoverClassIndex
        (g * x * g⁻¹) =
      alternatingSixUniversalCoverClassIndex x := by
  simpa only [alternatingSixUniversalCoverClassIndex,
    map_mul, map_inv] using
    alternatingSixSchurClassIndex_conjugation_invariant
      (alternatingSixSchurCoordinatesEquivUniversalCover.symm g)
      (alternatingSixSchurCoordinatesEquivUniversalCover.symm x)

/-- The first canonical automorphism has the checked class action after
transport to the universal cover. -/
theorem
    alternatingSixUniversalCoverAlphaOneAutomorphism_classIndex_representative
    (index : Fin 31) :
    alternatingSixUniversalCoverClassIndex
        (alternatingSixUniversalCoverAlphaOneAutomorphism
          (alternatingSixUniversalCoverClassRepresentative index)) =
      alternatingSixSchurAlphaOneClassIndexAction index := by
  simpa [alternatingSixUniversalCoverClassIndex,
    alternatingSixUniversalCoverClassRepresentative] using
    alternatingSixSchurAlphaOneAutomorphism_classIndex_representative
      index

/-- The second canonical automorphism has the checked class action after
transport to the universal cover. -/
theorem
    alternatingSixUniversalCoverAlphaTwoAutomorphism_classIndex_representative
    (index : Fin 31) :
    alternatingSixUniversalCoverClassIndex
        (alternatingSixUniversalCoverAlphaTwoAutomorphism
          (alternatingSixUniversalCoverClassRepresentative index)) =
      alternatingSixSchurAlphaTwoClassIndexAction index := by
  simpa [alternatingSixUniversalCoverClassIndex,
    alternatingSixUniversalCoverClassRepresentative] using
    alternatingSixSchurAlphaTwoAutomorphism_classIndex_representative
      index

/-- The first checked coordinate automorphism has the displayed class
action on every element, not only on the chosen representatives. -/
theorem alternatingSixSchurAlphaOneAutomorphism_classIndex
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaOneAutomorphism coordinate) =
      alternatingSixSchurAlphaOneClassIndexAction
        (alternatingSixSchurClassIndex coordinate) := by
  have himage :=
    congrArg alternatingSixSchurAlphaOneAutomorphism
      (alternatingSixSchurClassConjugator_spec coordinate)
  simp only [map_mul, map_inv] at himage
  calc
    alternatingSixSchurClassIndex
          (alternatingSixSchurAlphaOneAutomorphism coordinate) =
        alternatingSixSchurClassIndex
          (alternatingSixSchurAlphaOneAutomorphism
              (alternatingSixSchurClassConjugator coordinate) *
            alternatingSixSchurAlphaOneAutomorphism
              (alternatingSixSchurClassRepresentative
                (alternatingSixSchurClassIndex coordinate)) *
            (alternatingSixSchurAlphaOneAutomorphism
              (alternatingSixSchurClassConjugator coordinate))⁻¹) :=
      congrArg alternatingSixSchurClassIndex himage.symm
    _ =
        alternatingSixSchurClassIndex
          (alternatingSixSchurAlphaOneAutomorphism
            (alternatingSixSchurClassRepresentative
              (alternatingSixSchurClassIndex coordinate))) :=
      alternatingSixSchurClassIndex_conjugation_invariant _ _
    _ =
        alternatingSixSchurAlphaOneClassIndexAction
          (alternatingSixSchurClassIndex coordinate) :=
      alternatingSixSchurAlphaOneAutomorphism_classIndex_representative _

/-- The second checked coordinate automorphism has the displayed class
action on every element, not only on the chosen representatives. -/
theorem alternatingSixSchurAlphaTwoAutomorphism_classIndex
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoAutomorphism coordinate) =
      alternatingSixSchurAlphaTwoClassIndexAction
        (alternatingSixSchurClassIndex coordinate) := by
  have himage :=
    congrArg alternatingSixSchurAlphaTwoAutomorphism
      (alternatingSixSchurClassConjugator_spec coordinate)
  simp only [map_mul, map_inv] at himage
  calc
    alternatingSixSchurClassIndex
          (alternatingSixSchurAlphaTwoAutomorphism coordinate) =
        alternatingSixSchurClassIndex
          (alternatingSixSchurAlphaTwoAutomorphism
              (alternatingSixSchurClassConjugator coordinate) *
            alternatingSixSchurAlphaTwoAutomorphism
              (alternatingSixSchurClassRepresentative
                (alternatingSixSchurClassIndex coordinate)) *
            (alternatingSixSchurAlphaTwoAutomorphism
              (alternatingSixSchurClassConjugator coordinate))⁻¹) :=
      congrArg alternatingSixSchurClassIndex himage.symm
    _ =
        alternatingSixSchurClassIndex
          (alternatingSixSchurAlphaTwoAutomorphism
            (alternatingSixSchurClassRepresentative
              (alternatingSixSchurClassIndex coordinate))) :=
      alternatingSixSchurClassIndex_conjugation_invariant _ _
    _ =
        alternatingSixSchurAlphaTwoClassIndexAction
          (alternatingSixSchurClassIndex coordinate) :=
      alternatingSixSchurAlphaTwoAutomorphism_classIndex_representative _

/-- Transported form of the first class action on every universal-cover
element. -/
theorem
    alternatingSixUniversalCoverAlphaOneAutomorphism_classIndex
    (x : universalCover) :
    alternatingSixUniversalCoverClassIndex
        (alternatingSixUniversalCoverAlphaOneAutomorphism x) =
      alternatingSixSchurAlphaOneClassIndexAction
        (alternatingSixUniversalCoverClassIndex x) := by
  obtain ⟨coordinate, rfl⟩ :=
    alternatingSixSchurCoordinatesEquivUniversalCover.surjective x
  simpa [alternatingSixUniversalCoverClassIndex] using
    alternatingSixSchurAlphaOneAutomorphism_classIndex
      coordinate

/-- Transported form of the second class action on every universal-cover
element. -/
theorem
    alternatingSixUniversalCoverAlphaTwoAutomorphism_classIndex
    (x : universalCover) :
    alternatingSixUniversalCoverClassIndex
        (alternatingSixUniversalCoverAlphaTwoAutomorphism x) =
      alternatingSixSchurAlphaTwoClassIndexAction
        (alternatingSixUniversalCoverClassIndex x) := by
  obtain ⟨coordinate, rfl⟩ :=
    alternatingSixSchurCoordinatesEquivUniversalCover.surjective x
  simpa [alternatingSixUniversalCoverClassIndex] using
    alternatingSixSchurAlphaTwoAutomorphism_classIndex
      coordinate

/-- The first checked automorphism is not inner. -/
theorem alternatingSixUniversalCoverAlphaOneOuterClass_ne_one :
    alternatingSixUniversalCoverAlphaOneOuterClass ≠ 1 := by
  intro houter
  have houter' :
      QuotientGroup.mk'
          (InnerAutomorphismSubgroup universalCover)
          alternatingSixUniversalCoverAlphaOneAutomorphism =
        QuotientGroup.mk'
          (InnerAutomorphismSubgroup universalCover)
          (1 : MulAut universalCover) := by
    simpa [alternatingSixUniversalCoverAlphaOneOuterClass] using
      houter
  have hclass :=
    conjugationInvariant_apply_eq_of_outer_eq
      alternatingSixUniversalCoverClassIndex
      alternatingSixUniversalCoverClassIndex_conjugation_invariant
      houter'
      (alternatingSixUniversalCoverClassRepresentative 1)
  have haction :
      alternatingSixSchurAlphaOneClassIndexAction 1 ≠
        (1 : Fin 31) := by
    decide
  apply haction
  calc
    alternatingSixSchurAlphaOneClassIndexAction 1 =
        alternatingSixUniversalCoverClassIndex
          (alternatingSixUniversalCoverAlphaOneAutomorphism
            (alternatingSixUniversalCoverClassRepresentative 1)) :=
      (alternatingSixUniversalCoverAlphaOneAutomorphism_classIndex_representative
        1).symm
    _ =
        alternatingSixUniversalCoverClassIndex
          ((1 : MulAut universalCover)
            (alternatingSixUniversalCoverClassRepresentative 1)) :=
      hclass
    _ = 1 := by
      simpa [alternatingSixUniversalCoverClassRepresentative,
        alternatingSixUniversalCoverClassIndex] using
        (alternatingSixSchurClassIndex_representative 1)

/-- The second checked automorphism is not inner. -/
theorem alternatingSixUniversalCoverAlphaTwoOuterClass_ne_one :
    alternatingSixUniversalCoverAlphaTwoOuterClass ≠ 1 := by
  intro houter
  have houter' :
      QuotientGroup.mk'
          (InnerAutomorphismSubgroup universalCover)
          alternatingSixUniversalCoverAlphaTwoAutomorphism =
        QuotientGroup.mk'
          (InnerAutomorphismSubgroup universalCover)
          (1 : MulAut universalCover) := by
    simpa [alternatingSixUniversalCoverAlphaTwoOuterClass] using
      houter
  have hclass :=
    conjugationInvariant_apply_eq_of_outer_eq
      alternatingSixUniversalCoverClassIndex
      alternatingSixUniversalCoverClassIndex_conjugation_invariant
      houter'
      (alternatingSixUniversalCoverClassRepresentative 1)
  have haction :
      alternatingSixSchurAlphaTwoClassIndexAction 1 ≠
        (1 : Fin 31) := by
    decide
  apply haction
  calc
    alternatingSixSchurAlphaTwoClassIndexAction 1 =
        alternatingSixUniversalCoverClassIndex
          (alternatingSixUniversalCoverAlphaTwoAutomorphism
            (alternatingSixUniversalCoverClassRepresentative 1)) :=
      (alternatingSixUniversalCoverAlphaTwoAutomorphism_classIndex_representative
        1).symm
    _ =
        alternatingSixUniversalCoverClassIndex
          ((1 : MulAut universalCover)
            (alternatingSixUniversalCoverClassRepresentative 1)) :=
      hclass
    _ = 1 := by
      simpa [alternatingSixUniversalCoverClassRepresentative,
        alternatingSixUniversalCoverClassIndex] using
        (alternatingSixSchurClassIndex_representative 1)

/-- The two checked automorphisms represent different outer classes. -/
theorem alternatingSixUniversalCoverAlphaOneOuterClass_ne_alphaTwo :
    alternatingSixUniversalCoverAlphaOneOuterClass ≠
      alternatingSixUniversalCoverAlphaTwoOuterClass := by
  intro houter
  have hclass :=
    conjugationInvariant_apply_eq_of_outer_eq
      alternatingSixUniversalCoverClassIndex
      alternatingSixUniversalCoverClassIndex_conjugation_invariant
      houter
      (alternatingSixUniversalCoverClassRepresentative 9)
  have haction :
      alternatingSixSchurAlphaOneClassIndexAction 9 ≠
        alternatingSixSchurAlphaTwoClassIndexAction 9 := by
    decide
  apply haction
  calc
    alternatingSixSchurAlphaOneClassIndexAction 9 =
        alternatingSixUniversalCoverClassIndex
          (alternatingSixUniversalCoverAlphaOneAutomorphism
            (alternatingSixUniversalCoverClassRepresentative 9)) :=
      (alternatingSixUniversalCoverAlphaOneAutomorphism_classIndex_representative
        9).symm
    _ =
        alternatingSixUniversalCoverClassIndex
          (alternatingSixUniversalCoverAlphaTwoAutomorphism
            (alternatingSixUniversalCoverClassRepresentative 9)) :=
      hclass
    _ = alternatingSixSchurAlphaTwoClassIndexAction 9 :=
      alternatingSixUniversalCoverAlphaTwoAutomorphism_classIndex_representative
        9

/-- The product of the two checked outer classes is nonidentity. -/
theorem
    alternatingSixUniversalCoverAlphaOneOuterClass_mul_alphaTwo_ne_one :
    alternatingSixUniversalCoverAlphaOneOuterClass *
        alternatingSixUniversalCoverAlphaTwoOuterClass ≠
      1 := by
  intro houter
  have houter' :
      QuotientGroup.mk'
          (InnerAutomorphismSubgroup universalCover)
          (alternatingSixUniversalCoverAlphaOneAutomorphism *
            alternatingSixUniversalCoverAlphaTwoAutomorphism) =
        QuotientGroup.mk'
          (InnerAutomorphismSubgroup universalCover)
          (1 : MulAut universalCover) := by
    simpa [alternatingSixUniversalCoverAlphaOneOuterClass,
      alternatingSixUniversalCoverAlphaTwoOuterClass,
      map_mul] using houter
  have hclass :=
    conjugationInvariant_apply_eq_of_outer_eq
      alternatingSixUniversalCoverClassIndex
      alternatingSixUniversalCoverClassIndex_conjugation_invariant
      houter'
      (alternatingSixUniversalCoverClassRepresentative 9)
  have haction :
      alternatingSixSchurAlphaOneClassIndexAction
          (alternatingSixSchurAlphaTwoClassIndexAction 9) ≠
        (9 : Fin 31) := by
    decide
  apply haction
  calc
    alternatingSixSchurAlphaOneClassIndexAction
          (alternatingSixSchurAlphaTwoClassIndexAction 9) =
        alternatingSixUniversalCoverClassIndex
          (alternatingSixUniversalCoverAlphaOneAutomorphism
            (alternatingSixUniversalCoverAlphaTwoAutomorphism
              (alternatingSixUniversalCoverClassRepresentative 9))) := by
      rw [
        alternatingSixUniversalCoverAlphaOneAutomorphism_classIndex,
        alternatingSixUniversalCoverAlphaTwoAutomorphism_classIndex,
        alternatingSixUniversalCoverClassIndex_representative
      ]
    _ =
        alternatingSixUniversalCoverClassIndex
          ((alternatingSixUniversalCoverAlphaOneAutomorphism *
              alternatingSixUniversalCoverAlphaTwoAutomorphism)
            (alternatingSixUniversalCoverClassRepresentative 9)) :=
      rfl
    _ =
        alternatingSixUniversalCoverClassIndex
          ((1 : MulAut universalCover)
            (alternatingSixUniversalCoverClassRepresentative 9)) :=
      hclass
    _ = 9 := by
      simpa [alternatingSixUniversalCoverClassRepresentative,
        alternatingSixUniversalCoverClassIndex] using
        (alternatingSixSchurClassIndex_representative 9)

/-- The four explicitly separated outer classes give a kernel-checked lower
bound on the outer quotient's cardinality. -/
theorem
    four_le_natCard_alternatingSixUniversalCoverOuterQuotient :
    4 ≤ Nat.card outerQuotient :=
  four_le_natCard_of_ne_one_of_ne_of_mul_ne_one
    alternatingSixUniversalCoverAlphaOneOuterClass_ne_one
    alternatingSixUniversalCoverAlphaTwoOuterClass_ne_one
    alternatingSixUniversalCoverAlphaOneOuterClass_ne_alphaTwo
    alternatingSixUniversalCoverAlphaOneOuterClass_mul_alphaTwo_ne_one

/-- The exact remaining classification boundary: there are at most four
outer automorphism classes of the universal cover.  Together with the
proved lower bound, this yields cardinality exactly four. -/
def AlternatingSixUniversalCoverOuterQuotientCardinalityAtMostFour :
    Prop :=
  Nat.card outerQuotient ≤ 4

/-- The classification upper bound and the four separated checked classes
give exact outer-quotient cardinality four. -/
theorem
    natCard_alternatingSixUniversalCoverOuterQuotient_eq_four
    (hbound :
      AlternatingSixUniversalCoverOuterQuotientCardinalityAtMostFour) :
    Nat.card outerQuotient = 4 :=
  Nat.le_antisymm hbound
    four_le_natCard_alternatingSixUniversalCoverOuterQuotient

/-- The minimal cardinality upper-bound input implies that the two checked
outer classes generate the full quotient. -/
theorem
    alternatingSixUniversalCover_outerQuotientGeneration_of_cardinalityAtMostFour
    (hbound :
      AlternatingSixUniversalCoverOuterQuotientCardinalityAtMostFour) :
    AlternatingSixUniversalCoverOuterQuotientGeneration := by
  rw [AlternatingSixUniversalCoverOuterQuotientGeneration,
    alternatingSixUniversalCoverOuterQuotientGenerators]
  exact
    closure_pair_eq_top_of_natCard_eq_four
      (natCard_alternatingSixUniversalCoverOuterQuotient_eq_four
        hbound)
      alternatingSixUniversalCoverAlphaOneOuterClass_ne_one
      alternatingSixUniversalCoverAlphaTwoOuterClass_ne_one
      alternatingSixUniversalCoverAlphaOneOuterClass_ne_alphaTwo

/-- Under the minimal classification upper bound, the two adjusted
representatives generate every fixed Sylow automorphism stabilizer modulo
the exact normalizer's inner action. -/
theorem
    alternatingSixUniversalCover_adjusted_generatesModuloInner_of_cardinalityAtMostFour
    (p : ℕ) [Fact p.Prime]
    (hbound :
      AlternatingSixUniversalCoverOuterQuotientCardinalityAtMostFour) :
    GeneratesSylowAutStabilizerModuloInner
      (alternatingSixUniversalCoverSylow p)
      (alternatingSixUniversalCoverSylowAdjustedOuterGenerators p) :=
  alternatingSixUniversalCover_adjusted_generatesSylowAutStabilizerModuloInner
    p
    (alternatingSixUniversalCover_outerQuotientGeneration_of_cardinalityAtMostFour
      hbound)

end InductiveMcKay
end McKayConjecture
