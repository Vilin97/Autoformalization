/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.TwoPointCenterScalar
import McKayConjecture.InductiveMcKay.ExactNormalizerInnerProjectiveCompatibility
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveGeneralLinearScalarAlignment
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoInnerExtensions

/-!
# Symmetric-square projective rows at `p = 2`

The two degree-three rows are exchanged by the outer automorphism, hence
their inertia groups are covered by the exact Sylow-two normalizer.  Both
matched characters are trivial on the central kernel `{±1}`.  A normalized
choice of inner lift therefore gives identical projective factors and
central scalars.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeTwoForSymmetricSquareProjectiveRows :
    Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The explicit equivariant McKay equivalence at `p = 2`. -/
def specialLinearTwoFiveTwoEquivariantMcKayEquiv :
    EquivariantMcKayEquiv specialLinearTwoFiveSylowTwo :=
  specialLinearTwoFiveTwoCharacterTableCompletion.toEquivariantMcKayEquiv

/-- Every element of a symmetric-square inertia group has an exact
normalizer implementer. -/
theorem specialLinearTwoFiveTwoSymmetricSquareStabilizer_exists_innerLift
    (k : Fin 2)
    (a :
      PPrimeCharacterStabilizer
        specialLinearTwoFiveSylowTwo
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k))) :
    ∃ g : SpecialLinearTwoFiveSylowTwoNormalizer,
      a.1.1 = MulAut.conj g.1 := by
  obtain ⟨g, hg⟩ :=
    specialLinearTwoFiveTwo_innerCharacterStabilizer_surjective k a
  refine ⟨g, ?_⟩
  exact
    (congrArg
      (fun b :
        PPrimeCharacterStabilizer
          specialLinearTwoFiveSylowTwo
          (specialLinearTwoFiveTwoPPrimeCharacterEquiv
            (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k)) ↦
        b.1.1) hg).symm

/-- A normalized set-theoretic implementer lift. -/
def specialLinearTwoFiveTwoSymmetricSquareStabilizerLift
    (k : Fin 2)
    (a :
      PPrimeCharacterStabilizer
        specialLinearTwoFiveSylowTwo
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k))) :
    SpecialLinearTwoFiveSylowTwoNormalizer := by
  classical
  exact
    if ha : a = 1 then 1
    else
      Classical.choose
        (specialLinearTwoFiveTwoSymmetricSquareStabilizer_exists_innerLift
          k a)

@[simp]
theorem specialLinearTwoFiveTwoSymmetricSquareStabilizerLift_one
    (k : Fin 2) :
    specialLinearTwoFiveTwoSymmetricSquareStabilizerLift k 1 = 1 := by
  simp [specialLinearTwoFiveTwoSymmetricSquareStabilizerLift]

theorem specialLinearTwoFiveTwoSymmetricSquareStabilizerLift_spec
    (k : Fin 2)
    (a :
      PPrimeCharacterStabilizer
        specialLinearTwoFiveSylowTwo
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k))) :
    PPrimeCharacterStabilizer.ambientAction a =
      MulAut.conj
        (specialLinearTwoFiveTwoSymmetricSquareStabilizerLift k a).1 := by
  by_cases ha : a = 1
  · subst a
    simp
  · change
      a.1.1 =
        MulAut.conj
          (specialLinearTwoFiveTwoSymmetricSquareStabilizerLift k a).1
    rw [specialLinearTwoFiveTwoSymmetricSquareStabilizerLift,
      dif_neg ha]
    exact
      Classical.choose_spec
        (specialLinearTwoFiveTwoSymmetricSquareStabilizer_exists_innerLift
          k a)

theorem specialLinearTwoFiveTwo_mem_center_eq_one_or_negOne
    (z : SpecialLinearTwoFive)
    (hz : z ∈ Subgroup.center SpecialLinearTwoFive) :
    z = 1 ∨ z = -1 :=
  specialLinearTwoFive_center_eq_one_or_neg_one ⟨z, hz⟩

theorem specialLinearTwoFiveTwoNormalizer_mem_center_eq_one_or_negOne
    (z : SpecialLinearTwoFiveSylowTwoNormalizer)
    (hz :
      z ∈ Subgroup.center SpecialLinearTwoFiveSylowTwoNormalizer) :
    z = 1 ∨
      z =
        specialLinearTwoFiveCentralNegOneNormalizer
          specialLinearTwoFiveSylowTwo := by
  rcases
      specialLinearTwoFiveTwoNormalizer_center_eq_one_or_neg_one
        ⟨z, hz⟩ with hz_one | hz_neg
  · left
    apply Subtype.ext
    exact hz_one
  · right
    apply Subtype.ext
    simpa using hz_neg

theorem specialLinearTwoFiveTwoSymmetricSquareAmbient_values_neg_one
    (k : Fin 2) :
    (specialLinearTwoFiveTwoPPrimeCharacterEquiv
      (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k)).1.values
        (-1) =
      ((specialLinearTwoFiveTwoPPrimeCharacterEquiv
        (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k)).1.degree :
        ℂ) := by
  let χ :=
    (specialLinearTwoFiveTwoPPrimeCharacterEquiv
      (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k)).1
  exact
    (IrreducibleCharacter.trivialOn_iff_values_eq_degree
      χ (Subgroup.center SpecialLinearTwoFive) le_rfl).mp
        (specialLinearTwoFiveTwoSymmetricSquare_trivialOn_center k)
        ⟨-1, by
          rw [Subgroup.mem_center_iff]
          intro g
          simp⟩

theorem specialLinearTwoFiveTwoSymmetricSquareLocal_values_neg_one
    (k : Fin 2) :
    (specialLinearTwoFiveTwoEquivariantMcKayEquiv
      (specialLinearTwoFiveTwoPPrimeCharacterEquiv
        (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k))).1.values
          (specialLinearTwoFiveCentralNegOneNormalizer
            specialLinearTwoFiveSylowTwo) =
      ((specialLinearTwoFiveTwoEquivariantMcKayEquiv
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k))).1.degree :
        ℂ) := by
  let ψ :=
    (specialLinearTwoFiveTwoEquivariantMcKayEquiv
      (specialLinearTwoFiveTwoPPrimeCharacterEquiv
        (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k))).1
  exact
    (IrreducibleCharacter.trivialOn_iff_values_eq_degree
      ψ
      (Subgroup.center SpecialLinearTwoFiveSylowTwoNormalizer)
      le_rfl).mp
        (specialLinearTwoFiveTwoMatchedLinear_trivialOn_center k)
        ⟨specialLinearTwoFiveCentralNegOneNormalizer
            specialLinearTwoFiveSylowTwo,
          by
            rw [Subgroup.mem_center_iff]
            intro n
            apply Subtype.ext
            simp⟩

/-- The two degree-three rows satisfy the projective compatibility
condition.  Their inertia groups are inner and both central actions are
trivial. -/
theorem specialLinearTwoFiveTwoSymmetricSquareRow_tripleCompatible
    (k : Fin 2) :
    specialLinearTwoFiveTwoEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence.TripleCompatible
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k)) := by
  let e := specialLinearTwoFiveTwoEquivariantMcKayEquiv
  let χ :=
    specialLinearTwoFiveTwoPPrimeCharacterEquiv
      (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k)
  apply
    e.tripleCompatible_of_innerNormalizerLift χ
      (specialLinearTwoFiveTwoSymmetricSquareStabilizerLift k)
      (specialLinearTwoFiveTwoSymmetricSquareStabilizerLift_one k)
      (specialLinearTwoFiveTwoSymmetricSquareStabilizerLift_spec k)
      (fun _ : SpecialLinearTwoFive => 1)
  · intro z hz
    apply
      irreducibleCharacter_realizationAction_eq_of_twoPointCenter
        χ.1 (-1) (fun _ : SpecialLinearTwoFive => 1)
        specialLinearTwoFiveTwo_mem_center_eq_one_or_negOne
        (by simp)
        (by
          simpa using
            specialLinearTwoFiveTwoSymmetricSquareAmbient_values_neg_one k)
        z hz
  · intro z hz
    apply
      irreducibleCharacter_realizationAction_eq_of_twoPointCenter
        (e χ).1
        (specialLinearTwoFiveCentralNegOneNormalizer
          specialLinearTwoFiveSylowTwo)
        (fun _ : SpecialLinearTwoFiveSylowTwoNormalizer => 1)
        specialLinearTwoFiveTwoNormalizer_mem_center_eq_one_or_negOne
        (by simp)
        (by
          simpa using
            specialLinearTwoFiveTwoSymmetricSquareLocal_values_neg_one k)
        z hz

/-- Packaged exact-normalizer projective data for either degree-three
row. -/
def specialLinearTwoFiveTwoSymmetricSquareProjectiveRowData
    (k : Fin 2) :
    ExactNormalizerProjectiveRowData
      specialLinearTwoFiveTwoEquivariantMcKayEquiv
      (specialLinearTwoFiveTwoPPrimeCharacterEquiv
        (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k)) :=
  ExactNormalizerProjectiveRowData.ofTripleCompatible
    specialLinearTwoFiveTwoEquivariantMcKayEquiv
    (specialLinearTwoFiveTwoPPrimeCharacterEquiv
      (specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k))
    (specialLinearTwoFiveTwoSymmetricSquareRow_tripleCompatible k)

end InductiveMcKay
end McKayConjecture
