/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurFiveNormalizerModel
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterAutomorphismData

/-!
# Audited outer automorphisms of the sixfold cover of `A₆`

This file constructs and checks the inverse presentation endomorphism for
the second assignment from `AlternatingSixSchurOuterAutomorphismData`.
The inverse coordinates are independently recorded in the reproducible GAP
audit.  The companion `AlternatingSixSchurOuterAutomorphismChecks` module
checks both inverse identities and packages the resulting automorphisms.

The first chosen representative has order two.  The second has order eight:
the involution seen on character rows is its image in the outer
automorphism group, not an equality of the representatives constructed
here.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- Audited images of the six presentation generators under the inverse
of the chosen `alpha2` representative. -/
def alternatingSixSchurAlphaTwoInverseGeneratorCoordinates :
    Fin 6 → AlternatingSixSchurCoordinates :=
  ![
    { state := 355, central := 2 },
    { state := 345, central := 0 },
    { state := 0, central := 5 },
    { state := 0, central := 3 },
    { state := 0, central := 1 },
    { state := 0, central := 5 }
  ]

/-- Evaluation identifies the six audited source coordinates with the six
generators of the abstract presentation. -/
theorem alternatingSixSchurAuditedPresentationGenerator_evaluate
    (i : Fin 6) :
    AlternatingSixSchurCoordinates.evaluate
        (alternatingSixSchurAuditedPresentationGeneratorCoordinates i) =
      alternatingSixSchurPresentedGenerator i := by
  fin_cases i
  · rfl
  · rfl
  · change
      alternatingSixSchurWord [] *
          AlternatingSixSchurCoordinates.centralValue 1 =
        alternatingSixSchurPresentedK 0
    rw [alternatingSixSchurWord_nil, one_mul]
    simpa [AlternatingSixSchurCoordinates.centralValue,
      alternatingSixSchurPresentedK] using
        QuaternionGroup.zmodPower_natCast
          (alternatingSixSchurPresentedK 0)
          alternatingSixSchurPresentedK0_pow_six 1
  · change
      alternatingSixSchurWord [] *
          AlternatingSixSchurCoordinates.centralValue 3 =
        alternatingSixSchurPresentedK 1
    rw [alternatingSixSchurWord_nil, one_mul,
      alternatingSixSchurPresentedK1_eq_k0_pow_three]
    simpa [AlternatingSixSchurCoordinates.centralValue,
      alternatingSixSchurFiveCentral] using
        QuaternionGroup.zmodPower_natCast
          (alternatingSixSchurPresentedK 0)
          alternatingSixSchurPresentedK0_pow_six 3
  · change
      alternatingSixSchurWord [] *
          AlternatingSixSchurCoordinates.centralValue 5 =
        alternatingSixSchurPresentedK 2
    rw [alternatingSixSchurWord_nil, one_mul,
      alternatingSixSchurPresentedK2_eq_k0_inv]
    change
      AlternatingSixSchurCoordinates.centralValue (-1) =
        alternatingSixSchurFiveCentral⁻¹
    rw [AlternatingSixSchurCoordinates.centralValue_neg]
    simpa [AlternatingSixSchurCoordinates.centralValue,
      alternatingSixSchurFiveCentral] using
        QuaternionGroup.zmodPower_natCast
          (alternatingSixSchurPresentedK 0)
          alternatingSixSchurPresentedK0_pow_six 1
  · change
      alternatingSixSchurWord [] *
          AlternatingSixSchurCoordinates.centralValue 1 =
        alternatingSixSchurPresentedK 3
    rw [alternatingSixSchurWord_nil, one_mul,
      alternatingSixSchurPresentedK3_eq_k0]
    simpa [AlternatingSixSchurCoordinates.centralValue,
      alternatingSixSchurFiveCentral] using
        QuaternionGroup.zmodPower_natCast
          (alternatingSixSchurPresentedK 0)
          alternatingSixSchurPresentedK0_pow_six 1

/-- Extensionality for homomorphisms out of the coordinate model, reduced
to its six audited presentation generators. -/
theorem alternatingSixSchurCoordinates_monoidHom_ext
    {H : Type*} [Group H]
    (f g : AlternatingSixSchurCoordinates →* H)
    (hgenerator :
      ∀ i : Fin 6,
        f (alternatingSixSchurAuditedPresentationGeneratorCoordinates i) =
          g (alternatingSixSchurAuditedPresentationGeneratorCoordinates i)) :
    f = g := by
  have hpreimage
      (i : Fin 6) :
      AlternatingSixSchurCoordinates.mulEquivPresentedGroup.symm
          (alternatingSixSchurPresentedGenerator i) =
        alternatingSixSchurAuditedPresentationGeneratorCoordinates i := by
    apply
      AlternatingSixSchurCoordinates.mulEquivPresentedGroup.injective
    rw [MulEquiv.apply_symm_apply,
      AlternatingSixSchurCoordinates.mulEquivPresentedGroup_apply]
    exact
      (alternatingSixSchurAuditedPresentationGenerator_evaluate i).symm
  have hcomp :
      f.comp
          AlternatingSixSchurCoordinates.mulEquivPresentedGroup.symm.toMonoidHom =
        g.comp
          AlternatingSixSchurCoordinates.mulEquivPresentedGroup.symm.toMonoidHom := by
    apply PresentedGroup.ext
    intro i
    change
      f (AlternatingSixSchurCoordinates.mulEquivPresentedGroup.symm
          (alternatingSixSchurPresentedGenerator i)) =
        g (AlternatingSixSchurCoordinates.mulEquivPresentedGroup.symm
          (alternatingSixSchurPresentedGenerator i))
    rw [hpreimage]
    exact hgenerator i
  apply MonoidHom.ext
  intro coordinate
  have hcoordinate :=
    DFunLike.congr_fun hcomp
      (AlternatingSixSchurCoordinates.mulEquivPresentedGroup coordinate)
  change
    f (AlternatingSixSchurCoordinates.mulEquivPresentedGroup.symm
        (AlternatingSixSchurCoordinates.mulEquivPresentedGroup coordinate)) =
      g (AlternatingSixSchurCoordinates.mulEquivPresentedGroup.symm
        (AlternatingSixSchurCoordinates.mulEquivPresentedGroup coordinate))
      at hcoordinate
  simpa only [MulEquiv.symm_apply_apply] using hcoordinate

@[simp]
theorem alternatingSixSchurAlphaOneEndomorphism_generator
    (i : Fin 6) :
    alternatingSixSchurAlphaOneEndomorphism
        (alternatingSixSchurAuditedPresentationGeneratorCoordinates i) =
      alternatingSixSchurAlphaOneGeneratorCoordinates i := by
  change
    alternatingSixSchurAlphaOneRepresentationData.toMonoidHom
        (AlternatingSixSchurCoordinates.evaluate
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates i)) =
      alternatingSixSchurAlphaOneGeneratorCoordinates i
  rw [
    alternatingSixSchurAuditedPresentationGenerator_evaluate,
    AlternatingSixSchurRepresentationData.toMonoidHom_generator]
  rfl

@[simp]
theorem alternatingSixSchurAlphaTwoEndomorphism_generator
    (i : Fin 6) :
    alternatingSixSchurAlphaTwoEndomorphism
        (alternatingSixSchurAuditedPresentationGeneratorCoordinates i) =
      alternatingSixSchurAlphaTwoGeneratorCoordinates i := by
  change
    alternatingSixSchurAlphaTwoRepresentationData.toMonoidHom
        (AlternatingSixSchurCoordinates.evaluate
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates i)) =
      alternatingSixSchurAlphaTwoGeneratorCoordinates i
  rw [
    alternatingSixSchurAuditedPresentationGenerator_evaluate,
    AlternatingSixSchurRepresentationData.toMonoidHom_generator]
  rfl

/-- Three checked multiplication steps suffice to certify a fourth power. -/
theorem pow_four_eq_of_mul_chain
    {G : Type*} [Group G]
    (x xTwo xThree xFour : G)
    (hTwo : x * x = xTwo)
    (hThree : xTwo * x = xThree)
    (hFour : xThree * x = xFour) :
    x ^ 4 = xFour := by
  calc
    x ^ 4 = ((x * x) * x) * x := by
      simp only [pow_succ, pow_zero, one_mul]
    _ = (xTwo * x) * x := by rw [hTwo]
    _ = xThree * x := by rw [hThree]
    _ = xFour := hFour

private theorem alphaTwoInverse_generator_zero_square :
    alternatingSixSchurAuditedCoordinate 355 2 *
        alternatingSixSchurAuditedCoordinate 355 2 =
      alternatingSixSchurAuditedCoordinate 0 5 := by
  calc
    alternatingSixSchurAuditedCoordinate 355 2 *
          alternatingSixSchurAuditedCoordinate 355 2 =
        alternatingSixSchurAuditedCoordinate 355 2 *
          (alternatingSixSchurAuditedCoordinate 75 0 *
            alternatingSixSchurAuditedCoordinate 106 2) := by
              congr 1
    _ =
        (alternatingSixSchurAuditedCoordinate 355 2 *
            alternatingSixSchurAuditedCoordinate 75 0) *
          alternatingSixSchurAuditedCoordinate 106 2 := by
            rw [mul_assoc]
    _ =
        alternatingSixSchurAuditedCoordinate 90 0 *
          alternatingSixSchurAuditedCoordinate 106 2 := by
            rw [show
              alternatingSixSchurAuditedCoordinate 355 2 *
                  alternatingSixSchurAuditedCoordinate 75 0 =
                alternatingSixSchurAuditedCoordinate 90 0 by decide]
    _ = alternatingSixSchurAuditedCoordinate 0 5 := by decide

private theorem alphaTwoInverse_generator_one_square :
    alternatingSixSchurAuditedCoordinate 345 0 *
        alternatingSixSchurAuditedCoordinate 345 0 =
      alternatingSixSchurAuditedCoordinate 32 0 := by
  calc
    alternatingSixSchurAuditedCoordinate 345 0 *
          alternatingSixSchurAuditedCoordinate 345 0 =
        alternatingSixSchurAuditedCoordinate 345 0 *
          (alternatingSixSchurAuditedCoordinate 58 0 *
            alternatingSixSchurAuditedCoordinate 107 0) := by
              congr 1
    _ =
        (alternatingSixSchurAuditedCoordinate 345 0 *
            alternatingSixSchurAuditedCoordinate 58 0) *
          alternatingSixSchurAuditedCoordinate 107 0 := by
            rw [mul_assoc]
    _ =
        alternatingSixSchurAuditedCoordinate 88 0 *
          alternatingSixSchurAuditedCoordinate 107 0 := by
            rw [show
              alternatingSixSchurAuditedCoordinate 345 0 *
                  alternatingSixSchurAuditedCoordinate 58 0 =
                alternatingSixSchurAuditedCoordinate 88 0 by decide]
    _ = alternatingSixSchurAuditedCoordinate 32 0 := by decide

private theorem alphaTwoInverse_generator_one_cube :
    alternatingSixSchurAuditedCoordinate 32 0 *
        alternatingSixSchurAuditedCoordinate 345 0 =
      alternatingSixSchurAuditedCoordinate 343 5 := by
  calc
    alternatingSixSchurAuditedCoordinate 32 0 *
          alternatingSixSchurAuditedCoordinate 345 0 =
        alternatingSixSchurAuditedCoordinate 32 0 *
          (alternatingSixSchurAuditedCoordinate 58 0 *
            alternatingSixSchurAuditedCoordinate 107 0) := by
              congr 1
    _ =
        (alternatingSixSchurAuditedCoordinate 32 0 *
            alternatingSixSchurAuditedCoordinate 58 0) *
          alternatingSixSchurAuditedCoordinate 107 0 := by
            rw [mul_assoc]
    _ =
        alternatingSixSchurAuditedCoordinate 128 3 *
          alternatingSixSchurAuditedCoordinate 107 0 := by
            rw [show
              alternatingSixSchurAuditedCoordinate 32 0 *
                  alternatingSixSchurAuditedCoordinate 58 0 =
                alternatingSixSchurAuditedCoordinate 128 3 by decide]
    _ = alternatingSixSchurAuditedCoordinate 343 5 := by decide

private theorem alphaTwoInverse_generator_one_fourth :
    alternatingSixSchurAuditedCoordinate 343 5 *
        alternatingSixSchurAuditedCoordinate 345 0 =
      alternatingSixSchurAuditedCoordinate 0 3 := by
  calc
    alternatingSixSchurAuditedCoordinate 343 5 *
          alternatingSixSchurAuditedCoordinate 345 0 =
        alternatingSixSchurAuditedCoordinate 343 5 *
          (alternatingSixSchurAuditedCoordinate 58 0 *
            alternatingSixSchurAuditedCoordinate 107 0) := by
              congr 1
    _ =
        (alternatingSixSchurAuditedCoordinate 343 5 *
            alternatingSixSchurAuditedCoordinate 58 0) *
          alternatingSixSchurAuditedCoordinate 107 0 := by
            rw [mul_assoc]
    _ =
        alternatingSixSchurAuditedCoordinate 87 3 *
          alternatingSixSchurAuditedCoordinate 107 0 := by
            rw [show
              alternatingSixSchurAuditedCoordinate 343 5 *
                  alternatingSixSchurAuditedCoordinate 58 0 =
                alternatingSixSchurAuditedCoordinate 87 3 by decide]
    _ = alternatingSixSchurAuditedCoordinate 0 3 := by decide

private theorem alphaTwoInverse_generator_product :
    alternatingSixSchurAuditedCoordinate 355 2 *
        alternatingSixSchurAuditedCoordinate 345 0 =
      alternatingSixSchurAuditedCoordinate 126 3 := by
  calc
    alternatingSixSchurAuditedCoordinate 355 2 *
          alternatingSixSchurAuditedCoordinate 345 0 =
        alternatingSixSchurAuditedCoordinate 355 2 *
          (alternatingSixSchurAuditedCoordinate 58 0 *
            alternatingSixSchurAuditedCoordinate 107 0) := by
              congr 1
    _ =
        (alternatingSixSchurAuditedCoordinate 355 2 *
            alternatingSixSchurAuditedCoordinate 58 0) *
          alternatingSixSchurAuditedCoordinate 107 0 := by
            rw [mul_assoc]
    _ =
        alternatingSixSchurAuditedCoordinate 178 5 *
          alternatingSixSchurAuditedCoordinate 107 0 := by
            rw [show
              alternatingSixSchurAuditedCoordinate 355 2 *
                  alternatingSixSchurAuditedCoordinate 58 0 =
                alternatingSixSchurAuditedCoordinate 178 5 by decide]
    _ = alternatingSixSchurAuditedCoordinate 126 3 := by decide

theorem alternatingSixSchurAlphaTwoInverse_baseRelator_zero :
    alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 0 ^ 2 =
      alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 2 := by
  simpa [alternatingSixSchurAlphaTwoInverseGeneratorCoordinates,
    alternatingSixSchurAuditedCoordinate, pow_two] using
      alphaTwoInverse_generator_zero_square

theorem alternatingSixSchurAlphaTwoInverse_baseRelator_one :
    alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 1 ^ 4 =
      alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 3 := by
  change
    alternatingSixSchurAuditedCoordinate 345 0 ^ 4 =
      alternatingSixSchurAuditedCoordinate 0 3
  exact
    pow_four_eq_of_mul_chain
      (alternatingSixSchurAuditedCoordinate 345 0)
      (alternatingSixSchurAuditedCoordinate 32 0)
      (alternatingSixSchurAuditedCoordinate 343 5)
      (alternatingSixSchurAuditedCoordinate 0 3)
      alphaTwoInverse_generator_one_square
      alphaTwoInverse_generator_one_cube
      alphaTwoInverse_generator_one_fourth

theorem alternatingSixSchurAlphaTwoInverse_baseRelator_two :
    (alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 0 *
        alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 1) ^ 5 =
      alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 4 := by
  rw [show
    alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 0 *
        alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 1 =
      alternatingSixSchurAuditedCoordinate 126 3 by
        exact alphaTwoInverse_generator_product]
  exact
    pow_five_eq_of_mul_chain
      (alternatingSixSchurAuditedCoordinate 126 3)
      (alternatingSixSchurAuditedCoordinate 161 1)
      (alternatingSixSchurAuditedCoordinate 192 5)
      (alternatingSixSchurAuditedCoordinate 132 0)
      (alternatingSixSchurAuditedCoordinate 0 1)
      (by decide) (by decide) (by decide) (by decide)

theorem alternatingSixSchurAlphaTwoInverse_baseRelator_three :
    (alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 0 *
        alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 1 ^ 2) ^ 5 =
      alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 5 := by
  rw [show
    alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 1 ^ 2 =
      alternatingSixSchurAuditedCoordinate 32 0 by
        simpa [alternatingSixSchurAlphaTwoInverseGeneratorCoordinates,
          alternatingSixSchurAuditedCoordinate, pow_two] using
            alphaTwoInverse_generator_one_square]
  rw [show
    alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 0 *
        alternatingSixSchurAuditedCoordinate 32 0 =
      alternatingSixSchurAuditedCoordinate 168 4 by decide]
  exact
    pow_five_eq_of_mul_chain
      (alternatingSixSchurAuditedCoordinate 168 4)
      (alternatingSixSchurAuditedCoordinate 254 3)
      (alternatingSixSchurAuditedCoordinate 250 4)
      (alternatingSixSchurAuditedCoordinate 207 0)
      (alternatingSixSchurAuditedCoordinate 0 5)
      (by decide) (by decide) (by decide) (by decide)

/-- Lean verification that the audited inverse assignment for `alpha2`
satisfies every relation of the Schur-cover presentation. -/
def alternatingSixSchurAlphaTwoInverseRepresentationData :
    AlternatingSixSchurRepresentationData
      AlternatingSixSchurCoordinates where
  generator := alternatingSixSchurAlphaTwoInverseGeneratorCoordinates
  baseRelator_eq i := by
    fin_cases i
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using
          alternatingSixSchurAlphaTwoInverse_baseRelator_zero
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using
          alternatingSixSchurAlphaTwoInverse_baseRelator_one
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using
          alternatingSixSchurAlphaTwoInverse_baseRelator_two
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using
          alternatingSixSchurAlphaTwoInverse_baseRelator_three
  centrality i j := by
    fin_cases i
    all_goals
      apply alternatingSixSchurCoordinate_state_zero_commute
  lattice_one := by decide
  lattice_two := by decide

/-- The coordinate endomorphism induced by the audited inverse
generator assignment for `alpha2`. -/
def alternatingSixSchurAlphaTwoInverseEndomorphism :
    AlternatingSixSchurCoordinates →*
      AlternatingSixSchurCoordinates :=
  alternatingSixSchurAlphaTwoInverseRepresentationData.toMonoidHom.comp
    AlternatingSixSchurCoordinates.evaluateHom

@[simp]
theorem alternatingSixSchurAlphaTwoInverseEndomorphism_generator
    (i : Fin 6) :
    alternatingSixSchurAlphaTwoInverseEndomorphism
        (alternatingSixSchurAuditedPresentationGeneratorCoordinates i) =
      alternatingSixSchurAlphaTwoInverseGeneratorCoordinates i := by
  change
    alternatingSixSchurAlphaTwoInverseRepresentationData.toMonoidHom
        (AlternatingSixSchurCoordinates.evaluate
          (alternatingSixSchurAuditedPresentationGeneratorCoordinates i)) =
      alternatingSixSchurAlphaTwoInverseGeneratorCoordinates i
  rw [
    alternatingSixSchurAuditedPresentationGenerator_evaluate,
    AlternatingSixSchurRepresentationData.toMonoidHom_generator]
  rfl

/-- A list of individually checked right-multiplication steps.  Recording
the intermediate coordinates lets large finite calculations remain within
Lean's default recursion depth. -/
def alternatingSixSchurMultiplicationChain
    (start : AlternatingSixSchurCoordinates) :
    List
        (AlternatingSixSchurCoordinates ×
          AlternatingSixSchurCoordinates) →
      AlternatingSixSchurCoordinates → Prop
  | [], result => start = result
  | (factor, next) :: steps, result =>
      start * factor = next ∧
        alternatingSixSchurMultiplicationChain next steps result

theorem alternatingSixSchurMultiplicationChain_prod
    {start result : AlternatingSixSchurCoordinates}
    {steps :
      List
        (AlternatingSixSchurCoordinates ×
          AlternatingSixSchurCoordinates)}
    (hchain :
      alternatingSixSchurMultiplicationChain start steps result) :
    start * (steps.map Prod.fst).prod = result := by
  induction steps generalizing start with
  | nil =>
      simpa [alternatingSixSchurMultiplicationChain] using hchain
  | cons step steps ih =>
      rcases step with ⟨factor, next⟩
      change
        start * factor = next ∧
          alternatingSixSchurMultiplicationChain next steps result
        at hchain
      rw [List.map_cons, List.prod_cons, ← mul_assoc, hchain.1]
      exact ih hchain.2

/-- Multiplying the products of consecutive chunks is the same as
multiplying their flattened list of factors. -/
theorem list_prod_map_prod_eq_flatten_prod
    {G : Type*} [Monoid G]
    (chunks : List (List G)) :
    (chunks.map List.prod).prod = chunks.flatten.prod := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      simp only [List.map_cons, List.prod_cons, List.flatten_cons,
        List.prod_append, ih]

theorem alternatingSixSchurAlphaTwoInverse_apply_alphaTwo_generator_zero :
    alternatingSixSchurAlphaTwoInverseEndomorphism
        (alternatingSixSchurAlphaTwoGeneratorCoordinates 0) =
      alternatingSixSchurAuditedPresentationGeneratorCoordinates 0 := by
  let sourceFactors : List AlternatingSixSchurCoordinates := [
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1)⁻¹,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2]
  let imageChunks : List (List AlternatingSixSchurCoordinates) := [
    [alternatingSixSchurAuditedCoordinate 58 0,
      alternatingSixSchurAuditedCoordinate 107 0],
    [alternatingSixSchurAuditedCoordinate 75 0,
      alternatingSixSchurAuditedCoordinate 106 2],
    [alternatingSixSchurAuditedCoordinate 58 0,
      alternatingSixSchurAuditedCoordinate 107 0],
    [alternatingSixSchurAuditedCoordinate 58 0,
      alternatingSixSchurAuditedCoordinate 107 0],
    [alternatingSixSchurAuditedCoordinate 75 0,
      alternatingSixSchurAuditedCoordinate 106 2],
    [alternatingSixSchurAuditedCoordinate 58 0,
      alternatingSixSchurAuditedCoordinate 107 0],
    [alternatingSixSchurAuditedCoordinate 75 0,
      alternatingSixSchurAuditedCoordinate 106 2],
    [alternatingSixSchurAuditedCoordinate 57 0,
      alternatingSixSchurAuditedCoordinate 84 2],
    [alternatingSixSchurAuditedCoordinate 75 0,
      alternatingSixSchurAuditedCoordinate 106 2],
    [alternatingSixSchurAuditedCoordinate 58 0,
      alternatingSixSchurAuditedCoordinate 107 0],
    [alternatingSixSchurAuditedCoordinate 75 0,
      alternatingSixSchurAuditedCoordinate 106 2],
    [alternatingSixSchurAuditedCoordinate 58 0,
      alternatingSixSchurAuditedCoordinate 107 0],
    [alternatingSixSchurAuditedCoordinate 0 5]]
  let steps :
      List
        (AlternatingSixSchurCoordinates ×
          AlternatingSixSchurCoordinates) := [
    (alternatingSixSchurAuditedCoordinate 58 0,
      alternatingSixSchurAuditedCoordinate 58 0),
    (alternatingSixSchurAuditedCoordinate 107 0,
      alternatingSixSchurAuditedCoordinate 345 0),
    (alternatingSixSchurAuditedCoordinate 75 0,
      alternatingSixSchurAuditedCoordinate 188 0),
    (alternatingSixSchurAuditedCoordinate 106 2,
      alternatingSixSchurAuditedCoordinate 297 0),
    (alternatingSixSchurAuditedCoordinate 58 0,
      alternatingSixSchurAuditedCoordinate 77 1),
    (alternatingSixSchurAuditedCoordinate 107 0,
      alternatingSixSchurAuditedCoordinate 37 4),
    (alternatingSixSchurAuditedCoordinate 58 0,
      alternatingSixSchurAuditedCoordinate 115 4),
    (alternatingSixSchurAuditedCoordinate 107 0,
      alternatingSixSchurAuditedCoordinate 256 2),
    (alternatingSixSchurAuditedCoordinate 75 0,
      alternatingSixSchurAuditedCoordinate 266 3),
    (alternatingSixSchurAuditedCoordinate 106 2,
      alternatingSixSchurAuditedCoordinate 221 1),
    (alternatingSixSchurAuditedCoordinate 58 0,
      alternatingSixSchurAuditedCoordinate 18 1),
    (alternatingSixSchurAuditedCoordinate 107 0,
      alternatingSixSchurAuditedCoordinate 129 0),
    (alternatingSixSchurAuditedCoordinate 75 0,
      alternatingSixSchurAuditedCoordinate 12 4),
    (alternatingSixSchurAuditedCoordinate 106 2,
      alternatingSixSchurAuditedCoordinate 69 1),
    (alternatingSixSchurAuditedCoordinate 57 0,
      alternatingSixSchurAuditedCoordinate 73 3),
    (alternatingSixSchurAuditedCoordinate 84 2,
      alternatingSixSchurAuditedCoordinate 222 5),
    (alternatingSixSchurAuditedCoordinate 75 0,
      alternatingSixSchurAuditedCoordinate 33 3),
    (alternatingSixSchurAuditedCoordinate 106 2,
      alternatingSixSchurAuditedCoordinate 22 1),
    (alternatingSixSchurAuditedCoordinate 58 0,
      alternatingSixSchurAuditedCoordinate 8 0),
    (alternatingSixSchurAuditedCoordinate 107 0,
      alternatingSixSchurAuditedCoordinate 158 0),
    (alternatingSixSchurAuditedCoordinate 75 0,
      alternatingSixSchurAuditedCoordinate 175 4),
    (alternatingSixSchurAuditedCoordinate 106 2,
      alternatingSixSchurAuditedCoordinate 330 4),
    (alternatingSixSchurAuditedCoordinate 58 0,
      alternatingSixSchurAuditedCoordinate 72 2),
    (alternatingSixSchurAuditedCoordinate 107 0,
      alternatingSixSchurAuditedCoordinate 1 1),
    (alternatingSixSchurAuditedCoordinate 0 5,
      alternatingSixSchurAuditedCoordinate 1 0)]
  have hsource :
      sourceFactors.prod =
        alternatingSixSchurAlphaTwoGeneratorCoordinates 0 := by
    dsimp [sourceFactors]
    decide
  have hmapped :
      sourceFactors.map
          alternatingSixSchurAlphaTwoInverseEndomorphism =
        imageChunks.map List.prod := by
    simp only [sourceFactors, imageChunks, List.map_cons, List.map_nil,
      map_inv,
      alternatingSixSchurAlphaTwoInverseEndomorphism_generator]
    decide
  have hflatten :
      imageChunks.flatten = steps.map Prod.fst := by
    rfl
  have hchain :
      alternatingSixSchurMultiplicationChain 1 steps
        (alternatingSixSchurAuditedCoordinate 1 0) := by
    simp only [steps, alternatingSixSchurMultiplicationChain]
    repeat' apply And.intro
    all_goals decide
  calc
    alternatingSixSchurAlphaTwoInverseEndomorphism
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 0) =
        alternatingSixSchurAlphaTwoInverseEndomorphism
          sourceFactors.prod := congrArg
            alternatingSixSchurAlphaTwoInverseEndomorphism hsource.symm
    _ = (sourceFactors.map
          alternatingSixSchurAlphaTwoInverseEndomorphism).prod :=
      map_list_prod
        alternatingSixSchurAlphaTwoInverseEndomorphism sourceFactors
    _ = (imageChunks.map List.prod).prod := congrArg List.prod hmapped
    _ = imageChunks.flatten.prod :=
      list_prod_map_prod_eq_flatten_prod imageChunks
    _ = (steps.map Prod.fst).prod := congrArg List.prod hflatten
    _ = alternatingSixSchurAuditedCoordinate 1 0 := by
      simpa using
        alternatingSixSchurMultiplicationChain_prod hchain
    _ =
        alternatingSixSchurAuditedPresentationGeneratorCoordinates 0 := rfl

end GroupTheory
end McKayConjecture
