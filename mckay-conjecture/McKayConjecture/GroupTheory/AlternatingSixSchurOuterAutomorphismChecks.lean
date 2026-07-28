/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterAutomorphisms

/-!
# Inverse checks for the audited outer automorphisms of `6.A₆`

The long normal words occurring in the two audited assignments are split
into short factors.  Each finite multiplication below is checked at Lean's
default resource limits, one factor at a time.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

theorem monoidHom_apply_eq_of_alternatingSixSchurMultiplicationChain
    (f :
      AlternatingSixSchurCoordinates →*
        AlternatingSixSchurCoordinates)
    (sourceFactors : List AlternatingSixSchurCoordinates)
    (target : AlternatingSixSchurCoordinates)
    (imageChunks : List (List AlternatingSixSchurCoordinates))
    (steps :
      List
        (AlternatingSixSchurCoordinates ×
          AlternatingSixSchurCoordinates))
    (result : AlternatingSixSchurCoordinates)
    (hsource : sourceFactors.prod = target)
    (hmapped :
      sourceFactors.map f = imageChunks.map List.prod)
    (hflatten : imageChunks.flatten = steps.map Prod.fst)
    (hchain :
      alternatingSixSchurMultiplicationChain 1 steps result) :
    f target = result := by
  calc
    f target = f sourceFactors.prod :=
      congrArg f hsource.symm
    _ = (sourceFactors.map f).prod :=
      map_list_prod f sourceFactors
    _ = (imageChunks.map List.prod).prod :=
      congrArg List.prod hmapped
    _ = imageChunks.flatten.prod :=
      list_prod_map_prod_eq_flatten_prod imageChunks
    _ = (steps.map Prod.fst).prod :=
      congrArg List.prod hflatten
    _ = result := by
      simpa using
        alternatingSixSchurMultiplicationChain_prod hchain

/-- Any coordinate homomorphism which inverts `k₀` acts by negation on
all six central coordinates. -/
theorem alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
    (f :
      AlternatingSixSchurCoordinates →*
        AlternatingSixSchurCoordinates)
    (hgenerator :
      f (alternatingSixSchurAuditedPresentationGeneratorCoordinates 2) =
        alternatingSixSchurAuditedCoordinate 0 5)
    (central : Fin 6) :
    f
        (alternatingSixSchurAuditedCoordinate 0
          (ZMod.finEquiv 6 central)) =
      alternatingSixSchurAuditedCoordinate 0
        (-(ZMod.finEquiv 6 central)) := by
  fin_cases central
  · change f (alternatingSixSchurAuditedCoordinate 0 0) =
      alternatingSixSchurAuditedCoordinate 0 0
    change f 1 = 1
    exact map_one f
  · change
      f (alternatingSixSchurAuditedCoordinate 0 1) =
        alternatingSixSchurAuditedCoordinate 0 5
    simpa [alternatingSixSchurAuditedPresentationGeneratorCoordinates,
      alternatingSixSchurAuditedCoordinate] using hgenerator
  · change
      f (alternatingSixSchurAuditedCoordinate 0 2) =
        alternatingSixSchurAuditedCoordinate 0 4
    rw [show
      alternatingSixSchurAuditedCoordinate 0 2 =
        alternatingSixSchurAuditedPresentationGeneratorCoordinates 2 ^ 2 by
          decide,
      map_pow, hgenerator]
    decide
  · change
      f (alternatingSixSchurAuditedCoordinate 0 3) =
        alternatingSixSchurAuditedCoordinate 0 3
    rw [show
      alternatingSixSchurAuditedCoordinate 0 3 =
        alternatingSixSchurAuditedPresentationGeneratorCoordinates 2 ^ 3 by
          decide,
      map_pow, hgenerator]
    decide
  · change
      f (alternatingSixSchurAuditedCoordinate 0 4) =
        alternatingSixSchurAuditedCoordinate 0 2
    rw [show
      alternatingSixSchurAuditedCoordinate 0 4 =
        alternatingSixSchurAuditedPresentationGeneratorCoordinates 2 ^ 4 by
          decide,
      map_pow, hgenerator]
    decide
  · change
      f (alternatingSixSchurAuditedCoordinate 0 5) =
        alternatingSixSchurAuditedCoordinate 0 1
    rw [show
      alternatingSixSchurAuditedCoordinate 0 5 =
        alternatingSixSchurAuditedPresentationGeneratorCoordinates 2 ^ 5 by
          decide,
      map_pow, hgenerator]
    decide

theorem alternatingSixSchurAlphaTwoInverse_apply_alphaTwo_generator_one :
    alternatingSixSchurAlphaTwoInverseEndomorphism
        (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) =
      alternatingSixSchurAuditedPresentationGeneratorCoordinates 1 := by
  let sourceFactors : List AlternatingSixSchurCoordinates := [
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1)⁻¹,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1)⁻¹,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2]
  let imageChunks : List (List AlternatingSixSchurCoordinates) := [
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
    [alternatingSixSchurAuditedCoordinate 57 0,
      alternatingSixSchurAuditedCoordinate 84 2],
    [alternatingSixSchurAuditedCoordinate 0 5],
    [alternatingSixSchurAuditedCoordinate 0 5],
    [alternatingSixSchurAuditedCoordinate 0 5],
    [alternatingSixSchurAuditedCoordinate 0 5]]
  let steps :
      List
        (AlternatingSixSchurCoordinates ×
          AlternatingSixSchurCoordinates) := [
    (alternatingSixSchurAuditedCoordinate 75 0,
      alternatingSixSchurAuditedCoordinate 75 0),
    (alternatingSixSchurAuditedCoordinate 106 2,
      alternatingSixSchurAuditedCoordinate 355 2),
    (alternatingSixSchurAuditedCoordinate 58 0,
      alternatingSixSchurAuditedCoordinate 178 5),
    (alternatingSixSchurAuditedCoordinate 107 0,
      alternatingSixSchurAuditedCoordinate 126 3),
    (alternatingSixSchurAuditedCoordinate 75 0,
      alternatingSixSchurAuditedCoordinate 349 1),
    (alternatingSixSchurAuditedCoordinate 106 2,
      alternatingSixSchurAuditedCoordinate 65 3),
    (alternatingSixSchurAuditedCoordinate 57 0,
      alternatingSixSchurAuditedCoordinate 243 1),
    (alternatingSixSchurAuditedCoordinate 84 2,
      alternatingSixSchurAuditedCoordinate 224 5),
    (alternatingSixSchurAuditedCoordinate 75 0,
      alternatingSixSchurAuditedCoordinate 354 1),
    (alternatingSixSchurAuditedCoordinate 106 2,
      alternatingSixSchurAuditedCoordinate 359 4),
    (alternatingSixSchurAuditedCoordinate 57 0,
      alternatingSixSchurAuditedCoordinate 141 4),
    (alternatingSixSchurAuditedCoordinate 84 2,
      alternatingSixSchurAuditedCoordinate 2 4),
    (alternatingSixSchurAuditedCoordinate 0 5,
      alternatingSixSchurAuditedCoordinate 2 3),
    (alternatingSixSchurAuditedCoordinate 0 5,
      alternatingSixSchurAuditedCoordinate 2 2),
    (alternatingSixSchurAuditedCoordinate 0 5,
      alternatingSixSchurAuditedCoordinate 2 1),
    (alternatingSixSchurAuditedCoordinate 0 5,
      alternatingSixSchurAuditedCoordinate 2 0)]
  have hsource :
      sourceFactors.prod =
        alternatingSixSchurAlphaTwoGeneratorCoordinates 1 := by
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
        (alternatingSixSchurAuditedCoordinate 2 0) := by
    simp only [steps, alternatingSixSchurMultiplicationChain]
    repeat' apply And.intro
    all_goals decide
  have happly :=
    monoidHom_apply_eq_of_alternatingSixSchurMultiplicationChain
      alternatingSixSchurAlphaTwoInverseEndomorphism
      sourceFactors
      (alternatingSixSchurAlphaTwoGeneratorCoordinates 1)
      imageChunks steps
      (alternatingSixSchurAuditedCoordinate 2 0)
      hsource hmapped hflatten hchain
  simpa [alternatingSixSchurAuditedPresentationGeneratorCoordinates,
    alternatingSixSchurAuditedCoordinate] using happly

theorem alternatingSixSchurAlphaTwoInverse_comp_alphaTwo :
    alternatingSixSchurAlphaTwoInverseEndomorphism.comp
        alternatingSixSchurAlphaTwoEndomorphism =
      MonoidHom.id AlternatingSixSchurCoordinates := by
  apply alternatingSixSchurCoordinates_monoidHom_ext
  intro i
  fin_cases i
  · change
      alternatingSixSchurAlphaTwoInverseEndomorphism
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 0) =
        alternatingSixSchurAuditedPresentationGeneratorCoordinates 0
    exact
      alternatingSixSchurAlphaTwoInverse_apply_alphaTwo_generator_zero
  · change
      alternatingSixSchurAlphaTwoInverseEndomorphism
          (alternatingSixSchurAlphaTwoGeneratorCoordinates 1) =
        alternatingSixSchurAuditedPresentationGeneratorCoordinates 1
    exact
      alternatingSixSchurAlphaTwoInverse_apply_alphaTwo_generator_one
  · change
      alternatingSixSchurAlphaTwoInverseEndomorphism
          (alternatingSixSchurAuditedCoordinate 0 5) =
        alternatingSixSchurAuditedCoordinate 0 1
    convert
      alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
        alternatingSixSchurAlphaTwoInverseEndomorphism
        (alternatingSixSchurAlphaTwoInverseEndomorphism_generator 2)
        (5 : Fin 6) using 1 <;> decide
  · change
      alternatingSixSchurAlphaTwoInverseEndomorphism
          (alternatingSixSchurAuditedCoordinate 0 3) =
        alternatingSixSchurAuditedCoordinate 0 3
    convert
      alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
        alternatingSixSchurAlphaTwoInverseEndomorphism
        (alternatingSixSchurAlphaTwoInverseEndomorphism_generator 2)
        (3 : Fin 6) using 1 <;> decide
  · change
      alternatingSixSchurAlphaTwoInverseEndomorphism
          (alternatingSixSchurAuditedCoordinate 0 1) =
        alternatingSixSchurAuditedCoordinate 0 5
    convert
      alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
        alternatingSixSchurAlphaTwoInverseEndomorphism
        (alternatingSixSchurAlphaTwoInverseEndomorphism_generator 2)
        (1 : Fin 6) using 1 <;> decide
  · change
      alternatingSixSchurAlphaTwoInverseEndomorphism
          (alternatingSixSchurAuditedCoordinate 0 5) =
        alternatingSixSchurAuditedCoordinate 0 1
    convert
      alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
        alternatingSixSchurAlphaTwoInverseEndomorphism
        (alternatingSixSchurAlphaTwoInverseEndomorphism_generator 2)
        (5 : Fin 6) using 1 <;> decide

theorem alternatingSixSchurAlphaTwo_apply_inverse_generator_zero :
    alternatingSixSchurAlphaTwoEndomorphism
        (alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 0) =
      alternatingSixSchurAuditedPresentationGeneratorCoordinates 0 := by
  let sourceFactors : List AlternatingSixSchurCoordinates := [
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1)⁻¹,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1)⁻¹,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1)⁻¹,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1)⁻¹,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2]
  let imageChunks : List (List AlternatingSixSchurCoordinates) := [
    [alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 56 1],
    [alternatingSixSchurAuditedCoordinate 52 4],
    [alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 56 1],
    [alternatingSixSchurAuditedCoordinate 52 4],
    [alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 56 1],
    [alternatingSixSchurAuditedCoordinate 60 5],
    [alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 56 1],
    [alternatingSixSchurAuditedCoordinate 60 5],
    [alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 56 1],
    [alternatingSixSchurAuditedCoordinate 52 4],
    [alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 56 1],
    [alternatingSixSchurAuditedCoordinate 60 5],
    [alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 56 1],
    [alternatingSixSchurAuditedCoordinate 60 5],
    [alternatingSixSchurAuditedCoordinate 0 5],
    [alternatingSixSchurAuditedCoordinate 0 5]]
  let steps :
      List
        (AlternatingSixSchurCoordinates ×
          AlternatingSixSchurCoordinates) := [
    (alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 61 0),
    (alternatingSixSchurAuditedCoordinate 56 1,
      alternatingSixSchurAuditedCoordinate 317 1),
    (alternatingSixSchurAuditedCoordinate 52 4,
      alternatingSixSchurAuditedCoordinate 284 2),
    (alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 135 5),
    (alternatingSixSchurAuditedCoordinate 56 1,
      alternatingSixSchurAuditedCoordinate 298 0),
    (alternatingSixSchurAuditedCoordinate 52 4,
      alternatingSixSchurAuditedCoordinate 182 1),
    (alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 210 3),
    (alternatingSixSchurAuditedCoordinate 56 1,
      alternatingSixSchurAuditedCoordinate 16 4),
    (alternatingSixSchurAuditedCoordinate 60 5,
      alternatingSixSchurAuditedCoordinate 11 4),
    (alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 173 4),
    (alternatingSixSchurAuditedCoordinate 56 1,
      alternatingSixSchurAuditedCoordinate 285 5),
    (alternatingSixSchurAuditedCoordinate 60 5,
      alternatingSixSchurAuditedCoordinate 40 4),
    (alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 131 5),
    (alternatingSixSchurAuditedCoordinate 56 1,
      alternatingSixSchurAuditedCoordinate 314 5),
    (alternatingSixSchurAuditedCoordinate 52 4,
      alternatingSixSchurAuditedCoordinate 217 5),
    (alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 237 4),
    (alternatingSixSchurAuditedCoordinate 56 1,
      alternatingSixSchurAuditedCoordinate 174 3),
    (alternatingSixSchurAuditedCoordinate 60 5,
      alternatingSixSchurAuditedCoordinate 176 0),
    (alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 287 0),
    (alternatingSixSchurAuditedCoordinate 56 1,
      alternatingSixSchurAuditedCoordinate 41 1),
    (alternatingSixSchurAuditedCoordinate 60 5,
      alternatingSixSchurAuditedCoordinate 1 2),
    (alternatingSixSchurAuditedCoordinate 0 5,
      alternatingSixSchurAuditedCoordinate 1 1),
    (alternatingSixSchurAuditedCoordinate 0 5,
      alternatingSixSchurAuditedCoordinate 1 0)]
  have hsource :
      sourceFactors.prod =
        alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 0 := by
    dsimp [sourceFactors]
    decide
  have hmapped :
      sourceFactors.map alternatingSixSchurAlphaTwoEndomorphism =
        imageChunks.map List.prod := by
    simp only [sourceFactors, imageChunks, List.map_cons, List.map_nil,
      map_inv, alternatingSixSchurAlphaTwoEndomorphism_generator]
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
  have happly :=
    monoidHom_apply_eq_of_alternatingSixSchurMultiplicationChain
      alternatingSixSchurAlphaTwoEndomorphism
      sourceFactors
      (alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 0)
      imageChunks steps
      (alternatingSixSchurAuditedCoordinate 1 0)
      hsource hmapped hflatten hchain
  simpa [alternatingSixSchurAuditedPresentationGeneratorCoordinates,
    alternatingSixSchurAuditedCoordinate] using happly

theorem alternatingSixSchurAlphaTwo_apply_inverse_generator_one :
    alternatingSixSchurAlphaTwoEndomorphism
        (alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 1) =
      alternatingSixSchurAuditedPresentationGeneratorCoordinates 1 := by
  let sourceFactors : List AlternatingSixSchurCoordinates := [
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1)⁻¹,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1)⁻¹,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0]
  let imageChunks : List (List AlternatingSixSchurCoordinates) := [
    [alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 56 1],
    [alternatingSixSchurAuditedCoordinate 60 5],
    [alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 56 1],
    [alternatingSixSchurAuditedCoordinate 52 4],
    [alternatingSixSchurAuditedCoordinate 52 4],
    [alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 56 1],
    [alternatingSixSchurAuditedCoordinate 60 5],
    [alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 56 1],
    [alternatingSixSchurAuditedCoordinate 52 4],
    [alternatingSixSchurAuditedCoordinate 52 4],
    [alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 56 1],
    [alternatingSixSchurAuditedCoordinate 52 4],
    [alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 56 1]]
  let steps :
      List
        (AlternatingSixSchurCoordinates ×
          AlternatingSixSchurCoordinates) := [
    (alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 61 0),
    (alternatingSixSchurAuditedCoordinate 56 1,
      alternatingSixSchurAuditedCoordinate 317 1),
    (alternatingSixSchurAuditedCoordinate 60 5,
      alternatingSixSchurAuditedCoordinate 112 4),
    (alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 46 1),
    (alternatingSixSchurAuditedCoordinate 56 1,
      alternatingSixSchurAuditedCoordinate 296 2),
    (alternatingSixSchurAuditedCoordinate 52 4,
      alternatingSixSchurAuditedCoordinate 146 0),
    (alternatingSixSchurAuditedCoordinate 52 4,
      alternatingSixSchurAuditedCoordinate 33 1),
    (alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 26 4),
    (alternatingSixSchurAuditedCoordinate 56 1,
      alternatingSixSchurAuditedCoordinate 149 0),
    (alternatingSixSchurAuditedCoordinate 60 5,
      alternatingSixSchurAuditedCoordinate 76 0),
    (alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 21 0),
    (alternatingSixSchurAuditedCoordinate 56 1,
      alternatingSixSchurAuditedCoordinate 61 0),
    (alternatingSixSchurAuditedCoordinate 52 4,
      alternatingSixSchurAuditedCoordinate 173 5),
    (alternatingSixSchurAuditedCoordinate 52 4,
      alternatingSixSchurAuditedCoordinate 223 4),
    (alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 84 2),
    (alternatingSixSchurAuditedCoordinate 56 1,
      alternatingSixSchurAuditedCoordinate 87 5),
    (alternatingSixSchurAuditedCoordinate 52 4,
      alternatingSixSchurAuditedCoordinate 276 3),
    (alternatingSixSchurAuditedCoordinate 61 0,
      alternatingSixSchurAuditedCoordinate 35 2),
    (alternatingSixSchurAuditedCoordinate 56 1,
      alternatingSixSchurAuditedCoordinate 2 0)]
  have hsource :
      sourceFactors.prod =
        alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 1 := by
    dsimp [sourceFactors]
    decide
  have hmapped :
      sourceFactors.map alternatingSixSchurAlphaTwoEndomorphism =
        imageChunks.map List.prod := by
    simp only [sourceFactors, imageChunks, List.map_cons, List.map_nil,
      map_inv, alternatingSixSchurAlphaTwoEndomorphism_generator]
    decide
  have hflatten :
      imageChunks.flatten = steps.map Prod.fst := by
    rfl
  have hchain :
      alternatingSixSchurMultiplicationChain 1 steps
        (alternatingSixSchurAuditedCoordinate 2 0) := by
    simp only [steps, alternatingSixSchurMultiplicationChain]
    repeat' apply And.intro
    all_goals decide
  have happly :=
    monoidHom_apply_eq_of_alternatingSixSchurMultiplicationChain
      alternatingSixSchurAlphaTwoEndomorphism
      sourceFactors
      (alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 1)
      imageChunks steps
      (alternatingSixSchurAuditedCoordinate 2 0)
      hsource hmapped hflatten hchain
  simpa [alternatingSixSchurAuditedPresentationGeneratorCoordinates,
    alternatingSixSchurAuditedCoordinate] using happly

theorem alternatingSixSchurAlphaTwo_comp_inverse :
    alternatingSixSchurAlphaTwoEndomorphism.comp
        alternatingSixSchurAlphaTwoInverseEndomorphism =
      MonoidHom.id AlternatingSixSchurCoordinates := by
  apply alternatingSixSchurCoordinates_monoidHom_ext
  intro i
  fin_cases i
  · change
      alternatingSixSchurAlphaTwoEndomorphism
          (alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 0) =
        alternatingSixSchurAuditedPresentationGeneratorCoordinates 0
    exact
      alternatingSixSchurAlphaTwo_apply_inverse_generator_zero
  · change
      alternatingSixSchurAlphaTwoEndomorphism
          (alternatingSixSchurAlphaTwoInverseGeneratorCoordinates 1) =
        alternatingSixSchurAuditedPresentationGeneratorCoordinates 1
    exact
      alternatingSixSchurAlphaTwo_apply_inverse_generator_one
  · change
      alternatingSixSchurAlphaTwoEndomorphism
          (alternatingSixSchurAuditedCoordinate 0 5) =
        alternatingSixSchurAuditedCoordinate 0 1
    convert
      alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
        alternatingSixSchurAlphaTwoEndomorphism
        (alternatingSixSchurAlphaTwoEndomorphism_generator 2)
        (5 : Fin 6) using 1 <;> decide
  · change
      alternatingSixSchurAlphaTwoEndomorphism
          (alternatingSixSchurAuditedCoordinate 0 3) =
        alternatingSixSchurAuditedCoordinate 0 3
    convert
      alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
        alternatingSixSchurAlphaTwoEndomorphism
        (alternatingSixSchurAlphaTwoEndomorphism_generator 2)
        (3 : Fin 6) using 1 <;> decide
  · change
      alternatingSixSchurAlphaTwoEndomorphism
          (alternatingSixSchurAuditedCoordinate 0 1) =
        alternatingSixSchurAuditedCoordinate 0 5
    convert
      alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
        alternatingSixSchurAlphaTwoEndomorphism
        (alternatingSixSchurAlphaTwoEndomorphism_generator 2)
        (1 : Fin 6) using 1 <;> decide
  · change
      alternatingSixSchurAlphaTwoEndomorphism
          (alternatingSixSchurAuditedCoordinate 0 5) =
        alternatingSixSchurAuditedCoordinate 0 1
    convert
      alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
        alternatingSixSchurAlphaTwoEndomorphism
        (alternatingSixSchurAlphaTwoEndomorphism_generator 2)
        (5 : Fin 6) using 1 <;> decide

theorem alternatingSixSchurAlphaTwoInverse_leftInverse :
    Function.LeftInverse
      alternatingSixSchurAlphaTwoInverseEndomorphism
      alternatingSixSchurAlphaTwoEndomorphism := by
  intro coordinate
  have hcoordinate :=
    DFunLike.congr_fun
      alternatingSixSchurAlphaTwoInverse_comp_alphaTwo coordinate
  simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using hcoordinate

theorem alternatingSixSchurAlphaTwoInverse_rightInverse :
    Function.RightInverse
      alternatingSixSchurAlphaTwoInverseEndomorphism
      alternatingSixSchurAlphaTwoEndomorphism := by
  intro coordinate
  have hcoordinate :=
    DFunLike.congr_fun
      alternatingSixSchurAlphaTwo_comp_inverse coordinate
  simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using hcoordinate

theorem alternatingSixSchurAlphaTwoEndomorphism_bijective :
    Function.Bijective alternatingSixSchurAlphaTwoEndomorphism :=
  ⟨alternatingSixSchurAlphaTwoInverse_leftInverse.injective,
    alternatingSixSchurAlphaTwoInverse_rightInverse.surjective⟩

/-- The audited order-eight representative of the second outer class,
packaged as an automorphism of the computable Schur-cover model. -/
def alternatingSixSchurAlphaTwoAutomorphism :
    AlternatingSixSchurCoordinates ≃*
      AlternatingSixSchurCoordinates :=
  MulEquiv.ofBijective
    alternatingSixSchurAlphaTwoEndomorphism
    alternatingSixSchurAlphaTwoEndomorphism_bijective

theorem alternatingSixSchurAlphaOne_apply_alphaOne_generator_zero :
    alternatingSixSchurAlphaOneEndomorphism
        (alternatingSixSchurAlphaOneGeneratorCoordinates 0) =
      alternatingSixSchurAuditedPresentationGeneratorCoordinates 0 := by
  let sourceFactors : List AlternatingSixSchurCoordinates := [
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2]
  let imageChunks : List (List AlternatingSixSchurCoordinates) := [
    [alternatingSixSchurAuditedCoordinate 1 2],
    [alternatingSixSchurAuditedCoordinate 0 5],
    [alternatingSixSchurAuditedCoordinate 0 5]]
  let steps :
      List
        (AlternatingSixSchurCoordinates ×
          AlternatingSixSchurCoordinates) := [
    (alternatingSixSchurAuditedCoordinate 1 2,
      alternatingSixSchurAuditedCoordinate 1 2),
    (alternatingSixSchurAuditedCoordinate 0 5,
      alternatingSixSchurAuditedCoordinate 1 1),
    (alternatingSixSchurAuditedCoordinate 0 5,
      alternatingSixSchurAuditedCoordinate 1 0)]
  have hsource :
      sourceFactors.prod =
        alternatingSixSchurAlphaOneGeneratorCoordinates 0 := by
    dsimp [sourceFactors]
    decide
  have hmapped :
      sourceFactors.map alternatingSixSchurAlphaOneEndomorphism =
        imageChunks.map List.prod := by
    simp only [sourceFactors, imageChunks, List.map_cons, List.map_nil,
      alternatingSixSchurAlphaOneEndomorphism_generator]
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
  have happly :=
    monoidHom_apply_eq_of_alternatingSixSchurMultiplicationChain
      alternatingSixSchurAlphaOneEndomorphism
      sourceFactors
      (alternatingSixSchurAlphaOneGeneratorCoordinates 0)
      imageChunks steps
      (alternatingSixSchurAuditedCoordinate 1 0)
      hsource hmapped hflatten hchain
  simpa [alternatingSixSchurAuditedPresentationGeneratorCoordinates,
    alternatingSixSchurAuditedCoordinate] using happly

theorem alternatingSixSchurAlphaOne_apply_alphaOne_generator_one :
    alternatingSixSchurAlphaOneEndomorphism
        (alternatingSixSchurAlphaOneGeneratorCoordinates 1) =
      alternatingSixSchurAuditedPresentationGeneratorCoordinates 1 := by
  let sourceFactors : List AlternatingSixSchurCoordinates := [
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    (alternatingSixSchurAuditedPresentationGeneratorCoordinates 1)⁻¹,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 1,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 0,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2,
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2]
  let imageChunks : List (List AlternatingSixSchurCoordinates) := [
    [alternatingSixSchurAuditedCoordinate 63 2],
    [alternatingSixSchurAuditedCoordinate 1 2],
    [alternatingSixSchurAuditedCoordinate 57 1],
    [alternatingSixSchurAuditedCoordinate 1 2],
    [alternatingSixSchurAuditedCoordinate 63 2],
    [alternatingSixSchurAuditedCoordinate 1 2],
    [alternatingSixSchurAuditedCoordinate 0 5],
    [alternatingSixSchurAuditedCoordinate 0 5]]
  let steps :
      List
        (AlternatingSixSchurCoordinates ×
          AlternatingSixSchurCoordinates) := [
    (alternatingSixSchurAuditedCoordinate 63 2,
      alternatingSixSchurAuditedCoordinate 63 2),
    (alternatingSixSchurAuditedCoordinate 1 2,
      alternatingSixSchurAuditedCoordinate 40 5),
    (alternatingSixSchurAuditedCoordinate 57 1,
      alternatingSixSchurAuditedCoordinate 32 4),
    (alternatingSixSchurAuditedCoordinate 1 2,
      alternatingSixSchurAuditedCoordinate 18 1),
    (alternatingSixSchurAuditedCoordinate 63 2,
      alternatingSixSchurAuditedCoordinate 6 5),
    (alternatingSixSchurAuditedCoordinate 1 2,
      alternatingSixSchurAuditedCoordinate 2 2),
    (alternatingSixSchurAuditedCoordinate 0 5,
      alternatingSixSchurAuditedCoordinate 2 1),
    (alternatingSixSchurAuditedCoordinate 0 5,
      alternatingSixSchurAuditedCoordinate 2 0)]
  have hsource :
      sourceFactors.prod =
        alternatingSixSchurAlphaOneGeneratorCoordinates 1 := by
    dsimp [sourceFactors]
    decide
  have hmapped :
      sourceFactors.map alternatingSixSchurAlphaOneEndomorphism =
        imageChunks.map List.prod := by
    simp only [sourceFactors, imageChunks, List.map_cons, List.map_nil,
      map_inv, alternatingSixSchurAlphaOneEndomorphism_generator]
    decide
  have hflatten :
      imageChunks.flatten = steps.map Prod.fst := by
    rfl
  have hchain :
      alternatingSixSchurMultiplicationChain 1 steps
        (alternatingSixSchurAuditedCoordinate 2 0) := by
    simp only [steps, alternatingSixSchurMultiplicationChain]
    repeat' apply And.intro
    all_goals decide
  have happly :=
    monoidHom_apply_eq_of_alternatingSixSchurMultiplicationChain
      alternatingSixSchurAlphaOneEndomorphism
      sourceFactors
      (alternatingSixSchurAlphaOneGeneratorCoordinates 1)
      imageChunks steps
      (alternatingSixSchurAuditedCoordinate 2 0)
      hsource hmapped hflatten hchain
  simpa [alternatingSixSchurAuditedPresentationGeneratorCoordinates,
    alternatingSixSchurAuditedCoordinate] using happly

theorem alternatingSixSchurAlphaOne_comp_self :
    alternatingSixSchurAlphaOneEndomorphism.comp
        alternatingSixSchurAlphaOneEndomorphism =
      MonoidHom.id AlternatingSixSchurCoordinates := by
  apply alternatingSixSchurCoordinates_monoidHom_ext
  intro i
  fin_cases i
  · change
      alternatingSixSchurAlphaOneEndomorphism
          (alternatingSixSchurAlphaOneGeneratorCoordinates 0) =
        alternatingSixSchurAuditedPresentationGeneratorCoordinates 0
    exact alternatingSixSchurAlphaOne_apply_alphaOne_generator_zero
  · change
      alternatingSixSchurAlphaOneEndomorphism
          (alternatingSixSchurAlphaOneGeneratorCoordinates 1) =
        alternatingSixSchurAuditedPresentationGeneratorCoordinates 1
    exact alternatingSixSchurAlphaOne_apply_alphaOne_generator_one
  · change
      alternatingSixSchurAlphaOneEndomorphism
          (alternatingSixSchurAuditedCoordinate 0 5) =
        alternatingSixSchurAuditedCoordinate 0 1
    convert
      alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
        alternatingSixSchurAlphaOneEndomorphism
        (alternatingSixSchurAlphaOneEndomorphism_generator 2)
        (5 : Fin 6) using 1 <;> decide
  · change
      alternatingSixSchurAlphaOneEndomorphism
          (alternatingSixSchurAuditedCoordinate 0 3) =
        alternatingSixSchurAuditedCoordinate 0 3
    convert
      alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
        alternatingSixSchurAlphaOneEndomorphism
        (alternatingSixSchurAlphaOneEndomorphism_generator 2)
        (3 : Fin 6) using 1 <;> decide
  · change
      alternatingSixSchurAlphaOneEndomorphism
          (alternatingSixSchurAuditedCoordinate 0 1) =
        alternatingSixSchurAuditedCoordinate 0 5
    convert
      alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
        alternatingSixSchurAlphaOneEndomorphism
        (alternatingSixSchurAlphaOneEndomorphism_generator 2)
        (1 : Fin 6) using 1 <;> decide
  · change
      alternatingSixSchurAlphaOneEndomorphism
          (alternatingSixSchurAuditedCoordinate 0 5) =
        alternatingSixSchurAuditedCoordinate 0 1
    convert
      alternatingSixSchurMonoidHom_central_of_generator_eq_inverse
        alternatingSixSchurAlphaOneEndomorphism
        (alternatingSixSchurAlphaOneEndomorphism_generator 2)
        (5 : Fin 6) using 1 <;> decide

theorem alternatingSixSchurAlphaOneEndomorphism_involutive :
    Function.Involutive alternatingSixSchurAlphaOneEndomorphism := by
  intro coordinate
  have hcoordinate :=
    DFunLike.congr_fun alternatingSixSchurAlphaOne_comp_self coordinate
  simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using hcoordinate

theorem alternatingSixSchurAlphaOneEndomorphism_bijective :
    Function.Bijective alternatingSixSchurAlphaOneEndomorphism :=
  alternatingSixSchurAlphaOneEndomorphism_involutive.bijective

/-- The audited involutive representative of the first outer class,
packaged as an automorphism of the computable Schur-cover model. -/
def alternatingSixSchurAlphaOneAutomorphism :
    AlternatingSixSchurCoordinates ≃*
      AlternatingSixSchurCoordinates :=
  MulEquiv.ofBijective
    alternatingSixSchurAlphaOneEndomorphism
    alternatingSixSchurAlphaOneEndomorphism_bijective

end GroupTheory
end McKayConjecture
