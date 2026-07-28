/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AlternatingSixThreeNormalizerDegreeFourIrreducible

/-!
# Separation of the four degree-four normalizer rows

Two diagnostic values distinguish the two orbit parameters and the two
extension signs.  The noncentral Heisenberg generator has values `1` and
`-2`, while the fourth power of the cyclic generator has values `4` and
`-4`.
-/

noncomputable section

open CategoryTheory Matrix

namespace McKayConjecture
namespace AlternatingSixThreeNormalizer

open GroupTheory

/-- Character values are traces of the displayed monomial matrices. -/
theorem degreeFourCharacter_values_trace
    (orbit extension : Fin 2)
    (g : AlternatingSixThreeNormalizerCoordinates) :
    (degreeFourCharacter orbit extension).values g =
      Matrix.trace
        (degreeFourGLHom orbit extension g :
          Matrix (Fin 4) (Fin 4) ℂ) := by
  change
    (degreeFourFDRep orbit extension).character g =
      Matrix.trace
        (degreeFourGLHom orbit extension g :
          Matrix (Fin 4) (Fin 4) ℂ)
  rw [show
      (degreeFourFDRep orbit extension).character g =
        LinearMap.trace ℂ (Fin 4 → ℂ)
          (Matrix.toLin'
            (degreeFourGLHom orbit extension g :
              Matrix (Fin 4) (Fin 4) ℂ)) by
      rfl,
    Matrix.trace_toLin'_eq]

/-- The primitive cubic phase satisfies its cyclotomic polynomial. -/
theorem threePhase_one_cyclotomic :
    threePhase (1 : ZMod 3) ^ 2 +
        threePhase (1 : ZMod 3) + 1 =
      0 := by
  let w : ℂ := threePhase (1 : ZMod 3)
  have hw_ne : w ≠ 1 := by
    intro hw
    have hphase :
        threePhase (1 : ZMod 3) =
          threePhase (0 : ZMod 3) := by
      simpa [w] using hw
    exact (by decide : (1 : ZMod 3) ≠ 0)
      (ZMod.injective_stdAddChar hphase)
  have hw_cube : w ^ 3 = 1 := by
    rw [show w ^ 3 = w * w * w by ring]
    dsimp [w]
    rw [← threePhase_add, ← threePhase_add]
    rw [show (1 + 1 + 1 : ZMod 3) = 0 by decide,
      threePhase_zero]
  have hfactor :
      (w - 1) * (w ^ 2 + w + 1) = 0 := by
    calc
      (w - 1) * (w ^ 2 + w + 1) = w ^ 3 - 1 := by ring
      _ = 0 := sub_eq_zero.mpr hw_cube
  exact
    (mul_eq_zero.mp hfactor).resolve_left
      (sub_ne_zero.mpr hw_ne)

theorem threePhase_neg_one :
    threePhase (-1 : ZMod 3) =
      threePhase (1 : ZMod 3) ^ 2 := by
  rw [show (-1 : ZMod 3) = 1 + 1 by decide,
    threePhase_add, pow_two]

/-- The two orbit parameters are distinguished on a noncentral
Heisenberg generator. -/
@[simp]
theorem degreeFourCharacter_values_generatorA
    (orbit extension : Fin 2) :
    (degreeFourCharacter orbit extension).values
        degreeFourNormalizerGeneratorA =
      if orbit.val = 0 then 1 else -2 := by
  rw [degreeFourCharacter_values_trace]
  have hmatrix :
      (degreeFourGLHom orbit extension
          degreeFourNormalizerGeneratorA :
        Matrix (Fin 4) (Fin 4) ℂ) =
        degreeFourDiagonalMatrix orbit
          degreeFourHeisenbergGenerator := by
    change
      ((degreeFourGLHom orbit extension
          (SemidirectProduct.inl degreeFourHeisenbergGenerator) :
            Matrix.GeneralLinearGroup (Fin 4) ℂ) :
        Matrix (Fin 4) (Fin 4) ℂ) =
          degreeFourDiagonalMatrix orbit
            degreeFourHeisenbergGenerator
    rw [degreeFourGLHom, SemidirectProduct.lift_inl]
    rfl
  rw [hmatrix]
  fin_cases orbit
  · simp [Matrix.trace, degreeFourDiagonalMatrix,
      degreeFourExponent, degreeFourHeisenbergGenerator,
      Fin.sum_univ_succ, threePhase_neg_one]
    linear_combination threePhase_one_cyclotomic
  · simp [Matrix.trace, degreeFourDiagonalMatrix,
      degreeFourExponent, degreeFourHeisenbergGenerator,
      Fin.sum_univ_succ, threePhase_neg_one]
    linear_combination 2 * threePhase_one_cyclotomic

/-- The order-two kernel element of `C₈ → C₄` detects the extension
sign. -/
def degreeFourCyclicKernelElement :
    AlternatingSixThreeNormalizerCoordinates :=
  SemidirectProduct.inr
    (Multiplicative.ofAdd (4 : ZMod 8))

@[simp]
theorem degreeFourCharacter_values_cyclicKernel
    (orbit extension : Fin 2) :
    (degreeFourCharacter orbit extension).values
        degreeFourCyclicKernelElement =
      if extension.val = 0 then 4 else -4 := by
  rw [degreeFourCharacter_values_trace]
  have hmatrix :
      (degreeFourGLHom orbit extension
          degreeFourCyclicKernelElement :
        Matrix (Fin 4) (Fin 4) ℂ) =
        (degreeFourCyclicHom extension
            (Multiplicative.ofAdd (4 : ZMod 8)) :
          Matrix (Fin 4) (Fin 4) ℂ) := by
    change
      ((degreeFourGLHom orbit extension
          (SemidirectProduct.inr
            (Multiplicative.ofAdd (4 : ZMod 8))) :
            Matrix.GeneralLinearGroup (Fin 4) ℂ) :
        Matrix (Fin 4) (Fin 4) ℂ) =
          (degreeFourCyclicHom extension
              (Multiplicative.ofAdd (4 : ZMod 8)) :
            Matrix (Fin 4) (Fin 4) ℂ)
    rw [degreeFourGLHom, SemidirectProduct.lift_inr]
  rw [hmatrix]
  have hpow :
      (degreeFourCyclicHom extension
          (Multiplicative.ofAdd (4 : ZMod 8)) :
        Matrix (Fin 4) (Fin 4) ℂ) =
        ((degreeFourShiftGL extension ^ 4 :
            Matrix.GeneralLinearGroup (Fin 4) ℂ) :
          Matrix (Fin 4) (Fin 4) ℂ) :=
    congrArg
      (fun u : Matrix.GeneralLinearGroup (Fin 4) ℂ =>
        (u : Matrix (Fin 4) (Fin 4) ℂ))
      (degreeFourCyclicHom_ofAdd_nat extension 4)
  rw [hpow]
  fin_cases extension <;>
    simp [Matrix.trace, degreeFourShiftGL,
      degreeFourShiftMatrix, degreeFourSign,
      pow_succ, Fin.sum_univ_succ] <;>
    norm_num

/-- The four degree-four characters are pairwise distinct. -/
theorem degreeFourCharacter_injective :
    Function.Injective
      (fun r : Fin 2 × Fin 2 =>
        degreeFourCharacter r.1 r.2) := by
  rintro ⟨orbit, extension⟩ ⟨orbit', extension'⟩ hrows
  have horbitValue :=
    congrArg
      (fun χ :
        IrreducibleCharacter
          AlternatingSixThreeNormalizerCoordinates =>
        χ.values degreeFourNormalizerGeneratorA)
      hrows
  have horbit : orbit = orbit' := by
    fin_cases orbit <;> fin_cases orbit'
    · rfl
    · norm_num at horbitValue
    · norm_num at horbitValue
    · rfl
  subst orbit'
  have hextensionValue :=
    congrArg
      (fun χ :
        IrreducibleCharacter
          AlternatingSixThreeNormalizerCoordinates =>
        χ.values degreeFourCyclicKernelElement)
      hrows
  have hextension : extension = extension' := by
    fin_cases extension <;> fin_cases extension'
    · rfl
    · norm_num at hextensionValue
    · norm_num at hextensionValue
    · rfl
  subst extension'
  rfl

end AlternatingSixThreeNormalizer
end McKayConjecture
