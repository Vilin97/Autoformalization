/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.BinaryIcosahedralTwoGeneratorPresentation
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveSylowThreeNormalizer

/-!
# Automorphisms of `SL(2, 𝔽₅)` stabilizing the chosen Sylow-three subgroup

Conjugation by a determinant-nonsquare matrix gives the non-inner
automorphism of `SL(2, 𝔽₅)`.  We compose it with one inner automorphism so
that it fixes the chosen Sylow-three generator.  A finite certificate on
the standard binary-icosahedral generators then proves that every
automorphism is either inner or this fixed outer automorphism followed by
an inner automorphism.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace McKayConjecture
namespace GroupTheory

/-- The determinant-nonsquare diagonal matrix used to define the outer
automorphism. -/
def specialLinearTwoFiveOuterDiagonal :
    Matrix (Fin 2) (Fin 2) (ZMod 5) :=
  !![(2 : ZMod 5), 0; 0, 1]

/-- The inverse of `specialLinearTwoFiveOuterDiagonal`. -/
def specialLinearTwoFiveOuterDiagonalInv :
    Matrix (Fin 2) (Fin 2) (ZMod 5) :=
  !![(3 : ZMod 5), 0; 0, 1]

@[simp]
theorem specialLinearTwoFiveOuterDiagonal_mul_inv :
    specialLinearTwoFiveOuterDiagonal *
        specialLinearTwoFiveOuterDiagonalInv =
      1 := by
  native_decide

@[simp]
theorem specialLinearTwoFiveOuterDiagonal_inv_mul :
    specialLinearTwoFiveOuterDiagonalInv *
        specialLinearTwoFiveOuterDiagonal =
      1 := by
  native_decide

/-- Conjugation by `diag(2,1)`, viewed as an automorphism of the special
linear group. -/
def specialLinearTwoFiveDiagonalOuterAutomorphism :
    MulAut SpecialLinearTwoFive where
  toFun g :=
    ⟨specialLinearTwoFiveOuterDiagonal * g.1 *
        specialLinearTwoFiveOuterDiagonalInv, by
      rw [det_mul, det_mul, g.2]
      native_decide⟩
  invFun g :=
    ⟨specialLinearTwoFiveOuterDiagonalInv * g.1 *
        specialLinearTwoFiveOuterDiagonal, by
      rw [det_mul, det_mul, g.2]
      native_decide⟩
  left_inv g := by
    apply Subtype.ext
    change
      specialLinearTwoFiveOuterDiagonalInv *
            (specialLinearTwoFiveOuterDiagonal * g.1 *
              specialLinearTwoFiveOuterDiagonalInv) *
          specialLinearTwoFiveOuterDiagonal =
        g.1
    simp only [← Matrix.mul_assoc,
      specialLinearTwoFiveOuterDiagonal_inv_mul, mul_one]
    rw [one_mul, Matrix.mul_assoc,
      specialLinearTwoFiveOuterDiagonal_inv_mul, mul_one]
  right_inv g := by
    apply Subtype.ext
    change
      specialLinearTwoFiveOuterDiagonal *
            (specialLinearTwoFiveOuterDiagonalInv * g.1 *
              specialLinearTwoFiveOuterDiagonal) *
          specialLinearTwoFiveOuterDiagonalInv =
        g.1
    simp only [← Matrix.mul_assoc,
      specialLinearTwoFiveOuterDiagonal_mul_inv, mul_one]
    rw [one_mul, Matrix.mul_assoc,
      specialLinearTwoFiveOuterDiagonal_mul_inv, mul_one]
  map_mul' g h := by
    apply Subtype.ext
    change
      specialLinearTwoFiveOuterDiagonal * (g.1 * h.1) *
          specialLinearTwoFiveOuterDiagonalInv =
        (specialLinearTwoFiveOuterDiagonal * g.1 *
            specialLinearTwoFiveOuterDiagonalInv) *
          (specialLinearTwoFiveOuterDiagonal * h.1 *
            specialLinearTwoFiveOuterDiagonalInv)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc
      specialLinearTwoFiveOuterDiagonalInv
      specialLinearTwoFiveOuterDiagonal
      (h.1 * specialLinearTwoFiveOuterDiagonalInv),
      specialLinearTwoFiveOuterDiagonal_inv_mul, one_mul]

/-- The inner correction which makes the chosen outer automorphism fix the
selected order-three generator. -/
def specialLinearTwoFiveOuterCorrection :
    SpecialLinearTwoFive :=
  ⟨!![(1 : ZMod 5), 1; 2, 3], by native_decide⟩

/-- A fixed representative of the outer automorphism class which stabilizes
the chosen Sylow-three subgroup. -/
def specialLinearTwoFiveSylowThreeOuterAutomorphism :
    MulAut SpecialLinearTwoFive :=
  MulAut.conj specialLinearTwoFiveOuterCorrection *
    specialLinearTwoFiveDiagonalOuterAutomorphism

@[simp]
theorem specialLinearTwoFiveSylowThreeOuterAutomorphism_orderThree :
    specialLinearTwoFiveSylowThreeOuterAutomorphism
        specialLinearTwoFive_orderThreeElement =
      specialLinearTwoFive_orderThreeElement := by
  native_decide

@[simp]
theorem specialLinearTwoFiveSylowThreeOuterAutomorphism_normalizerA :
    specialLinearTwoFiveSylowThreeOuterAutomorphism
        specialLinearTwoFiveSylowThreeNormalizerA.1 =
      specialLinearTwoFiveSylowThreeNormalizerA.1 := by
  native_decide

@[simp]
theorem specialLinearTwoFiveSylowThreeOuterAutomorphism_normalizerX :
    specialLinearTwoFiveSylowThreeOuterAutomorphism
        specialLinearTwoFiveSylowThreeNormalizerX.1 =
      specialLinearTwoFiveSylowThreeNormalizerX.1⁻¹ := by
  native_decide

/-- The two-generator presentation map directly into the concrete matrix
group. -/
def binaryIcosahedralTwoPresentationToSpecialLinearTwoFive :
    BinaryIcosahedralTwoPresentedGroup →*
      SpecialLinearTwoFive :=
  binaryIcosahedralPresentationToSpecialLinearTwoFive.comp
    binaryIcosahedralTwoPresentationToBalanced

@[simp]
theorem binaryIcosahedralTwoPresentationToSpecialLinearTwoFive_a :
    binaryIcosahedralTwoPresentationToSpecialLinearTwoFive
        binaryIcosahedralTwoPresentedA =
      specialLinearTwoFivePresentationY := by
  simp [binaryIcosahedralTwoPresentationToSpecialLinearTwoFive]

@[simp]
theorem binaryIcosahedralTwoPresentationToSpecialLinearTwoFive_b :
    binaryIcosahedralTwoPresentationToSpecialLinearTwoFive
        binaryIcosahedralTwoPresentedB =
      specialLinearTwoFivePresentationZ := by
  simp [binaryIcosahedralTwoPresentationToSpecialLinearTwoFive,
    binaryIcosahedralPresentationToSpecialLinearTwoFive,
    specialLinearTwoFivePresentationGenerator,
    binaryIcosahedralPresentedZ]

/-- The two standard concrete generators generate `SL(2, 𝔽₅)`. -/
theorem binaryIcosahedralTwoPresentationToSpecialLinearTwoFive_surjective :
    Function.Surjective
      binaryIcosahedralTwoPresentationToSpecialLinearTwoFive :=
  binaryIcosahedralPresentationToSpecialLinearTwoFive_surjective.comp
    binaryIcosahedralTwoPresentationToBalanced_surjective

/-- Homomorphisms out of `SL(2, 𝔽₅)` are determined by the two standard
binary-icosahedral generators. -/
theorem specialLinearTwoFive_hom_ext
    {H : Type*} [Group H]
    {f g : SpecialLinearTwoFive →* H}
    (ha :
      f specialLinearTwoFivePresentationY =
        g specialLinearTwoFivePresentationY)
    (hb :
      f specialLinearTwoFivePresentationZ =
        g specialLinearTwoFivePresentationZ) :
    f = g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨w, rfl⟩ :=
    binaryIcosahedralTwoPresentationToSpecialLinearTwoFive_surjective x
  have hcomp :
      f.comp binaryIcosahedralTwoPresentationToSpecialLinearTwoFive =
        g.comp binaryIcosahedralTwoPresentationToSpecialLinearTwoFive := by
    apply MonoidHom.eq_of_eqOn_dense
      (PresentedGroup.closure_range_of
        binaryIcosahedralTwoRelators)
    intro z hz
    obtain ⟨i, rfl⟩ := hz
    fin_cases i
    · change
        f (binaryIcosahedralTwoPresentationToSpecialLinearTwoFive
            binaryIcosahedralTwoPresentedA) =
          g (binaryIcosahedralTwoPresentationToSpecialLinearTwoFive
            binaryIcosahedralTwoPresentedA)
      rw [binaryIcosahedralTwoPresentationToSpecialLinearTwoFive_a]
      exact ha
    · change
        f (binaryIcosahedralTwoPresentationToSpecialLinearTwoFive
            binaryIcosahedralTwoPresentedB) =
          g (binaryIcosahedralTwoPresentationToSpecialLinearTwoFive
            binaryIcosahedralTwoPresentedB)
      rw [binaryIcosahedralTwoPresentationToSpecialLinearTwoFive_b]
      exact hb
  exact DFunLike.congr_fun hcomp w

/-- The finite `(3,5,2)`-generator calculation underlying the
automorphism classification. -/
theorem specialLinearTwoFive_generator_pair_classification :
    ∀ u v : SpecialLinearTwoFive,
      ((u * v) ^ 2 = -1 ∧
        u ^ 3 = -1 ∧
        v ^ 5 = -1) →
      ∃ g : SpecialLinearTwoFive,
        (u = MulAut.conj g specialLinearTwoFivePresentationY ∧
            v = MulAut.conj g specialLinearTwoFivePresentationZ) ∨
          (u =
              (specialLinearTwoFiveSylowThreeOuterAutomorphism *
                MulAut.conj g)
                specialLinearTwoFivePresentationY ∧
            v =
              (specialLinearTwoFiveSylowThreeOuterAutomorphism *
                MulAut.conj g)
                specialLinearTwoFivePresentationZ) := by
  native_decide

/-- The central involution is the unique nontrivial element whose square
is one. -/
theorem specialLinearTwoFive_eq_neg_one_of_sq_eq_one
    (g : SpecialLinearTwoFive)
    (hg : g ^ 2 = 1)
    (hne : g ≠ 1) :
    g = -1 := by
  revert g
  native_decide

@[simp]
theorem specialLinearTwoFive_automorphism_neg_one
    (a : MulAut SpecialLinearTwoFive) :
    a (-1) = -1 := by
  apply specialLinearTwoFive_eq_neg_one_of_sq_eq_one
  · simpa only [map_pow, map_one] using
      congrArg a (show (-1 : SpecialLinearTwoFive) ^ 2 = 1 by
        native_decide)
  · intro h
    have hbad : (-1 : SpecialLinearTwoFive) = 1 := by
      apply a.injective
      simpa using h
    exact (by native_decide : (-1 : SpecialLinearTwoFive) ≠ 1) hbad

theorem specialLinearTwoFivePresentation_two_relations :
    (specialLinearTwoFivePresentationY *
        specialLinearTwoFivePresentationZ) ^ 2 = -1 ∧
      specialLinearTwoFivePresentationY ^ 3 = -1 ∧
      specialLinearTwoFivePresentationZ ^ 5 = -1 := by
  native_decide

/-- Every automorphism of `SL(2, 𝔽₅)` is inner or differs from the fixed
Sylow-three-stabilizing outer automorphism by an inner automorphism. -/
theorem specialLinearTwoFive_automorphism_eq_inner_or_outer_inner
    (a : MulAut SpecialLinearTwoFive) :
    ∃ g : SpecialLinearTwoFive,
      a = MulAut.conj g ∨
        a =
          specialLinearTwoFiveSylowThreeOuterAutomorphism *
            MulAut.conj g := by
  obtain ⟨g, hinner | houter⟩ :=
    specialLinearTwoFive_generator_pair_classification
      (a specialLinearTwoFivePresentationY)
      (a specialLinearTwoFivePresentationZ)
      ⟨(by
        simpa only [map_mul, map_pow,
          specialLinearTwoFive_automorphism_neg_one] using
          congrArg a
            specialLinearTwoFivePresentation_two_relations.1),
      (by
        simpa only [map_pow,
          specialLinearTwoFive_automorphism_neg_one] using
          congrArg a
            specialLinearTwoFivePresentation_two_relations.2.1),
      (by
        simpa only [map_pow,
          specialLinearTwoFive_automorphism_neg_one] using
          congrArg a
            specialLinearTwoFivePresentation_two_relations.2.2)⟩
  · refine ⟨g, Or.inl ?_⟩
    apply MulEquiv.toMonoidHom_injective
    apply specialLinearTwoFive_hom_ext
    · exact hinner.1
    · exact hinner.2
  · refine ⟨g, Or.inr ?_⟩
    apply MulEquiv.toMonoidHom_injective
    apply specialLinearTwoFive_hom_ext
    · exact houter.1
    · exact houter.2

end GroupTheory
end McKayConjecture
