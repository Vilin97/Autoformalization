/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralUnitTwist
import McKayConjecture.Character.ComplexUnitSquare
import McKayConjecture.Character.ZModFiveUnitCharacter
import McKayConjecture.InductiveMcKay.ExactNormalizerCommonCentralCoverCompatibility
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveGeneralLinearExtensions
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Scalar alignment in the `GL(2, 𝔽₅)` character covers

The scalar matrix `2I` generates the kernel of the general-linear cover
of `Aut(SL(2, 𝔽₅))`.  Its square is the central involution `-I` in
`SL(2, 𝔽₅)`.  Consequently, extensions of a matched ambient/local pair
have scalar values at `2I` which differ by at most a sign.  Twisting the
local extension by the determinant character corrects that sign while
remaining trivial on the exact normalizer.

This file packages that normalization and turns the resulting common
central cover into the projective clause for every row whose two central
involution scalars agree.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {p : ℕ}

/-- The scalar matrix `2I` in `GL(2, 𝔽₅)`. -/
def specialLinearTwoFiveGeneralLinearScalarTwo :
    GeneralLinearTwoFive :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) zmodFiveUnitTwo

@[simp]
theorem generalLinearTwoFiveConjugation_scalarTwo :
    generalLinearTwoFiveConjugation
        specialLinearTwoFiveGeneralLinearScalarTwo =
      1 := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  rw [generalLinearTwoFiveConjugation_apply]
  have hcomm :
      specialLinearTwoFiveGeneralLinearScalarTwo *
          Matrix.SpecialLinearGroup.toGL g =
        Matrix.SpecialLinearGroup.toGL g *
          specialLinearTwoFiveGeneralLinearScalarTwo :=
    Matrix.GeneralLinearGroup.scalar_commute _ _
  have hconj :
      specialLinearTwoFiveGeneralLinearScalarTwo *
            Matrix.SpecialLinearGroup.toGL g *
          specialLinearTwoFiveGeneralLinearScalarTwo⁻¹ =
        Matrix.SpecialLinearGroup.toGL g := by
    rw [hcomm]
    group
  exact congrArg Units.val hconj

/-- The scalar generator, regarded as an element of each character cover. -/
def specialLinearTwoFiveCharacterCoverScalarTwo
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p) :
    specialLinearTwoFiveGeneralLinearCharacterCover P χ := by
  have hSylow :
      specialLinearTwoFiveGeneralLinearScalarTwo ∈
        specialLinearTwoFiveGeneralLinearSylowCover P := by
    change
      generalLinearTwoFiveConjugation
          specialLinearTwoFiveGeneralLinearScalarTwo ∈
        SylowAutStabilizer P
    rw [generalLinearTwoFiveConjugation_scalarTwo]
    exact Subgroup.one_mem _
  let u :
      specialLinearTwoFiveGeneralLinearSylowCover P :=
    ⟨specialLinearTwoFiveGeneralLinearScalarTwo, hSylow⟩
  have hu :
      specialLinearTwoFiveGeneralLinearSylowCoverHom P u = 1 := by
    apply Subtype.ext
    exact generalLinearTwoFiveConjugation_scalarTwo
  refine ⟨u, ?_⟩
  change
    specialLinearTwoFiveGeneralLinearSylowCoverHom P u ∈
      PPrimeCharacterStabilizer P χ
  rw [hu]
  exact Subgroup.one_mem _

@[simp]
theorem specialLinearTwoFiveCharacterCoverScalarTwo_cover :
    specialLinearTwoFiveGeneralLinearCharacterCoverHom P χ
        (specialLinearTwoFiveCharacterCoverScalarTwo P χ) =
      1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact generalLinearTwoFiveConjugation_scalarTwo

@[simp]
theorem specialLinearTwoFiveCharacterCoverScalarTwo_det :
    specialLinearTwoFiveGeneralLinearCharacterCoverDet P χ
        (specialLinearTwoFiveCharacterCoverScalarTwo P χ) =
      zmodFiveUnitFour := by
  change
    Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar
          (Fin 2) zmodFiveUnitTwo) =
      zmodFiveUnitFour
  rw [Matrix.GeneralLinearGroup.det_scalar]
  native_decide

/-- The determinant character used to change the sign at the scalar
generator without changing restriction to the exact normalizer. -/
def specialLinearTwoFiveCharacterCoverScalarCorrection
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p) :
    specialLinearTwoFiveGeneralLinearCharacterCover P χ →* ℂˣ :=
  zmodFiveComplexUnitCharacter.comp
    (specialLinearTwoFiveGeneralLinearCharacterCoverDet P χ)

@[simp]
theorem specialLinearTwoFiveCharacterCoverScalarCorrection_scalarTwo :
    specialLinearTwoFiveCharacterCoverScalarCorrection P χ
        (specialLinearTwoFiveCharacterCoverScalarTwo P χ) =
      -1 := by
  rw [specialLinearTwoFiveCharacterCoverScalarCorrection,
    MonoidHom.comp_apply,
    specialLinearTwoFiveCharacterCoverScalarTwo_det,
    zmodFiveComplexUnitCharacter_four]

@[simp]
theorem specialLinearTwoFiveCharacterCoverScalarCorrection_localEmbedding
    (n : SylowNormalizer P) :
    specialLinearTwoFiveCharacterCoverScalarCorrection P χ
        (specialLinearTwoFiveNormalizerCharacterCoverEmbedding P χ n) =
      1 := by
  change
    zmodFiveComplexUnitCharacter
        (Matrix.GeneralLinearGroup.det
          (Matrix.SpecialLinearGroup.toGL n.1)) =
      1
  simp

/-- The ambient central involution, regarded as an element of the exact
Sylow normalizer. -/
def specialLinearTwoFiveCentralNegOneNormalizer
    (P : Sylow p SpecialLinearTwoFive) :
    SylowNormalizer P :=
  ⟨-1,
    Subgroup.center_le_normalizer (P : Set SpecialLinearTwoFive)
      (by
        rw [Subgroup.mem_center_iff]
        intro g
        simp)⟩

@[simp]
theorem specialLinearTwoFiveCentralNegOneNormalizer_val
    (P : Sylow p SpecialLinearTwoFive) :
    (specialLinearTwoFiveCentralNegOneNormalizer P :
      SpecialLinearTwoFive) =
      -1 :=
  rfl

@[simp]
theorem specialLinearTwoFiveCharacterCoverScalarTwo_sq
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p) :
    (specialLinearTwoFiveCharacterCoverScalarTwo P χ) ^ 2 =
      specialLinearTwoFiveNormalizerCharacterCoverEmbedding P χ
        (specialLinearTwoFiveCentralNegOneNormalizer P) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change
    ((Matrix.GeneralLinearGroup.scalar
        (Fin 2) zmodFiveUnitTwo : GeneralLinearTwoFive) ^ 2 :
      Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      ((Matrix.SpecialLinearGroup.toGL
        (-1 : SpecialLinearTwoFive) : GeneralLinearTwoFive) :
          Matrix (Fin 2) (Fin 2) (ZMod 5))
  native_decide

theorem specialLinearTwoFiveCharacterCoverScalarTwo_central_ambient
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p) :
    specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding P χ
        (specialLinearTwoFiveCharacterCoverScalarTwo P χ) ∈
      Subgroup.center GeneralLinearTwoFive := by
  apply specialLinearTwoFiveCharacterCover_kernel_central_ambient
  rw [MonoidHom.mem_ker]
  exact specialLinearTwoFiveCharacterCoverScalarTwo_cover

theorem specialLinearTwoFiveCharacterCoverScalarTwo_central_local
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p) :
    specialLinearTwoFiveCharacterCoverScalarTwo P χ ∈
      Subgroup.center
        (specialLinearTwoFiveGeneralLinearCharacterCover P χ) := by
  apply specialLinearTwoFiveCharacterCover_kernel_central_local
  rw [MonoidHom.mem_ker]
  exact specialLinearTwoFiveCharacterCoverScalarTwo_cover

/-- Every element of the character-cover kernel is a power of its scalar
generator `2I`. -/
theorem specialLinearTwoFiveCharacterCover_kernel_eq_scalarTwo_pow
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p)
    (l : specialLinearTwoFiveGeneralLinearCharacterCover P χ)
    (hl :
      l ∈
        (specialLinearTwoFiveGeneralLinearCharacterCoverHom P χ).ker) :
    ∃ n : Fin 4,
      l = (specialLinearTwoFiveCharacterCoverScalarTwo P χ) ^ n.val := by
  have hcenter :
      l.1.1 ∈ Subgroup.center GeneralLinearTwoFive :=
    specialLinearTwoFiveCharacterCover_kernel_central_ambient
      P χ l hl
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨u, hu⟩ := hcenter
  obtain ⟨n, hn⟩ := zmodFiveUnit_eq_two_pow u
  refine ⟨n, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  calc
    l.1.1 =
        Matrix.GeneralLinearGroup.scalar (Fin 2) u :=
      hu.symm
    _ =
        Matrix.GeneralLinearGroup.scalar (Fin 2)
          (zmodFiveUnitTwo ^ n.val) := by rw [hn]
    _ =
        (Matrix.GeneralLinearGroup.scalar
          (Fin 2) zmodFiveUnitTwo) ^ n.val := by
      rw [map_pow]
    _ =
        ((specialLinearTwoFiveCharacterCoverScalarTwo P χ) ^
          n.val).1.1 :=
      rfl

/-- Once two extension characters agree on the scalar generator, the
general-linear common cover proves the complete projective clause. -/
theorem EquivariantMcKayEquiv.tripleCompatible_of_generalLinearExtensions_generator_eq
    (P : Sylow p SpecialLinearTwoFive)
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p)
    (ambientExtension :
      IrreducibleCharacter GeneralLinearTwoFive)
    (ambientExtends :
      IrreducibleCharacter.IsExtensionAlong
        Matrix.SpecialLinearGroup.toGL χ.1 ambientExtension)
    (localExtension :
      IrreducibleCharacter
        (specialLinearTwoFiveGeneralLinearCharacterCover P χ))
    (localExtends :
      IrreducibleCharacter.IsExtensionAlong
        (specialLinearTwoFiveNormalizerCharacterCoverEmbedding P χ)
        (e χ).1 localExtension)
    (generator_eq :
      ambientExtension.centralUnit
          (specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding P χ
            (specialLinearTwoFiveCharacterCoverScalarTwo P χ))
          (specialLinearTwoFiveCharacterCoverScalarTwo_central_ambient
            P χ) =
        localExtension.centralUnit
          (specialLinearTwoFiveCharacterCoverScalarTwo P χ)
          (specialLinearTwoFiveCharacterCoverScalarTwo_central_local
            P χ)) :
    e.toExactNormalizerLocalCorrespondence.TripleCompatible χ := by
  apply e.tripleCompatible_of_commonCentralCover χ
      (specialLinearTwoFiveGeneralLinearCharacterCoverHom P χ)
      (specialLinearTwoFiveGeneralLinearCharacterCoverHom_surjective P χ)
      Matrix.SpecialLinearGroup.toGL
      (specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding P χ)
      (specialLinearTwoFiveNormalizerCharacterCoverEmbedding P χ)
      (specialLinearTwoFiveNormalizerCharacterCoverEmbedding_apply P χ)
      (specialLinearTwoFiveCharacterCover_localEmbedding P χ)
      (specialLinearTwoFiveCharacterCover_ambient_conjugates P χ)
      (specialLinearTwoFiveCharacterCover_local_conjugates P χ e)
      (specialLinearTwoFiveCharacterCover_kernel_central_ambient P χ)
      (specialLinearTwoFiveCharacterCover_kernel_central_local P χ)
      ambientExtension ambientExtends localExtension localExtends
  intro l hl
  apply ambientExtension.cross_of_centralUnit_eq localExtension
      (specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding P χ l) l
      (specialLinearTwoFiveCharacterCover_kernel_central_ambient P χ l hl)
      (specialLinearTwoFiveCharacterCover_kernel_central_local P χ l hl)
  obtain ⟨n, rfl⟩ :=
    specialLinearTwoFiveCharacterCover_kernel_eq_scalarTwo_pow
      P χ l hl
  calc
    ambientExtension.centralUnit
          (specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding P χ
            ((specialLinearTwoFiveCharacterCoverScalarTwo P χ) ^ n.val))
          _ =
        (ambientExtension.centralUnit
          (specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding P χ
            (specialLinearTwoFiveCharacterCoverScalarTwo P χ))
          (specialLinearTwoFiveCharacterCoverScalarTwo_central_ambient
            P χ)) ^ n.val := by
      simpa only [map_pow] using
        (ambientExtension.centralUnit_pow
          (specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding P χ
            (specialLinearTwoFiveCharacterCoverScalarTwo P χ))
          (specialLinearTwoFiveCharacterCoverScalarTwo_central_ambient
            P χ) n.val)
    _ =
        (localExtension.centralUnit
          (specialLinearTwoFiveCharacterCoverScalarTwo P χ)
          (specialLinearTwoFiveCharacterCoverScalarTwo_central_local
            P χ)) ^ n.val := by
      rw [generator_eq]
    _ =
        localExtension.centralUnit
          ((specialLinearTwoFiveCharacterCoverScalarTwo P χ) ^ n.val)
          _ := by
      exact
        (localExtension.centralUnit_pow
          (specialLinearTwoFiveCharacterCoverScalarTwo P χ)
          (specialLinearTwoFiveCharacterCoverScalarTwo_central_local
            P χ) n.val).symm

/-- A general-linear invariant row whose ambient and local central
involution scalars agree satisfies the full projective compatibility
clause.  The extension characters are normalized internally, so no
choice of extensions appears in the statement. -/
theorem EquivariantMcKayEquiv.tripleCompatible_of_generalLinearCover
    (P : Sylow p SpecialLinearTwoFive)
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p)
    (ambientInvariant :
      ∀ (u : GeneralLinearTwoFive) (g : SpecialLinearTwoFive),
        χ.1.values (generalLinearTwoFiveConjugation u g) =
          χ.1.values g)
    (centralCross :
      χ.1.values (-1) * ((e χ).1.degree : ℂ) =
        (e χ).1.values
            (specialLinearTwoFiveCentralNegOneNormalizer P) *
          (χ.1.degree : ℂ)) :
    e.toExactNormalizerLocalCorrespondence.TripleCompatible χ := by
  obtain ⟨ambientExtension, ambientExtends⟩ :=
    specialLinearTwoFive_exists_generalLinearExtension
      χ.1 ambientInvariant
  obtain ⟨localExtension, localExtends⟩ :=
    specialLinearTwoFive_exists_characterCoverLocalExtension P χ e
  let scalarTwo :=
    specialLinearTwoFiveCharacterCoverScalarTwo P χ
  let coverEmbedding :=
    specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding P χ
  let localEmbedding :=
    specialLinearTwoFiveNormalizerCharacterCoverEmbedding P χ
  let centralNegOne :=
    specialLinearTwoFiveCentralNegOneNormalizer P
  have negOne_central_ambient :
      (-1 : SpecialLinearTwoFive) ∈
        Subgroup.center SpecialLinearTwoFive := by
    rw [Subgroup.mem_center_iff]
    intro g
    simp
  have negOne_central_normalizer :
      centralNegOne ∈ Subgroup.center (SylowNormalizer P) := by
    rw [Subgroup.mem_center_iff]
    intro n
    apply Subtype.ext
    simp [centralNegOne]
  have negOne_central_generalLinear :
      Matrix.SpecialLinearGroup.toGL (-1 : SpecialLinearTwoFive) ∈
        Subgroup.center GeneralLinearTwoFive :=
    (Matrix.SpecialLinearGroup.toGL_mem_center_iff
      (-1 : SpecialLinearTwoFive)).mpr negOne_central_ambient
  have scalarTwo_central_ambient :
      coverEmbedding scalarTwo ∈
        Subgroup.center GeneralLinearTwoFive :=
    specialLinearTwoFiveCharacterCoverScalarTwo_central_ambient P χ
  have scalarTwo_central_local :
      scalarTwo ∈
        Subgroup.center
          (specialLinearTwoFiveGeneralLinearCharacterCover P χ) :=
    specialLinearTwoFiveCharacterCoverScalarTwo_central_local P χ
  have scalarTwo_sq :
      scalarTwo ^ 2 = localEmbedding centralNegOne :=
    specialLinearTwoFiveCharacterCoverScalarTwo_sq P χ
  have scalarTwo_sq_central_ambient :
      coverEmbedding (scalarTwo ^ 2) ∈
        Subgroup.center GeneralLinearTwoFive := by
    simpa only [map_pow] using
      pow_mem scalarTwo_central_ambient 2
  have scalarTwo_sq_central_local :
      scalarTwo ^ 2 ∈
        Subgroup.center
          (specialLinearTwoFiveGeneralLinearCharacterCover P χ) :=
    pow_mem scalarTwo_central_local 2
  have centralNegOne_image_central :
      localEmbedding centralNegOne ∈
        Subgroup.center
          (specialLinearTwoFiveGeneralLinearCharacterCover P χ) := by
    exact scalarTwo_sq ▸ scalarTwo_sq_central_local
  have scalarTwo_sq_ambient :
      coverEmbedding (scalarTwo ^ 2) =
        Matrix.SpecialLinearGroup.toGL (-1 : SpecialLinearTwoFive) := by
    calc
      coverEmbedding (scalarTwo ^ 2) =
          coverEmbedding (localEmbedding centralNegOne) := by
        rw [scalarTwo_sq]
      _ =
          Matrix.SpecialLinearGroup.toGL centralNegOne.1 :=
        specialLinearTwoFiveNormalizerCharacterCoverEmbedding_apply
          P χ centralNegOne
      _ =
          Matrix.SpecialLinearGroup.toGL
            (-1 : SpecialLinearTwoFive) := by
        rw [specialLinearTwoFiveCentralNegOneNormalizer_val]
  have ambient_negOne_unit :
      ambientExtension.centralUnit
          (Matrix.SpecialLinearGroup.toGL
            (-1 : SpecialLinearTwoFive))
          negOne_central_generalLinear =
        χ.1.centralUnit (-1) negOne_central_ambient :=
    ambientExtends.centralUnit_eq
      (-1 : SpecialLinearTwoFive)
      negOne_central_ambient negOne_central_generalLinear
  have local_negOne_unit :
      localExtension.centralUnit
          (localEmbedding centralNegOne)
          centralNegOne_image_central =
        (e χ).1.centralUnit centralNegOne
          negOne_central_normalizer :=
    localExtends.centralUnit_eq centralNegOne
      negOne_central_normalizer centralNegOne_image_central
  have base_negOne_unit :
      χ.1.centralUnit (-1) negOne_central_ambient =
        (e χ).1.centralUnit centralNegOne
          negOne_central_normalizer :=
    χ.1.centralUnit_eq_of_cross (e χ).1
      (-1 : SpecialLinearTwoFive) centralNegOne
      negOne_central_ambient negOne_central_normalizer
      centralCross
  have scalarTwo_sq_unit :
      ambientExtension.centralUnit
          (coverEmbedding (scalarTwo ^ 2))
          scalarTwo_sq_central_ambient =
        localExtension.centralUnit
          (scalarTwo ^ 2) scalarTwo_sq_central_local := by
    calc
      ambientExtension.centralUnit
          (coverEmbedding (scalarTwo ^ 2))
          scalarTwo_sq_central_ambient =
          ambientExtension.centralUnit
            (Matrix.SpecialLinearGroup.toGL
              (-1 : SpecialLinearTwoFive))
            negOne_central_generalLinear :=
        ambientExtension.centralUnit_congr
          scalarTwo_sq_central_ambient
          negOne_central_generalLinear scalarTwo_sq_ambient
      _ =
          χ.1.centralUnit (-1) negOne_central_ambient :=
        ambient_negOne_unit
      _ =
          (e χ).1.centralUnit centralNegOne
            negOne_central_normalizer :=
        base_negOne_unit
      _ =
          localExtension.centralUnit
            (localEmbedding centralNegOne)
            centralNegOne_image_central :=
        local_negOne_unit.symm
      _ =
          localExtension.centralUnit
            (scalarTwo ^ 2) scalarTwo_sq_central_local :=
        localExtension.centralUnit_congr
          centralNegOne_image_central
          scalarTwo_sq_central_local scalarTwo_sq.symm
  have generator_sq_eq :
      (ambientExtension.centralUnit
          (coverEmbedding scalarTwo)
          scalarTwo_central_ambient) ^ 2 =
        (localExtension.centralUnit scalarTwo
          scalarTwo_central_local) ^ 2 := by
    calc
      (ambientExtension.centralUnit
          (coverEmbedding scalarTwo)
          scalarTwo_central_ambient) ^ 2 =
          ambientExtension.centralUnit
            ((coverEmbedding scalarTwo) ^ 2)
            (pow_mem scalarTwo_central_ambient 2) :=
        (ambientExtension.centralUnit_pow
          (coverEmbedding scalarTwo)
          scalarTwo_central_ambient 2).symm
      _ =
          ambientExtension.centralUnit
            (coverEmbedding (scalarTwo ^ 2))
            scalarTwo_sq_central_ambient :=
        ambientExtension.centralUnit_congr
          (pow_mem scalarTwo_central_ambient 2)
          scalarTwo_sq_central_ambient
          (map_pow coverEmbedding scalarTwo 2).symm
      _ =
          localExtension.centralUnit
            (scalarTwo ^ 2) scalarTwo_sq_central_local :=
        scalarTwo_sq_unit
      _ =
          (localExtension.centralUnit scalarTwo
            scalarTwo_central_local) ^ 2 :=
        localExtension.centralUnit_pow scalarTwo
          scalarTwo_central_local 2
  rcases complexUnit_eq_or_eq_neg_mul_of_sq_eq generator_sq_eq with
      generator_eq | generator_eq
  · exact
      e.tripleCompatible_of_generalLinearExtensions_generator_eq
        P χ ambientExtension ambientExtends
        localExtension localExtends generator_eq
  · let correctedLocal :=
      IrreducibleCharacter.twist
        (specialLinearTwoFiveCharacterCoverScalarCorrection P χ)
        localExtension
    have correctedLocalExtends :
        IrreducibleCharacter.IsExtensionAlong localEmbedding
          (e χ).1 correctedLocal := by
      apply localExtends.twist_of_eq_one
      intro n
      exact
        specialLinearTwoFiveCharacterCoverScalarCorrection_localEmbedding
          (P := P) (χ := χ) n
    have corrected_generator_eq :
        ambientExtension.centralUnit
            (coverEmbedding scalarTwo)
            scalarTwo_central_ambient =
          correctedLocal.centralUnit scalarTwo
            scalarTwo_central_local := by
      calc
        ambientExtension.centralUnit
              (coverEmbedding scalarTwo)
              scalarTwo_central_ambient =
            -1 *
              localExtension.centralUnit scalarTwo
                scalarTwo_central_local :=
          generator_eq
        _ =
            correctedLocal.centralUnit scalarTwo
              scalarTwo_central_local := by
          change
            -1 * localExtension.centralUnit scalarTwo
                scalarTwo_central_local =
              (IrreducibleCharacter.twist
                (specialLinearTwoFiveCharacterCoverScalarCorrection P χ)
                localExtension).centralUnit scalarTwo
                scalarTwo_central_local
          rw [IrreducibleCharacter.twist_centralUnit,
            specialLinearTwoFiveCharacterCoverScalarCorrection_scalarTwo]
    exact
      e.tripleCompatible_of_generalLinearExtensions_generator_eq
        P χ ambientExtension ambientExtends
        correctedLocal correctedLocalExtends corrected_generator_eq

end InductiveMcKay
end McKayConjecture
