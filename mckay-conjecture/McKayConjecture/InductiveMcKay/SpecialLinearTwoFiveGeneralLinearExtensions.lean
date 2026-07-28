/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CyclicExtensionAlong
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveGeneralLinearStabilizerCover

/-!
# Cyclic extension characters for the `GL(2, 𝔽₅)` covers

The ambient inclusion `SL(2, 𝔽₅) → GL(2, 𝔽₅)` has cyclic quotient.  For
each Sylow-character stabilizer, the exact normalizer has cyclic quotient
inside its general-linear inverse image as well.  Character invariance
therefore supplies honest ambient and local extension characters.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {p : ℕ}

/-- An irreducible character of `SL(2, 𝔽₅)` invariant under all
general-linear conjugations extends to `GL(2, 𝔽₅)`. -/
theorem specialLinearTwoFive_exists_generalLinearExtension
    (χ : IrreducibleCharacter SpecialLinearTwoFive)
    (invariant :
      ∀ (u : GeneralLinearTwoFive) (g : SpecialLinearTwoFive),
        χ.values (generalLinearTwoFiveConjugation u g) =
          χ.values g) :
  ∃ ψ : IrreducibleCharacter GeneralLinearTwoFive,
      IrreducibleCharacter.IsExtensionAlong
        Matrix.SpecialLinearGroup.toGL χ ψ := by
  apply
    IrreducibleCharacter.exists_extensionAlong_of_injective_cyclic_range
      Matrix.SpecialLinearGroup.toGL
      Matrix.SpecialLinearGroup.toGL_injective
      specialLinearTwoFive_toGL_range_normal
      specialLinearTwoFive_generalLinearQuotient_isCyclic
      generalLinearTwoFiveConjugation
  · intro u g
    apply Units.ext
    exact generalLinearTwoFiveConjugation_apply u g
  · exact invariant

/-- Determinant restricted to a general-linear character cover. -/
def specialLinearTwoFiveGeneralLinearCharacterCoverDet
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p) :
    specialLinearTwoFiveGeneralLinearCharacterCover P χ →*
      (ZMod 5)ˣ :=
  Matrix.GeneralLinearGroup.det.comp
    (specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding P χ)

@[simp]
theorem specialLinearTwoFiveGeneralLinearCharacterCoverDet_apply
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p)
    (l : specialLinearTwoFiveGeneralLinearCharacterCover P χ) :
    specialLinearTwoFiveGeneralLinearCharacterCoverDet P χ l =
      Matrix.GeneralLinearGroup.det l.1.1 :=
  rfl

/-- Inside a character cover, the determinant-one elements are exactly
the embedded exact Sylow normalizer. -/
theorem
    specialLinearTwoFiveNormalizerCharacterCoverEmbedding_range_eq_detKer
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p) :
    (specialLinearTwoFiveNormalizerCharacterCoverEmbedding P χ).range =
      (specialLinearTwoFiveGeneralLinearCharacterCoverDet P χ).ker := by
  ext l
  constructor
  · rintro ⟨n, rfl⟩
    change
      Matrix.GeneralLinearGroup.det
          (Matrix.SpecialLinearGroup.toGL n.1) =
        1
    simp
  · intro hl
    have hdet :
        Matrix.GeneralLinearGroup.det l.1.1 = 1 := by
      exact MonoidHom.mem_ker.mp hl
    let x : specialLinearTwoFiveInGeneralLinear :=
      ⟨l.1.1, hdet⟩
    let g : SpecialLinearTwoFive :=
      specialLinearTwoFiveEquivDetKernel.symm x
    have hg :
        Matrix.SpecialLinearGroup.toGL g = l.1.1 := by
      exact
        congrArg Subtype.val
          (specialLinearTwoFiveEquivDetKernel.apply_symm_apply x)
    have hstabilizes :
        (MulAut.conj g) • P = P := by
      have hlSylow :
          generalLinearTwoFiveConjugation l.1.1 ∈
            SylowAutStabilizer P :=
        l.1.2
      rw [SylowAutStabilizer.mem_iff] at hlSylow
      rw [← hg, generalLinearTwoFiveConjugation_toGL] at hlSylow
      exact hlSylow
    have hgNormalizer :
        g ∈ Subgroup.normalizer (P : Set SpecialLinearTwoFive) := by
      rw [Subgroup.mem_normalizer_iff_conj_image_eq]
      exact
        congrArg
          (fun Q : Sylow p SpecialLinearTwoFive ↦
            (Q : Set SpecialLinearTwoFive))
          hstabilizes
    let n : SylowNormalizer P := ⟨g, hgNormalizer⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hg

/-- The embedded exact normalizer is normal in its character cover. -/
instance
    specialLinearTwoFiveNormalizerCharacterCoverEmbedding_range_normal
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p) :
    (specialLinearTwoFiveNormalizerCharacterCoverEmbedding P χ).range.Normal := by
  rw [
    specialLinearTwoFiveNormalizerCharacterCoverEmbedding_range_eq_detKer]
  infer_instance

/-- The quotient of a character cover by the exact normalizer is cyclic. -/
theorem
    specialLinearTwoFiveNormalizerCharacterCoverQuotient_isCyclic
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p) :
    IsCyclic
      (specialLinearTwoFiveGeneralLinearCharacterCover P χ ⧸
        (specialLinearTwoFiveNormalizerCharacterCoverEmbedding
          P χ).range) := by
  let δ :=
    specialLinearTwoFiveGeneralLinearCharacterCoverDet P χ
  letI : IsCyclic (ZMod 5)ˣ :=
    ZMod.isCyclic_units_prime Nat.prime_five
  have hcyclicKer :
      IsCyclic
        (specialLinearTwoFiveGeneralLinearCharacterCover P χ ⧸
          δ.ker) := by
    exact
      (QuotientGroup.quotientKerEquivRange δ).isCyclic.mpr
        inferInstance
  let e :
      specialLinearTwoFiveGeneralLinearCharacterCover P χ ⧸
          (specialLinearTwoFiveNormalizerCharacterCoverEmbedding
            P χ).range ≃*
        specialLinearTwoFiveGeneralLinearCharacterCover P χ ⧸
          δ.ker :=
    QuotientGroup.quotientMulEquivOfEq
      (specialLinearTwoFiveNormalizerCharacterCoverEmbedding_range_eq_detKer
        P χ)
  exact e.isCyclic.mpr hcyclicKer

/-- The character cover acts on the exact Sylow normalizer through the
restricted stabilizer action. -/
def specialLinearTwoFiveCharacterCoverNormalizerAction
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p)
    (e : EquivariantMcKayEquiv P) :
    specialLinearTwoFiveGeneralLinearCharacterCover P χ →*
      MulAut (SylowNormalizer P) :=
  (e.toExactNormalizerLocalCorrespondence
      |>.stabilizerIntermediateAction χ).comp
    (specialLinearTwoFiveGeneralLinearCharacterCoverHom P χ)

/-- The local character paired by an equivariant McKay equivalence extends
to the corresponding general-linear character cover. -/
theorem specialLinearTwoFive_exists_characterCoverLocalExtension
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p)
    (e : EquivariantMcKayEquiv P) :
    ∃ ψ :
        IrreducibleCharacter
          (specialLinearTwoFiveGeneralLinearCharacterCover P χ),
      IrreducibleCharacter.IsExtensionAlong
        (specialLinearTwoFiveNormalizerCharacterCoverEmbedding P χ)
        (e χ).1 ψ := by
  apply
    IrreducibleCharacter.exists_extensionAlong_of_injective_cyclic_range
      (specialLinearTwoFiveNormalizerCharacterCoverEmbedding P χ)
      (by
        intro n m h
        apply Subtype.ext
        exact
          Matrix.SpecialLinearGroup.toGL_injective
            (congrArg
              (specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding
                P χ) h))
      (specialLinearTwoFiveNormalizerCharacterCoverEmbedding_range_normal
        P χ)
      (specialLinearTwoFiveNormalizerCharacterCoverQuotient_isCyclic
        P χ)
      (specialLinearTwoFiveCharacterCoverNormalizerAction P χ e)
  · intro l n
    exact
      specialLinearTwoFiveCharacterCover_local_conjugates
        P χ e l n
  · intro l n
    exact
      e.toExactNormalizerLocalCorrespondence
        |>.localCharacter_invariant χ
          (specialLinearTwoFiveGeneralLinearCharacterCoverHom P χ l) n

end InductiveMcKay
end McKayConjecture
