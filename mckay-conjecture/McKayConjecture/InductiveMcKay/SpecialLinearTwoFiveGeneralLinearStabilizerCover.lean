/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveGeneralLinearCover
import McKayConjecture.InductiveMcKay.InnerCharacterStabilizer

/-!
# General-linear covers of character stabilizers for `SL(2, 𝔽₅)`

The inverse image in `GL(2, 𝔽₅)` of a Sylow stabilizer, and then of a
character stabilizer, gives the common central cover used in the explicit
projective rows.  This file packages the cover, its exact-normalizer
embedding, conjugation identities, surjectivity, and central-kernel facts.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {p : ℕ}

/-- The inverse image in `GL(2, 𝔽₅)` of the automorphisms stabilizing a
chosen Sylow subgroup. -/
def specialLinearTwoFiveGeneralLinearSylowCover
    (P : Sylow p SpecialLinearTwoFive) :
    Subgroup GeneralLinearTwoFive :=
  (SylowAutStabilizer P).comap
    generalLinearTwoFiveConjugation

/-- The natural map from the general-linear Sylow cover to the Sylow
automorphism stabilizer. -/
def specialLinearTwoFiveGeneralLinearSylowCoverHom
    (P : Sylow p SpecialLinearTwoFive) :
    specialLinearTwoFiveGeneralLinearSylowCover P →*
      SylowAutStabilizer P :=
  (generalLinearTwoFiveConjugation.domRestrict
      (specialLinearTwoFiveGeneralLinearSylowCover P)).codRestrict
    (SylowAutStabilizer P) (fun u ↦ u.2)

@[simp]
theorem specialLinearTwoFiveGeneralLinearSylowCoverHom_apply
    (P : Sylow p SpecialLinearTwoFive)
    (u : specialLinearTwoFiveGeneralLinearSylowCover P) :
    (specialLinearTwoFiveGeneralLinearSylowCoverHom P u).1 =
      generalLinearTwoFiveConjugation u.1 :=
  rfl

/-- The inverse image of the stabilizer of one `p'`-degree character. -/
def specialLinearTwoFiveGeneralLinearCharacterCover
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p) :
    Subgroup (specialLinearTwoFiveGeneralLinearSylowCover P) :=
  (PPrimeCharacterStabilizer P χ).comap
    (specialLinearTwoFiveGeneralLinearSylowCoverHom P)

/-- The natural epimorphism from the general-linear character cover to
the character stabilizer. -/
def specialLinearTwoFiveGeneralLinearCharacterCoverHom
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p) :
    specialLinearTwoFiveGeneralLinearCharacterCover P χ →*
      PPrimeCharacterStabilizer P χ :=
  ((specialLinearTwoFiveGeneralLinearSylowCoverHom P).domRestrict
      (specialLinearTwoFiveGeneralLinearCharacterCover P χ)).codRestrict
    (PPrimeCharacterStabilizer P χ) (fun u ↦ u.2)

@[simp]
theorem specialLinearTwoFiveGeneralLinearCharacterCoverHom_apply
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p)
    (u : specialLinearTwoFiveGeneralLinearCharacterCover P χ) :
    (specialLinearTwoFiveGeneralLinearCharacterCoverHom P χ u).1.1 =
      generalLinearTwoFiveConjugation u.1.1 :=
  rfl

/-- Inclusion of the character cover into the full general linear group. -/
def specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p) :
    specialLinearTwoFiveGeneralLinearCharacterCover P χ →*
      GeneralLinearTwoFive :=
  (specialLinearTwoFiveGeneralLinearSylowCover P).subtype.comp
    (specialLinearTwoFiveGeneralLinearCharacterCover P χ).subtype

@[simp]
theorem specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding_apply
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p)
    (u : specialLinearTwoFiveGeneralLinearCharacterCover P χ) :
    specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding P χ u =
      u.1.1 :=
  rfl

/-- The exact Sylow normalizer embeds in every character cover through
its usual inclusion in `SL(2, 𝔽₅)`. -/
def specialLinearTwoFiveNormalizerCharacterCoverEmbedding
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p) :
    SylowNormalizer P →*
      specialLinearTwoFiveGeneralLinearCharacterCover P χ where
  toFun n := by
    let a := normalizerInnerCharacterStabilizerHom P χ n
    let u : GeneralLinearTwoFive :=
      Matrix.SpecialLinearGroup.toGL n.1
    have hu :
        generalLinearTwoFiveConjugation u = a.1.1 := by
      change
        generalLinearTwoFiveConjugation
            (Matrix.SpecialLinearGroup.toGL n.1) =
          MulAut.conj n.1
      simp
    have hSylow :
        u ∈ specialLinearTwoFiveGeneralLinearSylowCover P := by
      change generalLinearTwoFiveConjugation u ∈
        SylowAutStabilizer P
      rw [hu]
      exact a.1.2
    refine ⟨⟨u, hSylow⟩, ?_⟩
    change
      specialLinearTwoFiveGeneralLinearSylowCoverHom P
          ⟨u, hSylow⟩ ∈
        PPrimeCharacterStabilizer P χ
    have ha :
        specialLinearTwoFiveGeneralLinearSylowCoverHom P
            ⟨u, hSylow⟩ =
          a.1 := by
      apply Subtype.ext
      exact hu
    rw [ha]
    exact a.2
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' n m := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rfl

@[simp]
theorem specialLinearTwoFiveNormalizerCharacterCoverEmbedding_apply
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p)
    (n : SylowNormalizer P) :
    specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding P χ
        (specialLinearTwoFiveNormalizerCharacterCoverEmbedding P χ n) =
      Matrix.SpecialLinearGroup.toGL n.1 :=
  rfl

/-- The character-cover map is onto. -/
theorem specialLinearTwoFiveGeneralLinearCharacterCoverHom_surjective
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p) :
    Function.Surjective
      (specialLinearTwoFiveGeneralLinearCharacterCoverHom P χ) := by
  intro a
  obtain ⟨u, hu⟩ :=
    generalLinearTwoFiveConjugation_surjective a.1.1
  have hSylow :
      u ∈ specialLinearTwoFiveGeneralLinearSylowCover P := by
    change generalLinearTwoFiveConjugation u ∈
      SylowAutStabilizer P
    rw [hu]
    exact a.1.2
  let v : specialLinearTwoFiveGeneralLinearSylowCover P :=
    ⟨u, hSylow⟩
  have hv :
      specialLinearTwoFiveGeneralLinearSylowCoverHom P v = a.1 := by
    apply Subtype.ext
    exact hu
  have hCharacter :
      v ∈ specialLinearTwoFiveGeneralLinearCharacterCover P χ := by
    change
      specialLinearTwoFiveGeneralLinearSylowCoverHom P v ∈
        PPrimeCharacterStabilizer P χ
    rw [hv]
    exact a.2
  refine ⟨⟨v, hCharacter⟩, ?_⟩
  apply Subtype.ext
  exact hv

@[simp]
theorem specialLinearTwoFiveCharacterCover_localEmbedding
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p)
    (n : SylowNormalizer P) :
    specialLinearTwoFiveGeneralLinearCharacterCoverHom P χ
        (specialLinearTwoFiveNormalizerCharacterCoverEmbedding P χ n) =
      normalizerInnerCharacterStabilizerHom P χ n := by
  apply Subtype.ext
  apply Subtype.ext
  change
    generalLinearTwoFiveConjugation
        (Matrix.SpecialLinearGroup.toGL n.1) =
      MulAut.conj n.1
  simp

/-- Conjugation through the character cover realizes its ambient action. -/
theorem specialLinearTwoFiveCharacterCover_ambient_conjugates
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p)
    (l : specialLinearTwoFiveGeneralLinearCharacterCover P χ)
    (g : SpecialLinearTwoFive) :
    Matrix.SpecialLinearGroup.toGL
        (PPrimeCharacterStabilizer.ambientAction
          (specialLinearTwoFiveGeneralLinearCharacterCoverHom P χ l) g) =
      specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding P χ l *
        Matrix.SpecialLinearGroup.toGL g *
        (specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding
          P χ l)⁻¹ := by
  apply Units.ext
  change
    ((generalLinearTwoFiveConjugation l.1.1) g :
        Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      _
  exact generalLinearTwoFiveConjugation_apply l.1.1 g

/-- Conjugation through the character cover also realizes the restricted
action on the exact Sylow normalizer. -/
theorem specialLinearTwoFiveCharacterCover_local_conjugates
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p)
    (e : EquivariantMcKayEquiv P)
    (l : specialLinearTwoFiveGeneralLinearCharacterCover P χ)
    (n : SylowNormalizer P) :
    specialLinearTwoFiveNormalizerCharacterCoverEmbedding P χ
        (e.toExactNormalizerLocalCorrespondence
          |>.stabilizerIntermediateAction χ
            (specialLinearTwoFiveGeneralLinearCharacterCoverHom P χ l) n) =
      l *
        specialLinearTwoFiveNormalizerCharacterCoverEmbedding P χ n *
        l⁻¹ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change
    ((generalLinearTwoFiveConjugation l.1.1) n.1 :
        Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      _
  exact generalLinearTwoFiveConjugation_apply l.1.1 n.1

/-- The character-cover kernel embeds centrally in the full general
linear group. -/
theorem specialLinearTwoFiveCharacterCover_kernel_central_ambient
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p)
    (l : specialLinearTwoFiveGeneralLinearCharacterCover P χ)
    (hl :
      l ∈
        (specialLinearTwoFiveGeneralLinearCharacterCoverHom P χ).ker) :
    specialLinearTwoFiveGeneralLinearCharacterCoverEmbedding P χ l ∈
      Subgroup.center GeneralLinearTwoFive := by
  apply generalLinearTwoFiveConjugation_ker_le_center
  rw [MonoidHom.mem_ker]
  have hcover :
      specialLinearTwoFiveGeneralLinearCharacterCoverHom P χ l = 1 :=
    MonoidHom.mem_ker.mp hl
  exact congrArg (fun a : PPrimeCharacterStabilizer P χ ↦ a.1.1) hcover

/-- The same kernel is central inside the character cover itself. -/
theorem specialLinearTwoFiveCharacterCover_kernel_central_local
    (P : Sylow p SpecialLinearTwoFive)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive p)
    (l : specialLinearTwoFiveGeneralLinearCharacterCover P χ)
    (hl :
      l ∈
        (specialLinearTwoFiveGeneralLinearCharacterCoverHom P χ).ker) :
    l ∈
      Subgroup.center
        (specialLinearTwoFiveGeneralLinearCharacterCover P χ) := by
  rw [Subgroup.mem_center_iff]
  intro m
  apply Subtype.ext
  apply Subtype.ext
  exact
    Subgroup.mem_center_iff.mp
      (specialLinearTwoFiveCharacterCover_kernel_central_ambient
        P χ l hl)
      m.1.1

end InductiveMcKay
end McKayConjecture
