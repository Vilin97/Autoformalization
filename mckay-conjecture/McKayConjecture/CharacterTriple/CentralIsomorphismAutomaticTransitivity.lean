/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedRescale
import McKayConjecture.CharacterTriple.AssociatedUniqueness
import McKayConjecture.CharacterTriple.Transitivity

/-!
# Automatic transitivity of central character-triple isomorphisms

Two composable central-isomorphism witnesses may use unrelated associated
projective representations for their common middle triple.  Associated-lift
uniqueness supplies a scalar gauge which makes the two middle factor sets
agree.  Rescaling both projective representations in the second witness by
that gauge (and its pullback along the second embedding) preserves every
field of that witness.

The adjusted second witness is automatically compatible with the first one,
so central isomorphisms compose without an additional coherence hypothesis.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple
namespace CentralIsomorphismWitness

variable {A : Type u} {B : Type v} {D : Type w}
  [Finite A] [Finite B] [Finite D]
  [Group A] [Group B] [Group D]
variable {T : CharacterTriple A} {U : CharacterTriple B}
  {Z : CharacterTriple D}
variable {V W W' Y : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup W'] [Module ℂ W'] [Module.Finite ℂ W'] [Nontrivial W']
  [AddCommGroup Y] [Module ℂ Y] [Module.Finite ℂ Y] [Nontrivial Y]

/-- The equivalence between the two chosen realizations of the common
middle character. -/
abbrev middleRestrictionEquiv
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) :=
  AssociatedProjectiveRepresentation.restrictionEquiv
    C₁.rightAssociated C₂.leftAssociated

/-- The scalar gauge which aligns the second witness's left projective
representation with the first witness's right projective representation. -/
abbrev middleGauge
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) :
    B → ℂˣ :=
  AssociatedProjectiveRepresentation.gaugeScalar
    C₁.rightAssociated C₂.leftAssociated
    (middleRestrictionEquiv C₁ C₂)

/-- Pull the middle alignment gauge back through the second embedding. -/
abbrev rightMiddleGauge
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) :
    D → ℂˣ :=
  fun d ↦ middleGauge C₁ C₂ (C₂.embedding d)

theorem rightMiddleGauge_normal
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y)
    (x : Z.normalSubgroup) :
    rightMiddleGauge C₁ C₂ (x : D) = 1 := by
  exact
    AssociatedProjectiveRepresentation.gaugeScalar_normal
      C₁.rightAssociated C₂.leftAssociated
      (middleRestrictionEquiv C₁ C₂)
      ⟨C₂.embedding x,
        C₂.embedding_rightNormal_mem_leftNormal x⟩

theorem rightMiddleGauge_normal_mul
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y)
    (x : Z.normalSubgroup) (d : D) :
    rightMiddleGauge C₁ C₂ ((x : D) * d) =
      rightMiddleGauge C₁ C₂ d := by
  change
    middleGauge C₁ C₂
        (C₂.embedding ((x : D) * d)) =
      middleGauge C₁ C₂ (C₂.embedding d)
  rw [map_mul]
  exact
    AssociatedProjectiveRepresentation.gaugeScalar_normal_mul
      C₁.rightAssociated C₂.leftAssociated
      (middleRestrictionEquiv C₁ C₂)
      ⟨C₂.embedding x,
        C₂.embedding_rightNormal_mem_leftNormal x⟩
      (C₂.embedding d)

theorem rightMiddleGauge_mul_normal
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y)
    (d : D) (x : Z.normalSubgroup) :
    rightMiddleGauge C₁ C₂ (d * (x : D)) =
      rightMiddleGauge C₁ C₂ d := by
  change
    middleGauge C₁ C₂
        (C₂.embedding (d * (x : D))) =
      middleGauge C₁ C₂ (C₂.embedding d)
  rw [map_mul]
  exact
    AssociatedProjectiveRepresentation.gaugeScalar_mul_normal
      C₁.rightAssociated C₂.leftAssociated
      (middleRestrictionEquiv C₁ C₂)
      (C₂.embedding d)
      ⟨C₂.embedding x,
        C₂.embedding_rightNormal_mem_leftNormal x⟩

/-- Rescale both sides of the second witness so that its left factor set
literally agrees with the first witness's right factor set. -/
def alignSecond
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) :
    CentralIsomorphismWitness U Z W' Y where
  leftProjective :=
    C₂.leftProjective.rescale (middleGauge C₁ C₂)
  leftAssociated :=
    AssociatedProjectiveRepresentation.rescaleAssociated
      C₁.rightAssociated C₂.leftAssociated
      (middleRestrictionEquiv C₁ C₂)
  rightProjective :=
    C₂.rightProjective.rescale (rightMiddleGauge C₁ C₂)
  rightAssociated :=
    C₂.rightAssociated.rescaleOfNormalTrivialCosetConstant
      (rightMiddleGauge C₁ C₂)
      (rightMiddleGauge_normal C₁ C₂)
      (rightMiddleGauge_normal_mul C₁ C₂)
      (rightMiddleGauge_mul_normal C₁ C₂)
  embedding := C₂.embedding
  embedding_injective := C₂.embedding_injective
  centralizer_le := C₂.centralizer_le
  ambient_eq_product := C₂.ambient_eq_product
  intersection_eq := C₂.intersection_eq
  factor_agreement := by
    intro d e
    simp only [ProjectiveRepresentation.rescale_factor,
      rightMiddleGauge, map_mul]
    rw [C₂.factor_agreement d e]
  scalar_agreement := by
    intro d hd
    obtain ⟨c, hleft, hright⟩ :=
      C₂.scalar_agreement d hd
    refine ⟨middleGauge C₁ C₂ (C₂.embedding d) * c, ?_, ?_⟩
    · rw [ProjectiveRepresentation.rescale_operator, hleft,
        scalarLinearEquiv_mul]
    · rw [ProjectiveRepresentation.rescale_operator, hright,
        scalarLinearEquiv_mul]

/-- The gauge-adjusted second witness is compatible with the first one. -/
theorem middleCompatibility_alignSecond
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) :
    MiddleCompatibility C₁ (alignSecond C₁ C₂) where
  factor_agreement := by
    intro d e
    exact
      AssociatedProjectiveRepresentation.gauge_factor_eq
        C₁.rightAssociated C₂.leftAssociated
        (middleRestrictionEquiv C₁ C₂)
        (C₂.embedding d) (C₂.embedding e)
  scalar_agreement := by
    intro d hd
    have hdMiddle :
        C₂.embedding d ∈
          Subgroup.centralizer (U.normalSubgroup : Set B) :=
      C₁.mem_rightCentralizer_of_embedding_mem_leftCentralizer hd
    obtain ⟨c, hright⟩ :=
      C₁.rightAssociated.operator_centralizer_isScalar
        (C₂.embedding d) hdMiddle
    refine ⟨c, hright, ?_⟩
    apply LinearEquiv.ext
    intro y
    let E := middleRestrictionEquiv C₁ C₂
    obtain ⟨x, rfl⟩ := E.toLinearEquiv.surjective y
    change
      (C₂.leftProjective.rescale
          (AssociatedProjectiveRepresentation.gaugeScalar
            C₁.rightAssociated C₂.leftAssociated E)).operator
          (C₂.embedding d) (E x) =
        (c : ℂ) • E x
    have hoperator :=
      AssociatedProjectiveRepresentation.gauge_operator_eq
        C₁.rightAssociated C₂.leftAssociated E
        (C₂.embedding d) x
    rw [hright] at hoperator
    simpa only [scalarLinearEquiv_apply, map_smul] using hoperator.symm

/-- A stronger alignment of the second witness: transport its aligned left
factor back to the first middle realization, so the two middle projective
representations are literally the same object.  This form supports the
literal functoriality theorems for the induced character correspondences. -/
def alignSecondOnFirstMiddleSpace
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) :
    CentralIsomorphismWitness U Z W Y where
  leftProjective := C₁.rightProjective
  leftAssociated := C₁.rightAssociated
  rightProjective :=
    C₂.rightProjective.rescale (rightMiddleGauge C₁ C₂)
  rightAssociated :=
    C₂.rightAssociated.rescaleOfNormalTrivialCosetConstant
      (rightMiddleGauge C₁ C₂)
      (rightMiddleGauge_normal C₁ C₂)
      (rightMiddleGauge_normal_mul C₁ C₂)
      (rightMiddleGauge_mul_normal C₁ C₂)
  embedding := C₂.embedding
  embedding_injective := C₂.embedding_injective
  centralizer_le := C₂.centralizer_le
  ambient_eq_product := C₂.ambient_eq_product
  intersection_eq := C₂.intersection_eq
  factor_agreement := by
    intro d e
    calc
      C₁.rightProjective.factor
          (C₂.embedding d) (C₂.embedding e) =
        (C₂.leftProjective.rescale
          (middleGauge C₁ C₂)).factor
            (C₂.embedding d) (C₂.embedding e) :=
        AssociatedProjectiveRepresentation.gauge_factor_eq
          C₁.rightAssociated C₂.leftAssociated
          (middleRestrictionEquiv C₁ C₂)
          (C₂.embedding d) (C₂.embedding e)
      _ =
        (C₂.rightProjective.rescale
          (rightMiddleGauge C₁ C₂)).factor d e :=
        (alignSecond C₁ C₂).factor_agreement d e
  scalar_agreement := by
    intro d hd
    obtain ⟨c, hfirst⟩ :=
      C₁.rightAssociated.operator_centralizer_isScalar
        (C₂.embedding d) hd
    obtain ⟨r, hleft, hright⟩ :=
      C₂.scalar_agreement d hd
    let E := middleRestrictionEquiv C₁ C₂
    have halignedLeft :
        (C₂.leftProjective.rescale
            (middleGauge C₁ C₂)).operator
              (C₂.embedding d) =
          scalarLinearEquiv ℂ W' c := by
      apply LinearEquiv.ext
      intro y
      obtain ⟨x, rfl⟩ := E.toLinearEquiv.surjective y
      change
        (C₂.leftProjective.rescale
            (AssociatedProjectiveRepresentation.gaugeScalar
              C₁.rightAssociated C₂.leftAssociated E)).operator
            (C₂.embedding d) (E x) =
          (c : ℂ) • E x
      have hoperator :=
        AssociatedProjectiveRepresentation.gauge_operator_eq
          C₁.rightAssociated C₂.leftAssociated E
          (C₂.embedding d) x
      rw [hfirst] at hoperator
      simpa only [scalarLinearEquiv_apply, map_smul] using hoperator.symm
    have hgauge :
        middleGauge C₁ C₂ (C₂.embedding d) * r = c := by
      apply scalarLinearEquiv_injective ℂ W'
      calc
        scalarLinearEquiv ℂ W'
            (middleGauge C₁ C₂ (C₂.embedding d) * r) =
          scalarLinearEquiv ℂ W'
              (middleGauge C₁ C₂ (C₂.embedding d)) *
            scalarLinearEquiv ℂ W' r :=
          scalarLinearEquiv_mul (K := ℂ) (V := W') _ _
        _ =
          (C₂.leftProjective.rescale
            (middleGauge C₁ C₂)).operator
              (C₂.embedding d) := by
            rw [ProjectiveRepresentation.rescale_operator, hleft]
        _ = scalarLinearEquiv ℂ W' c :=
          halignedLeft
    refine ⟨c, hfirst, ?_⟩
    rw [ProjectiveRepresentation.rescale_operator, hright,
      ← scalarLinearEquiv_mul, hgauge]

/-- The strict alignment really shares the first witness's middle
projective representation definitionally. -/
@[simp]
theorem alignSecondOnFirstMiddleSpace_leftProjective
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) :
    (alignSecondOnFirstMiddleSpace C₁ C₂).leftProjective =
      C₁.rightProjective :=
  rfl

/-- Central-isomorphism witnesses compose unconditionally: the necessary
middle coherence is supplied canonically by associated-lift uniqueness. -/
def composeAutomatic
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) :
    CentralIsomorphismWitness T Z V Y :=
  C₁.compose
    (alignSecond C₁ C₂)
    (middleCompatibility_alignSecond C₁ C₂)

/-- Automatic composition in the strict-middle form.  In addition to
producing the same outer relation, this version is directly compatible with
`centralCharacterEquiv_compose_of_projective_eq`. -/
def composeAutomaticStrict
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) :
    CentralIsomorphismWitness T Z V Y :=
  C₁.compose_of_projective_eq
    (alignSecondOnFirstMiddleSpace C₁ C₂) rfl

@[simp]
theorem composeAutomatic_embedding
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) :
    (C₁.composeAutomatic C₂).embedding =
      C₁.embedding.comp C₂.embedding :=
  rfl

@[simp]
theorem composeAutomaticStrict_embedding
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) :
    (C₁.composeAutomaticStrict C₂).embedding =
      C₁.embedding.comp C₂.embedding :=
  rfl

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
