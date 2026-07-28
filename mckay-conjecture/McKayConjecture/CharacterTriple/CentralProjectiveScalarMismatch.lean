/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralIsomorphism

/-!
# The scalar mismatch of two projective lifts

Suppose projective representations associated with two character triples
have literally equal factor sets along a homomorphism.  On the inverse image
of the left centralizer, Schur's lemma makes both projective operators scalar.
The quotient of those two scalars is independent of projective
multiplication: equality of the factor sets makes it a genuine linear
character.

Consequently the scalar clause in a central character-triple comparison is
equivalent to triviality of one explicit multiplicative character.  This
isolates the part of a Dade--Glauberman--Nagao comparison which is not
supplied merely by matching factor sets.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple

universe u v

variable {A : Type u} {B : Type v}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
variable {Q : ProjectiveRepresentation ℂ B W}

/-- The elements on the right whose images centralize the left normal
subgroup. -/
abbrev projectiveComparisonCentralizer
    (T : CharacterTriple A) (e : B →* A) : Subgroup B :=
  (Subgroup.centralizer
    (T.normalSubgroup : Set A)).comap e

namespace AssociatedProjectiveRepresentation

/-- The scalar selected by Schur's lemma for the left projective operator. -/
def leftComparisonCentralScalar
    (R : AssociatedProjectiveRepresentation T V P)
    (b : projectiveComparisonCentralizer T e) : ℂˣ :=
  Classical.choose
    (R.operator_centralizer_isScalar (e b) b.property)

omit [Finite B] in
/-- The selected left scalar affords the left projective operator. -/
theorem operator_leftComparisonCentralScalar
    (R : AssociatedProjectiveRepresentation T V P)
    (b : projectiveComparisonCentralizer T e) :
    P.operator (e b) =
      scalarLinearEquiv ℂ V
        (R.leftComparisonCentralScalar b) :=
  Classical.choose_spec
    (R.operator_centralizer_isScalar (e b) b.property)

/-- The scalar selected by Schur's lemma for the right projective operator.

The caller supplies the only required group-theoretic fact: every element in
the inverse image of the left centralizer also centralizes the right normal
subgroup. -/
def rightComparisonCentralScalar
    (S : AssociatedProjectiveRepresentation U W Q)
    (centralizer_preimage_le :
      projectiveComparisonCentralizer T e ≤
        Subgroup.centralizer
          (U.normalSubgroup : Set B))
    (b : projectiveComparisonCentralizer T e) : ℂˣ :=
  Classical.choose
    (S.operator_centralizer_isScalar
      b (centralizer_preimage_le b.property))

/-- The selected right scalar affords the right projective operator. -/
theorem operator_rightComparisonCentralScalar
    (S : AssociatedProjectiveRepresentation U W Q)
    (centralizer_preimage_le :
      projectiveComparisonCentralizer T e ≤
        Subgroup.centralizer
          (U.normalSubgroup : Set B))
    (b : projectiveComparisonCentralizer T e) :
    Q.operator b =
      scalarLinearEquiv ℂ W
        (S.rightComparisonCentralScalar
          centralizer_preimage_le b) :=
  Classical.choose_spec
    (S.operator_centralizer_isScalar
      b (centralizer_preimage_le b.property))

omit [Finite B] in
/-- Projective multiplication gives the multiplication law for the selected
left centralizer scalars. -/
theorem leftComparisonCentralScalar_mul_factor
    (R : AssociatedProjectiveRepresentation T V P)
    (b c : projectiveComparisonCentralizer T e) :
    R.leftComparisonCentralScalar b *
        R.leftComparisonCentralScalar c =
      P.factor (e b) (e c) *
        R.leftComparisonCentralScalar (b * c) := by
  apply scalarLinearEquiv_injective ℂ V
  rw [scalarLinearEquiv_mul, scalarLinearEquiv_mul]
  rw [← R.operator_leftComparisonCentralScalar b,
    ← R.operator_leftComparisonCentralScalar c,
    ← R.operator_leftComparisonCentralScalar (b * c)]
  calc
    P.operator (e b) * P.operator (e c) =
        scalarLinearEquiv ℂ V
            (P.factor (e b) (e c)) *
          P.operator (e b * e c) :=
      P.map_mul (e b) (e c)
    _ =
        scalarLinearEquiv ℂ V
            (P.factor (e b) (e c)) *
          P.operator (e ((b * c : projectiveComparisonCentralizer T e) : B)) := by
      rw [Subgroup.coe_mul, map_mul]

/-- Projective multiplication gives the multiplication law for the selected
right centralizer scalars. -/
theorem rightComparisonCentralScalar_mul_factor
    (S : AssociatedProjectiveRepresentation U W Q)
    (centralizer_preimage_le :
      projectiveComparisonCentralizer T e ≤
        Subgroup.centralizer
          (U.normalSubgroup : Set B))
    (b c : projectiveComparisonCentralizer T e) :
    S.rightComparisonCentralScalar centralizer_preimage_le b *
        S.rightComparisonCentralScalar centralizer_preimage_le c =
      Q.factor b c *
        S.rightComparisonCentralScalar
          centralizer_preimage_le (b * c) := by
  apply scalarLinearEquiv_injective ℂ W
  rw [scalarLinearEquiv_mul, scalarLinearEquiv_mul]
  rw [← S.operator_rightComparisonCentralScalar
      centralizer_preimage_le b,
    ← S.operator_rightComparisonCentralScalar
      centralizer_preimage_le c,
    ← S.operator_rightComparisonCentralScalar
      centralizer_preimage_le (b * c)]
  exact Q.map_mul b c

/-- The scalar quotient between two associated projective lifts on the
matched centralizer.

When the two factor sets agree, this function is multiplicative; see
`comparisonCentralScalarMismatch`. -/
def comparisonCentralScalarRatio
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (centralizer_preimage_le :
      projectiveComparisonCentralizer T e ≤
        Subgroup.centralizer
          (U.normalSubgroup : Set B))
    (b : projectiveComparisonCentralizer T e) : ℂˣ :=
  R.leftComparisonCentralScalar b /
    S.rightComparisonCentralScalar centralizer_preimage_le b

/-- Literal factor-set agreement makes the scalar ratio a genuine
multiplicative character of the matched centralizer. -/
def comparisonCentralScalarMismatch
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (centralizer_preimage_le :
      projectiveComparisonCentralizer T e ≤
        Subgroup.centralizer
          (U.normalSubgroup : Set B))
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c) :
    projectiveComparisonCentralizer T e →* ℂˣ :=
  MonoidHom.mk'
    (R.comparisonCentralScalarRatio
      S centralizer_preimage_le) (by
    intro b c
    have hleft :=
      R.leftComparisonCentralScalar_mul_factor
        (e := e) b c
    have hright :=
      S.rightComparisonCentralScalar_mul_factor
        centralizer_preimage_le b c
    rw [factorAgreement] at hleft
    unfold comparisonCentralScalarRatio
    calc
      R.leftComparisonCentralScalar (b * c) /
            S.rightComparisonCentralScalar
              centralizer_preimage_le (b * c) =
          (Q.factor (b : B) (c : B) *
              R.leftComparisonCentralScalar (b * c)) /
            (Q.factor (b : B) (c : B) *
              S.rightComparisonCentralScalar
                centralizer_preimage_le (b * c)) := by
        symm
        simp only [div_eq_mul_inv, mul_inv_rev]
        calc
          (Q.factor (b : B) (c : B) *
                R.leftComparisonCentralScalar (b * c)) *
              ((S.rightComparisonCentralScalar
                    centralizer_preimage_le (b * c))⁻¹ *
                (Q.factor (b : B) (c : B))⁻¹) =
            (Q.factor (b : B) (c : B) *
                (Q.factor (b : B) (c : B))⁻¹) *
              (R.leftComparisonCentralScalar (b * c) *
                (S.rightComparisonCentralScalar
                  centralizer_preimage_le (b * c))⁻¹) := by
            ac_rfl
          _ =
              R.leftComparisonCentralScalar (b * c) *
                (S.rightComparisonCentralScalar
                  centralizer_preimage_le (b * c))⁻¹ := by
            simp
      _ =
          (R.leftComparisonCentralScalar b *
              R.leftComparisonCentralScalar c) /
            (S.rightComparisonCentralScalar
                centralizer_preimage_le b *
              S.rightComparisonCentralScalar
                centralizer_preimage_le c) := by
        rw [hleft, hright]
      _ =
          R.leftComparisonCentralScalar b /
              S.rightComparisonCentralScalar
                centralizer_preimage_le b *
            (R.leftComparisonCentralScalar c /
              S.rightComparisonCentralScalar
                centralizer_preimage_le c) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ac_rfl)

@[simp]
theorem comparisonCentralScalarMismatch_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (centralizer_preimage_le :
      projectiveComparisonCentralizer T e ≤
        Subgroup.centralizer
          (U.normalSubgroup : Set B))
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c)
    (b : projectiveComparisonCentralizer T e) :
    R.comparisonCentralScalarMismatch
        S centralizer_preimage_le factorAgreement b =
      R.leftComparisonCentralScalar b /
        S.rightComparisonCentralScalar
          centralizer_preimage_le b :=
  rfl

/-- Scalar agreement is exactly triviality of the scalar mismatch
character. -/
theorem scalarAgreement_iff_comparisonCentralScalarMismatch_eq_one
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (centralizer_preimage_le :
      projectiveComparisonCentralizer T e ≤
        Subgroup.centralizer
          (U.normalSubgroup : Set B))
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c) :
    (∀ b : B,
        e b ∈
            Subgroup.centralizer
              (T.normalSubgroup : Set A) →
          ∃ c : ℂˣ,
            P.operator (e b) =
                scalarLinearEquiv ℂ V c ∧
              Q.operator b =
                scalarLinearEquiv ℂ W c) ↔
      R.comparisonCentralScalarMismatch
          S centralizer_preimage_le factorAgreement = 1 := by
  constructor
  · intro hagreement
    ext b
    obtain ⟨c, hcLeft, hcRight⟩ :=
      hagreement b b.property
    have hleft :
        R.leftComparisonCentralScalar b = c := by
      apply scalarLinearEquiv_injective ℂ V
      rw [← R.operator_leftComparisonCentralScalar b,
        hcLeft]
    have hright :
        S.rightComparisonCentralScalar
            centralizer_preimage_le b = c := by
      apply scalarLinearEquiv_injective ℂ W
      rw [← S.operator_rightComparisonCentralScalar
          centralizer_preimage_le b,
        hcRight]
    simp [hleft, hright]
  · intro hmismatch b hb
    let b' : projectiveComparisonCentralizer T e :=
      ⟨b, hb⟩
    have hratio :
        R.leftComparisonCentralScalar b' /
            S.rightComparisonCentralScalar
              centralizer_preimage_le b' =
          1 := by
      have :=
        DFunLike.congr_fun hmismatch b'
      simpa using this
    have hscalar :
        R.leftComparisonCentralScalar b' =
          S.rightComparisonCentralScalar
            centralizer_preimage_le b' := by
      exact (div_eq_one.mp hratio)
    refine
      ⟨R.leftComparisonCentralScalar b',
        R.operator_leftComparisonCentralScalar b',
        ?_⟩
    rw [S.operator_rightComparisonCentralScalar
      centralizer_preimage_le b', ← hscalar]

end AssociatedProjectiveRepresentation

end CharacterTriple
end McKayConjecture
