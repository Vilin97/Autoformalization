/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralProjectiveScalarMismatch
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Conjugation invariance of the projective scalar mismatch

The inverse image of the centralizer of the left normal subgroup is normal
in the right ambient group.  When the two projective factor sets agree
literally, conjugating an element of this subgroup changes the two selected
central scalars by the same factor-set correction.  Their quotient, the
comparison scalar mismatch, is therefore invariant under the whole right
ambient group.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple

universe u v

open scoped commutatorElement

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

/-- The comparison centralizer is normal in the right ambient group. -/
instance projectiveComparisonCentralizer_normal :
    (projectiveComparisonCentralizer T e).Normal := by
  dsimp [projectiveComparisonCentralizer]
  infer_instance

namespace AssociatedProjectiveRepresentation

omit [Finite B] in
/-- Conjugating a left comparison scalar changes it by the factor-set
correction forced by projective multiplication. -/
theorem leftComparisonCentralScalar_conjNormal
    (R : AssociatedProjectiveRepresentation T V P)
    (b : B) (k : projectiveComparisonCentralizer T e) :
    R.leftComparisonCentralScalar
        (MulAut.conjNormal b k) =
      P.factor (e (MulAut.conjNormal b k : B)) (e b) /
          P.factor (e b) (e k) *
        R.leftComparisonCentralScalar k := by
  have hconj :
      (MulAut.conjNormal b k : B) * b =
        b * (k : B) := by
    simp only [MulAut.conjNormal_apply]
    group
  have heconj :
      e (MulAut.conjNormal b k : B) * e b =
        e b * e k := by
    simpa only [map_mul] using congrArg e hconj
  apply scalarLinearEquiv_injective ℂ V
  rw [scalarLinearEquiv_mul]
  apply mul_right_cancel
  calc
    scalarLinearEquiv ℂ V
          (R.leftComparisonCentralScalar
            (MulAut.conjNormal b k)) *
        P.operator (e b) =
      P.operator (e (MulAut.conjNormal b k : B)) *
        P.operator (e b) := by
          rw [R.operator_leftComparisonCentralScalar]
    _ =
      scalarLinearEquiv ℂ V
          (P.factor
            (e (MulAut.conjNormal b k : B)) (e b)) *
        P.operator
          (e (MulAut.conjNormal b k : B) * e b) :=
      P.map_mul _ _
    _ =
      scalarLinearEquiv ℂ V
          (P.factor
            (e (MulAut.conjNormal b k : B)) (e b)) *
        P.operator (e b * e k) := by
          rw [heconj]
    _ =
      scalarLinearEquiv ℂ V
          (P.factor
              (e (MulAut.conjNormal b k : B)) (e b) /
            P.factor (e b) (e k)) *
        (scalarLinearEquiv ℂ V
            (P.factor (e b) (e k)) *
          P.operator (e b * e k)) := by
          rw [← mul_assoc, ← scalarLinearEquiv_mul]
          congr 2
          simp
    _ =
      scalarLinearEquiv ℂ V
          (P.factor
              (e (MulAut.conjNormal b k : B)) (e b) /
            P.factor (e b) (e k)) *
        (P.operator (e b) * P.operator (e k)) := by
          rw [P.map_mul]
    _ =
      scalarLinearEquiv ℂ V
          (P.factor
              (e (MulAut.conjNormal b k : B)) (e b) /
            P.factor (e b) (e k)) *
        (P.operator (e b) *
          scalarLinearEquiv ℂ V
            (R.leftComparisonCentralScalar k)) := by
          rw [R.operator_leftComparisonCentralScalar]
    _ =
      (scalarLinearEquiv ℂ V
          (P.factor
              (e (MulAut.conjNormal b k : B)) (e b) /
            P.factor (e b) (e k)) *
        scalarLinearEquiv ℂ V
          (R.leftComparisonCentralScalar k)) *
        P.operator (e b) := by
          rw [← scalarLinearEquiv_comm ℂ V
            (R.leftComparisonCentralScalar k)
            (P.operator (e b))]
          simp only [mul_assoc]

/-- Conjugating a right comparison scalar changes it by the factor-set
correction forced by projective multiplication. -/
theorem rightComparisonCentralScalar_conjNormal
    (S : AssociatedProjectiveRepresentation U W Q)
    (centralizer_preimage_le :
      projectiveComparisonCentralizer T e ≤
        Subgroup.centralizer
          (U.normalSubgroup : Set B))
    (b : B) (k : projectiveComparisonCentralizer T e) :
    S.rightComparisonCentralScalar centralizer_preimage_le
        (MulAut.conjNormal b k) =
      Q.factor (MulAut.conjNormal b k : B) b /
          Q.factor b k *
        S.rightComparisonCentralScalar
          centralizer_preimage_le k := by
  have hconj :
      (MulAut.conjNormal b k : B) * b =
        b * (k : B) := by
    simp only [MulAut.conjNormal_apply]
    group
  apply scalarLinearEquiv_injective ℂ W
  rw [scalarLinearEquiv_mul]
  apply mul_right_cancel
  calc
    scalarLinearEquiv ℂ W
          (S.rightComparisonCentralScalar
            centralizer_preimage_le
            (MulAut.conjNormal b k)) *
        Q.operator b =
      Q.operator (MulAut.conjNormal b k : B) *
        Q.operator b := by
          rw [S.operator_rightComparisonCentralScalar]
    _ =
      scalarLinearEquiv ℂ W
          (Q.factor (MulAut.conjNormal b k : B) b) *
        Q.operator
          ((MulAut.conjNormal b k : B) * b) :=
      Q.map_mul _ _
    _ =
      scalarLinearEquiv ℂ W
          (Q.factor (MulAut.conjNormal b k : B) b) *
        Q.operator (b * (k : B)) := by
          rw [hconj]
    _ =
      scalarLinearEquiv ℂ W
          (Q.factor (MulAut.conjNormal b k : B) b /
            Q.factor b k) *
        (scalarLinearEquiv ℂ W (Q.factor b k) *
          Q.operator (b * (k : B))) := by
          rw [← mul_assoc, ← scalarLinearEquiv_mul]
          congr 2
          simp
    _ =
      scalarLinearEquiv ℂ W
          (Q.factor (MulAut.conjNormal b k : B) b /
            Q.factor b k) *
        (Q.operator b * Q.operator k) := by
          rw [Q.map_mul]
    _ =
      scalarLinearEquiv ℂ W
          (Q.factor (MulAut.conjNormal b k : B) b /
            Q.factor b k) *
        (Q.operator b *
          scalarLinearEquiv ℂ W
            (S.rightComparisonCentralScalar
              centralizer_preimage_le k)) := by
          rw [S.operator_rightComparisonCentralScalar]
    _ =
      (scalarLinearEquiv ℂ W
          (Q.factor (MulAut.conjNormal b k : B) b /
            Q.factor b k) *
        scalarLinearEquiv ℂ W
          (S.rightComparisonCentralScalar
            centralizer_preimage_le k)) *
        Q.operator b := by
          rw [← scalarLinearEquiv_comm ℂ W
            (S.rightComparisonCentralScalar
              centralizer_preimage_le k)
            (Q.operator b)]
          simp only [mul_assoc]

/-- Literal factor-set agreement makes the comparison central scalar
mismatch invariant under conjugation by every element of the right ambient
group. -/
theorem comparisonCentralScalarMismatch_conjNormal
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
    (b : B) (k : projectiveComparisonCentralizer T e) :
    R.comparisonCentralScalarMismatch
        S centralizer_preimage_le factorAgreement
        (MulAut.conjNormal b k) =
      R.comparisonCentralScalarMismatch
        S centralizer_preimage_le factorAgreement k := by
  rw [comparisonCentralScalarMismatch_apply,
    comparisonCentralScalarMismatch_apply,
    R.leftComparisonCentralScalar_conjNormal,
    S.rightComparisonCentralScalar_conjNormal]
  rw [factorAgreement, factorAgreement]
  exact mul_div_mul_left_eq_div _ _ _

/-- Homomorphism-level form of ambient conjugation invariance. -/
theorem comparisonCentralScalarMismatch_comp_conjNormal
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
    (b : B) :
    (R.comparisonCentralScalarMismatch
        S centralizer_preimage_le factorAgreement).comp
        (MulAut.conjNormal b).toMonoidHom =
      R.comparisonCentralScalarMismatch
        S centralizer_preimage_le factorAgreement := by
  apply MonoidHom.ext
  intro k
  exact
    R.comparisonCentralScalarMismatch_conjNormal
      S centralizer_preimage_le factorAgreement b k

/-- The ambient commutator of the comparison centralizer with the right
ambient group is killed by the scalar mismatch character.

The kernel is mapped back to `B` along the subgroup inclusion, so the
statement directly expresses
`[projectiveComparisonCentralizer T e, B] ≤ ker(mismatch)`. -/
theorem projectiveComparisonCentralizer_commutator_le_scalarMismatchKernel
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
    ⁅projectiveComparisonCentralizer T e, (⊤ : Subgroup B)⁆ ≤
      (R.comparisonCentralScalarMismatch
          S centralizer_preimage_le factorAgreement).ker.map
        (projectiveComparisonCentralizer T e).subtype := by
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_le.mpr
  intro b _ k hk
  let k' : projectiveComparisonCentralizer T e := ⟨k, hk⟩
  let c : projectiveComparisonCentralizer T e :=
    MulAut.conjNormal b k' * k'⁻¹
  have hc :
      (c : B) = ⁅b, k⁆ := by
    simp [c, k', commutatorElement_def]
  refine ⟨c, ?_, hc⟩
  apply MonoidHom.mem_ker.mpr
  let m :=
    R.comparisonCentralScalarMismatch
      S centralizer_preimage_le factorAgreement
  change m c = 1
  calc
    m c =
        m (MulAut.conjNormal b k') *
          m k'⁻¹ := by
            exact m.map_mul _ _
    _ =
        m (MulAut.conjNormal b k') *
          (m k')⁻¹ := by
            rw [map_inv]
    _ = m k' * (m k')⁻¹ := by
          rw [R.comparisonCentralScalarMismatch_conjNormal
            S centralizer_preimage_le factorAgreement]
    _ = 1 := by simp

end AssociatedProjectiveRepresentation

end CharacterTriple
end McKayConjecture
