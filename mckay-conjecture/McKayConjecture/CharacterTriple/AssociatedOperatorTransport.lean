/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RepresentationTheory.FinGroupCharZero
import McKayConjecture.CharacterTriple.AssociatedUniqueness
import McKayConjecture.CharacterTriple.ProjectiveLinearGroup

/-!
# Transport of associated projective representations along operator equivalences

An exact intertwining equivalence between two projective representations
transports associatedness.  This is useful after a scalar gauge has made a
projective comparison exact: all six fields of associatedness then follow
from one operator identity.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

variable {A : Type} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
variable {Q : ProjectiveRepresentation ℂ A W}

/-- Conjugate a linear automorphism across a linear equivalence. -/
def conjugateOperator
    (E : V ≃ₗ[ℂ] W) (f : V ≃ₗ[ℂ] V) :
    W ≃ₗ[ℂ] W :=
  (E.symm.trans f).trans E

omit [Module.Finite ℂ V] [Nontrivial V]
  [Module.Finite ℂ W] [Nontrivial W] in
@[simp]
theorem conjugateOperator_apply
    (E : V ≃ₗ[ℂ] W) (f : V ≃ₗ[ℂ] V) (w : W) :
    conjugateOperator E f w = E (f (E.symm w)) :=
  rfl

/-- Exact conjugacy of projective operators transports associatedness.

The restriction on the source space is defined by the source projective
operators themselves.  Its representation law and its character are
transported through the supplied linear equivalence.
-/
def transportOfOperatorEquiv
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : V ≃ₗ[ℂ] W)
    (hoperator : ∀ (a : A) (v : V),
      E (P.operator a v) = Q.operator a (E v)) :
    AssociatedProjectiveRepresentation T V P := by
  let D : T.normalSubgroup →* (V ≃ₗ[ℂ] V) :=
    { toFun := fun x ↦ P.operator (x : A)
      map_one' := by
        ext v
        apply E.injective
        change E (P.operator (1 : A) v) = E v
        rw [hoperator]
        change Q.operator ((1 : T.normalSubgroup) : A) (E v) = E v
        rw [← S.restriction_apply]
        simp
      map_mul' := by
        intro x y
        ext v
        apply E.injective
        change
          E (P.operator (((x * y : T.normalSubgroup) : A)) v) =
            E (P.operator (x : A) (P.operator (y : A) v))
        calc
          E (P.operator (((x * y : T.normalSubgroup) : A)) v) =
              Q.operator (((x * y : T.normalSubgroup) : A)) (E v) :=
            hoperator _ _
          _ = S.restriction (x * y) (E v) := by
            rw [S.restriction_apply]
          _ = S.restriction x (S.restriction y (E v)) := by
            rw [map_mul]
            rfl
          _ = Q.operator (x : A) (Q.operator (y : A) (E v)) := by
            rw [S.restriction_apply, S.restriction_apply]
          _ = E (P.operator (x : A) (P.operator (y : A) v)) := by
            rw [hoperator, hoperator] }
  have hcharacter :
      (FDRep.of (linearRepresentationOfAction D)).character =
        T.character.values := by
    funext x
    change LinearMap.trace ℂ V (P.operator (x : A)) =
      T.character.values x
    have hconj :
        E.conj (P.operator (x : A) : V →ₗ[ℂ] V) =
          (Q.operator (x : A) : W →ₗ[ℂ] W) := by
      apply LinearMap.ext
      intro w
      change
        E (P.operator (x : A) (E.symm w)) =
          Q.operator (x : A) w
      rw [hoperator]
      simp
    calc
      LinearMap.trace ℂ V (P.operator (x : A)) =
          LinearMap.trace ℂ W
            (E.conj (P.operator (x : A) : V →ₗ[ℂ] V)) :=
        (LinearMap.trace_conj' _ E).symm
      _ = LinearMap.trace ℂ W (Q.operator (x : A)) := by
        rw [hconj]
      _ = T.character.values x := by
        rw [← S.restriction_apply]
        exact congrFun S.restriction_character x
  refine
    { restriction := D
      restriction_apply := fun _ ↦ rfl
      restriction_simple := ?_
      restriction_character := hcharacter
      normal_mul := ?_
      mul_normal := ?_ }
  · letI : Fintype T.normalSubgroup :=
      Fintype.ofFinite T.normalSubgroup
    rw [FDRep.simple_iff_char_is_norm_one]
    have hsimple : Simple T.character.realization :=
      inferInstance
    have hnorm :=
      (FDRep.simple_iff_char_is_norm_one
        T.character.realization).mp hsimple
    rw [hcharacter, ← T.character.realization_character]
    exact hnorm
  · intro x a
    ext v
    apply E.injective
    change
      E (P.operator ((x : A) * a) v) =
        E (P.operator (x : A) (P.operator a v))
    calc
      E (P.operator ((x : A) * a) v) =
          Q.operator ((x : A) * a) (E v) := hoperator _ _
      _ = Q.operator (x : A) (Q.operator a (E v)) := by
        rw [S.normal_mul]
        rfl
      _ = E (P.operator (x : A) (P.operator a v)) := by
        rw [hoperator, hoperator]
  · intro a x
    ext v
    apply E.injective
    change
      E (P.operator (a * (x : A)) v) =
        E (P.operator a (P.operator (x : A) v))
    calc
      E (P.operator (a * (x : A)) v) =
          Q.operator (a * (x : A)) (E v) := hoperator _ _
      _ = Q.operator a (Q.operator (x : A) (E v)) := by
        rw [S.mul_normal]
        rfl
      _ = E (P.operator a (P.operator (x : A) v)) := by
        rw [hoperator, hoperator]

omit [Finite A] [Module.Finite ℂ V] [Nontrivial V]
  [Module.Finite ℂ W] [Nontrivial W] in
/-- Projective conjugacy supplies a scalar gauge which makes the operator
conjugacy exact. -/
theorem exists_gauge_operatorEquiv
    (E : V ≃ₗ[ℂ] W)
    (hprojective : ∀ a : A,
      ProjectiveLinearGroup.mk ℂ W
          (conjugateOperator E (P.operator a)) =
        Q.toProjectiveLinearGroup a) :
    ∃ gauge : A → ℂˣ,
      ∀ (a : A) (v : V),
        E ((P.rescale gauge).operator a v) =
          Q.operator a (E v) := by
  have hexists : ∀ a : A, ∃ c : ℂˣ,
      conjugateOperator E (P.operator a) *
          scalarLinearEquiv ℂ W c =
        Q.operator a := by
    intro a
    have hquotient :
        ProjectiveLinearGroup.mk ℂ W
            (conjugateOperator E (P.operator a)) =
          ProjectiveLinearGroup.mk ℂ W (Q.operator a) :=
      hprojective a
    obtain ⟨z, hz, hzEq⟩ :=
      (QuotientGroup.mk'_eq_mk'
        (ScalarLinearEquivSubgroup ℂ W)).mp hquotient
    obtain ⟨c, rfl⟩ := hz
    exact ⟨c, hzEq⟩
  let gauge : A → ℂˣ :=
    fun a ↦ Classical.choose (hexists a)
  have hgauge :
      ∀ a : A,
        conjugateOperator E (P.operator a) *
            scalarLinearEquiv ℂ W (gauge a) =
          Q.operator a :=
    fun a ↦ Classical.choose_spec (hexists a)
  have hoperator :
      ∀ (a : A) (v : V),
        E ((P.rescale gauge).operator a v) =
          Q.operator a (E v) := by
    intro a v
    have hconjugate :
        scalarLinearEquiv ℂ W (gauge a) *
            conjugateOperator E (P.operator a) =
          Q.operator a := by
      rw [scalarLinearEquiv_comm]
      exact hgauge a
    have happly :=
      DFunLike.congr_fun hconjugate (E v)
    rw [ProjectiveRepresentation.rescale_operator]
    change
      E ((gauge a : ℂ) • P.operator a v) =
        Q.operator a (E v)
    rw [E.map_smul]
    simpa only [LinearEquiv.mul_apply, scalarLinearEquiv_apply,
      conjugateOperator_apply, E.symm_apply_apply] using happly
  exact ⟨gauge, hoperator⟩

/-- Projective conjugacy to an associated lift supplies a scalar gauge
which makes the conjugacy exact and transports associatedness.

This is the projective-linear form of `transportOfOperatorEquiv`: it reduces
an association proof to equality in the projective linear group and chooses
the required pointwise scalars from that equality.
-/
theorem exists_gauge_transportOfProjectiveEquiv
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : V ≃ₗ[ℂ] W)
    (hprojective : ∀ a : A,
      ProjectiveLinearGroup.mk ℂ W
          (conjugateOperator E (P.operator a)) =
        Q.toProjectiveLinearGroup a) :
    ∃ gauge : A → ℂˣ,
      (∀ (a : A) (v : V),
        E ((P.rescale gauge).operator a v) =
          Q.operator a (E v)) ∧
      Nonempty
        (AssociatedProjectiveRepresentation
          T V (P.rescale gauge)) := by
  obtain ⟨gauge, hoperator⟩ :=
    exists_gauge_operatorEquiv E hprojective
  exact
    ⟨gauge, hoperator,
      ⟨transportOfOperatorEquiv S E hoperator⟩⟩

/-- Trivial projective factors on both sides of the normal subgroup,
together with the correct normal trace, are sufficient for associatedness.

This criterion is convenient when normal multiplication is inherited from
factor agreement with another associated lift.
-/
def ofFactorNormalAndTrace
    (hleft : ∀ (x : T.normalSubgroup) (a : A),
      P.factor (x : A) a = 1)
    (hright : ∀ (a : A) (x : T.normalSubgroup),
      P.factor a (x : A) = 1)
    (htrace : ∀ x : T.normalSubgroup,
      LinearMap.trace ℂ V (P.operator (x : A)) =
        T.character.values x) :
    AssociatedProjectiveRepresentation T V P := by
  let D : T.normalSubgroup →* (V ≃ₗ[ℂ] V) :=
    { toFun := fun x ↦ P.operator (x : A)
      map_one' := by
        have h :=
          P.operator_one_eq_scalar_left
            ((1 : T.normalSubgroup) : A)
        rw [hright 1 (1 : T.normalSubgroup)] at h
        simpa using h
      map_mul' := by
        intro x y
        have h := P.map_mul (x : A) (y : A)
        rw [hleft x (y : A), map_one, one_mul] at h
        exact h.symm }
  have hcharacter :
      (FDRep.of (linearRepresentationOfAction D)).character =
        T.character.values := by
    funext x
    exact htrace x
  refine
    { restriction := D
      restriction_apply := fun _ ↦ rfl
      restriction_simple := ?_
      restriction_character := hcharacter
      normal_mul := ?_
      mul_normal := ?_ }
  · letI : Fintype T.normalSubgroup :=
      Fintype.ofFinite T.normalSubgroup
    rw [FDRep.simple_iff_char_is_norm_one]
    have hsimple : Simple T.character.realization :=
      inferInstance
    have hnorm :=
      (FDRep.simple_iff_char_is_norm_one
        T.character.realization).mp hsimple
    rw [hcharacter, ← T.character.realization_character]
    exact hnorm
  · intro x a
    have h := P.map_mul (x : A) a
    rw [hleft x a, map_one, one_mul] at h
    exact h.symm
  · intro a x
    have h := P.map_mul a (x : A)
    rw [hright a x, map_one, one_mul] at h
    exact h.symm

end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
