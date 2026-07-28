/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveQuotientDescent

/-!
# Transporting projective quotient compatibility

Strict conjugacy of projective operators transports both their factor
sets and exact quotient compatibility.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K G V W : Type}
variable [Field K] [Group G]
variable [AddCommGroup V] [Module K V] [Nontrivial V]
variable [AddCommGroup W] [Module K W]

/-- Strictly conjugate projective operator systems have equal scalar
factors. -/
theorem factor_eq_of_linearEquiv_operator_eq
    (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W)
    (E : V ≃ₗ[K] W)
    (hoperator :
      ∀ (g : G) (v : V),
        E (P.operator g v) =
          Q.operator g (E v))
    (g h : G) :
    P.factor g h = Q.factor g h := by
  obtain ⟨v : V, hv⟩ := exists_ne (0 : V)
  have hw :
      Q.operator (g * h) (E v) ≠ 0 := by
    intro hzero
    apply hv
    apply E.injective
    apply (Q.operator (g * h)).injective
    simpa using hzero
  apply Units.ext
  apply smul_left_injective K hw
  calc
    (P.factor g h : K) • Q.operator (g * h) (E v) =
        E ((P.factor g h : K) •
          P.operator (g * h) v) := by
      rw [map_smul, hoperator]
    _ = E (P.operator g (P.operator h v)) := by
      congr 1
      exact
        (DFunLike.congr_fun (P.map_mul g h) v).symm
    _ = Q.operator g (E (P.operator h v)) :=
      hoperator g (P.operator h v)
    _ = Q.operator g (Q.operator h (E v)) := by
      rw [hoperator h v]
    _ = (Q.factor g h : K) •
        Q.operator (g * h) (E v) :=
      DFunLike.congr_fun (Q.map_mul g h) (E v)

/-- Exact quotient compatibility transfers across a strict linear
conjugacy of projective operator systems. -/
theorem IsQuotientCompatible.of_linearEquiv_operator_eq
    (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W)
    (N : Subgroup G)
    (hQ : Q.IsQuotientCompatible N)
    (E : V ≃ₗ[K] W)
    (hoperator :
      ∀ (g : G) (v : V),
        E (P.operator g v) =
          Q.operator g (E v)) :
    P.IsQuotientCompatible N where
  factor_normal_left n g := by
    rw [factor_eq_of_linearEquiv_operator_eq
      P Q E hoperator (n : G) g]
    exact hQ.factor_normal_left n g
  factor_normal_right g n := by
    rw [factor_eq_of_linearEquiv_operator_eq
      P Q E hoperator g (n : G)]
    exact hQ.factor_normal_right g n
  operator_normal n := by
    apply LinearEquiv.ext
    intro v
    apply E.injective
    rw [hoperator, hQ.operator_normal]
    simp

variable {N : Subgroup G} [N.Normal]

/-- A strict operator intertwiner descends unchanged to the two quotient
projective representations. -/
theorem quotientDescent_intertwines
    (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W)
    (hP : P.IsQuotientCompatible N)
    (hQ : Q.IsQuotientCompatible N)
    (E : V ≃ₗ[K] W)
    (hoperator :
      ∀ (g : G) (v : V),
        E (P.operator g v) =
          Q.operator g (E v))
    (u : G ⧸ N) (v : V) :
    E ((P.quotientDescent N hP).operator u v) =
      (Q.quotientDescent N hQ).operator u (E v) := by
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective N u
  rw [P.quotientDescent_operator_mk hP,
    Q.quotientDescent_operator_mk hQ]
  exact hoperator g v

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
