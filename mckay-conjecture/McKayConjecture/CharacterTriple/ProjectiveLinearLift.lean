/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveLinearGroup

/-!
# Lifting projective-linear actions

A homomorphism from a group to the projective linear group can be lifted,
using a chosen representative of every projective class, to a projective
representation.  The scalar discrepancy between two chosen representatives
is exactly its factor set.

The construction is deliberately basis-free.  It is the inverse-direction
tool needed for central character-triple correspondences: a multiplicity
action may first be transported across an isomorphism of quotient groups and
then lifted back to the ambient group.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple

namespace ProjectiveLinearGroup

variable {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V]

/-- A chosen linear representative of a projective-linear class. -/
def representative (q : ProjectiveLinearGroup K V) :
    V ≃ₗ[K] V := by
  classical
  exact
    if q = 1 then 1
    else
      Classical.choose
        (QuotientGroup.mk'_surjective
          (ScalarLinearEquivSubgroup K V) q)

/-- The chosen representative maps back to its original projective class. -/
@[simp]
theorem mk_representative (q : ProjectiveLinearGroup K V) :
    mk K V (representative q) = q :=
  by
    classical
    by_cases hq : q = 1
    · simp [representative, hq]
    · simp only [representative, hq, ↓reduceIte]
      exact
        Classical.choose_spec
          (QuotientGroup.mk'_surjective
            (ScalarLinearEquivSubgroup K V) q)

/-- The chosen representative of the identity projective class is the
identity linear automorphism. -/
@[simp]
theorem representative_one :
    representative (1 : ProjectiveLinearGroup K V) = 1 := by
  simp [representative]

end ProjectiveLinearGroup

namespace ProjectiveRepresentation

variable {K : Type u} {V : Type v} {G : Type w}
  [Field K] [AddCommGroup V] [Module K V] [Group G]

/-- On a nonzero module, the chosen operators determine the scalar factor
of a projective representation uniquely. -/
theorem factor_eq_of_operator_eq [Nontrivial V]
    (P Q : ProjectiveRepresentation K G V)
    (hoperator : P.operator = Q.operator) :
    P.factor = Q.factor := by
  funext g h
  apply scalarLinearEquiv_injective K V
  apply mul_right_cancel (b := Q.operator (g * h))
  have hP := P.map_mul g h
  rw [hoperator] at hP
  exact hP.symm.trans (Q.map_mul g h)

/-- Consequently, two projective representations on a nonzero module are
equal once all their chosen lifts agree. -/
theorem ext_of_operator_eq [Nontrivial V]
    (P Q : ProjectiveRepresentation K G V)
    (hoperator : P.operator = Q.operator) :
    P = Q :=
  ProjectiveRepresentation.ext hoperator
    (factor_eq_of_operator_eq P Q hoperator)

/-- The chosen lift of a projective-linear group action. -/
def operatorOfProjectiveLinearGroup
    (ρ : G →* ProjectiveLinearGroup K V) (g : G) :
    V ≃ₗ[K] V :=
  ProjectiveLinearGroup.representative (ρ g)

@[simp]
theorem mk_operatorOfProjectiveLinearGroup
    (ρ : G →* ProjectiveLinearGroup K V) (g : G) :
    ProjectiveLinearGroup.mk K V
        (operatorOfProjectiveLinearGroup ρ g) =
      ρ g :=
  ProjectiveLinearGroup.mk_representative (ρ g)

/-- Two chosen lifts multiply up to a nonzero scalar. -/
theorem exists_factorOfProjectiveLinearGroup
    (ρ : G →* ProjectiveLinearGroup K V) (g h : G) :
    ∃ c : Kˣ,
      operatorOfProjectiveLinearGroup ρ g *
          operatorOfProjectiveLinearGroup ρ h =
        scalarLinearEquiv K V c *
          operatorOfProjectiveLinearGroup ρ (g * h) := by
  have hquot :
      ProjectiveLinearGroup.mk K V
          (operatorOfProjectiveLinearGroup ρ (g * h)) =
        ProjectiveLinearGroup.mk K V
          (operatorOfProjectiveLinearGroup ρ g *
            operatorOfProjectiveLinearGroup ρ h) := by
    calc
      ProjectiveLinearGroup.mk K V
          (operatorOfProjectiveLinearGroup ρ (g * h)) =
          ρ (g * h) :=
        mk_operatorOfProjectiveLinearGroup ρ (g * h)
      _ = ρ g * ρ h := ρ.map_mul g h
      _ =
          ProjectiveLinearGroup.mk K V
              (operatorOfProjectiveLinearGroup ρ g) *
            ProjectiveLinearGroup.mk K V
              (operatorOfProjectiveLinearGroup ρ h) := by
        rw [mk_operatorOfProjectiveLinearGroup,
          mk_operatorOfProjectiveLinearGroup]
      _ =
          ProjectiveLinearGroup.mk K V
            (operatorOfProjectiveLinearGroup ρ g *
              operatorOfProjectiveLinearGroup ρ h) :=
        ((ProjectiveLinearGroup.mk K V).map_mul
          (operatorOfProjectiveLinearGroup ρ g)
          (operatorOfProjectiveLinearGroup ρ h)).symm
  obtain ⟨z, hz, hzEq⟩ :=
    (QuotientGroup.mk'_eq_mk'
      (N := ScalarLinearEquivSubgroup K V)).mp hquot
  obtain ⟨c, rfl⟩ := hz
  refine ⟨c, ?_⟩
  rw [← hzEq]
  exact
    (scalarLinearEquiv_comm K V c
      (operatorOfProjectiveLinearGroup ρ (g * h))).symm

/-- The scalar factor selected for the chosen lifts. -/
def factorOfProjectiveLinearGroup
    (ρ : G →* ProjectiveLinearGroup K V) (g h : G) : Kˣ :=
  Classical.choose (exists_factorOfProjectiveLinearGroup ρ g h)

/-- The selected scalar satisfies the projective multiplication law. -/
theorem operatorOfProjectiveLinearGroup_map_mul
    (ρ : G →* ProjectiveLinearGroup K V) (g h : G) :
    operatorOfProjectiveLinearGroup ρ g *
        operatorOfProjectiveLinearGroup ρ h =
      scalarLinearEquiv K V
          (factorOfProjectiveLinearGroup ρ g h) *
        operatorOfProjectiveLinearGroup ρ (g * h) :=
  Classical.choose_spec
    (exists_factorOfProjectiveLinearGroup ρ g h)

/-- Lift a homomorphism to the projective linear group to a projective
representation with chosen linear representatives. -/
def ofProjectiveLinearGroup
    (ρ : G →* ProjectiveLinearGroup K V) :
    ProjectiveRepresentation K G V where
  operator := operatorOfProjectiveLinearGroup ρ
  factor := factorOfProjectiveLinearGroup ρ
  map_mul := operatorOfProjectiveLinearGroup_map_mul ρ

@[simp]
theorem ofProjectiveLinearGroup_operator
    (ρ : G →* ProjectiveLinearGroup K V) (g : G) :
    (ofProjectiveLinearGroup ρ).operator g =
      operatorOfProjectiveLinearGroup ρ g :=
  rfl

@[simp]
theorem ofProjectiveLinearGroup_operator_one
    (ρ : G →* ProjectiveLinearGroup K V) :
    (ofProjectiveLinearGroup ρ).operator 1 = 1 := by
  rw [ofProjectiveLinearGroup_operator,
    operatorOfProjectiveLinearGroup, map_one]
  exact ProjectiveLinearGroup.representative_one

@[simp]
theorem ofProjectiveLinearGroup_toProjectiveLinearGroup
    (ρ : G →* ProjectiveLinearGroup K V) :
    (ofProjectiveLinearGroup ρ).toProjectiveLinearGroup = ρ := by
  ext g
  exact mk_operatorOfProjectiveLinearGroup ρ g

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
