/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveRepresentation
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The projective linear group of a module

A projective representation is an honest homomorphism after quotienting the
linear automorphism group by scalar automorphisms.  This file constructs that
homomorphism without choosing a basis, and proves its descent through a group
quotient whenever the chosen lifts are trivial on the normal subgroup.

The basis-free quotient is useful for character-triple multiplicity spaces:
their lifts may only be projective, while their classes in the projective
linear group form a genuine quotient action.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple

variable (K : Type u) (V : Type v)
  [Field K] [AddCommGroup V] [Module K V]

/-- The subgroup of scalar linear automorphisms. -/
abbrev ScalarLinearEquivSubgroup : Subgroup (V ≃ₗ[K] V) :=
  MonoidHom.range (scalarLinearEquiv K V)

instance scalarLinearEquivSubgroup_normal :
    (ScalarLinearEquivSubgroup K V).Normal where
  conj_mem := by
    intro f hf g
    obtain ⟨c, rfl⟩ := hf
    refine ⟨c, ?_⟩
    symm
    calc
      g * scalarLinearEquiv K V c * g⁻¹ =
          scalarLinearEquiv K V c * g * g⁻¹ := by
            rw [(scalarLinearEquiv_comm K V c g).symm]
      _ = scalarLinearEquiv K V c := by simp

/-- The basis-free projective linear group of `V`. -/
abbrev ProjectiveLinearGroup :=
  (V ≃ₗ[K] V) ⧸ ScalarLinearEquivSubgroup K V

namespace ProjectiveLinearGroup

/-- The quotient map from linear automorphisms to their projective classes. -/
abbrev mk :
    (V ≃ₗ[K] V) →* ProjectiveLinearGroup K V :=
  QuotientGroup.mk' (ScalarLinearEquivSubgroup K V)

@[simp]
theorem mk_scalar (c : Kˣ) :
    mk K V (scalarLinearEquiv K V c) = 1 := by
  change
    ((scalarLinearEquiv K V c :
      V ≃ₗ[K] V) : ProjectiveLinearGroup K V) = 1
  rw [QuotientGroup.eq_one_iff]
  exact ⟨c, rfl⟩

theorem mk_eq_one_iff_isScalar (f : V ≃ₗ[K] V) :
    mk K V f = 1 ↔ ∃ c : Kˣ, f = scalarLinearEquiv K V c := by
  change
    ((f : V ≃ₗ[K] V) : ProjectiveLinearGroup K V) = 1 ↔
      ∃ c : Kˣ, f = scalarLinearEquiv K V c
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

end ProjectiveLinearGroup

namespace ProjectiveRepresentation

variable {K V} {G : Type w} [Group G]

/-- A projective representation defines a genuine homomorphism to the
projective linear group. -/
def toProjectiveLinearGroup
    (P : ProjectiveRepresentation K G V) :
    G →* ProjectiveLinearGroup K V where
  toFun g := ProjectiveLinearGroup.mk K V (P.operator g)
  map_one' := by
    rw [ProjectiveLinearGroup.mk_eq_one_iff_isScalar]
    exact ⟨P.factor 1 1, P.operator_one_eq_scalar_left 1⟩
  map_mul' g h := by
    rw [← (ProjectiveLinearGroup.mk K V).map_mul]
    apply (QuotientGroup.mk'_eq_mk'
      (ScalarLinearEquivSubgroup K V)).2
    refine ⟨scalarLinearEquiv K V (P.factor g h), ?_, ?_⟩
    · exact ⟨P.factor g h, rfl⟩
    · calc
        P.operator (g * h) *
            scalarLinearEquiv K V (P.factor g h) =
          scalarLinearEquiv K V (P.factor g h) *
            P.operator (g * h) :=
              (scalarLinearEquiv_comm K V
                (P.factor g h) (P.operator (g * h))).symm
        _ = P.operator g * P.operator h := (P.map_mul g h).symm

@[simp]
theorem toProjectiveLinearGroup_apply
    (P : ProjectiveRepresentation K G V) (g : G) :
    P.toProjectiveLinearGroup g =
      ProjectiveLinearGroup.mk K V (P.operator g) :=
  rfl

theorem toProjectiveLinearGroup_eq_one_iff
    (P : ProjectiveRepresentation K G V) (g : G) :
    P.toProjectiveLinearGroup g = 1 ↔
      ∃ c : Kˣ, P.operator g = scalarLinearEquiv K V c :=
  ProjectiveLinearGroup.mk_eq_one_iff_isScalar K V (P.operator g)

/-- If the chosen lifts are identity on a normal subgroup, the projective
linear action descends to the quotient group. -/
def quotientProjectiveLinearGroup
    (P : ProjectiveRepresentation K G V)
    (N : Subgroup G) [N.Normal]
    (htriv : ∀ n : N, P.operator (n : G) = 1) :
    G ⧸ N →* ProjectiveLinearGroup K V :=
  QuotientGroup.lift N P.toProjectiveLinearGroup (by
    intro g hg
    rw [MonoidHom.mem_ker, P.toProjectiveLinearGroup_eq_one_iff]
    refine ⟨1, ?_⟩
    rw [htriv ⟨g, hg⟩, map_one])

@[simp]
theorem quotientProjectiveLinearGroup_mk
    (P : ProjectiveRepresentation K G V)
    (N : Subgroup G) [N.Normal]
    (htriv : ∀ n : N, P.operator (n : G) = 1)
    (g : G) :
    P.quotientProjectiveLinearGroup N htriv
        (QuotientGroup.mk' N g) =
      P.toProjectiveLinearGroup g :=
  rfl

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
