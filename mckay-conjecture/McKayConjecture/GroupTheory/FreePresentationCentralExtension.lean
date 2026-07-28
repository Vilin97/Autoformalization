/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.FreeGroup.Basic
import McKayConjecture.GroupTheory.PerfectCentralExtensionCenter

/-!
# The central extension attached to a free presentation

For a group `S`, let `F` be the free group on its underlying type, let
`R` be the kernel of the evaluation map `F → S`, and let `D = [F,F]`.
This file constructs the classical central extension

`D / [F,R] → S`.

When `S` is perfect, the projection is surjective.
-/

noncomputable section

open scoped commutatorElement

universe u

namespace McKayConjecture
namespace GroupTheory
namespace FreePresentation

variable (S : Type u) [Group S]

/-- The free group used in the canonical presentation of `S`. -/
abbrev Free := FreeGroup S

/-- Evaluation of a word in the free group on the underlying type of
`S`. -/
def evaluation : Free S →* S :=
  FreeGroup.lift id

@[simp]
theorem evaluation_of (s : S) :
    evaluation S (FreeGroup.of s) = s :=
  FreeGroup.lift_apply_of

/-- The evaluation map from the canonical free presentation is
surjective. -/
theorem evaluation_surjective :
    Function.Surjective (evaluation S) :=
  FreeGroup.lift_surjective_of_surjective
    Function.surjective_id

/-- The relation subgroup in the canonical free presentation. -/
def relations : Subgroup (Free S) :=
  (evaluation S).ker

instance relations_normal :
    (relations S).Normal := by
  unfold relations
  infer_instance

/-- The derived subgroup of the free group. -/
def derived : Subgroup (Free S) :=
  _root_.commutator (Free S)

instance derived_normal :
    (derived S).Normal := by
  unfold derived
  infer_instance

/-- The subgroup `[F,R]` in the canonical free presentation. -/
def centralRelators : Subgroup (Free S) :=
  ⁅(⊤ : Subgroup (Free S)), relations S⁆

instance centralRelators_normal :
    (centralRelators S).Normal := by
  unfold centralRelators
  infer_instance

/-- The relators `[F,R]` lie in the derived subgroup. -/
theorem centralRelators_le_derived :
    centralRelators S ≤ derived S := by
  exact
    Subgroup.commutator_mono le_rfl le_top

/-- The subgroup `[F,R]`, viewed inside `[F,F]`. -/
def centralRelatorsInDerived :
    Subgroup (derived S) :=
  (centralRelators S).subgroupOf (derived S)

instance centralRelatorsInDerived_normal :
    (centralRelatorsInDerived S).Normal := by
  unfold centralRelatorsInDerived
  infer_instance

/-- The group `[F,F]/[F,R]`. -/
abbrev Cover :=
  derived S ⧸ centralRelatorsInDerived S

/-- Evaluation restricted to the derived subgroup. -/
def derivedEvaluation :
    derived S →* S :=
  (evaluation S).comp (derived S).subtype

/-- Evaluation restricted to the derived subgroup is surjective when
the target is perfect. -/
theorem derivedEvaluation_surjective
    (hperfect : Group.IsPerfect S) :
    Function.Surjective (derivedEvaluation S) := by
  have hmap :
      (derived S).map (evaluation S) = ⊤ := by
    rw [derived, map_commutator_eq,
      MonoidHom.range_eq_top.2
        (evaluation_surjective S)]
    change _root_.commutator S = ⊤
    exact hperfect.commutator_eq_top
  intro s
  have hs :
      s ∈ (derived S).map (evaluation S) := by
    rw [hmap]
    exact Subgroup.mem_top s
  obtain ⟨f, hf, rfl⟩ := hs
  exact ⟨⟨f, hf⟩, rfl⟩

/-- The subgroup `[F,R]` is killed by restricted evaluation. -/
theorem centralRelatorsInDerived_le_ker :
    centralRelatorsInDerived S ≤
      (derivedEvaluation S).ker := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  apply MonoidHom.mem_ker.mp
  exact
    (Subgroup.commutator_le_right
      (⊤ : Subgroup (Free S))
      (relations S)) hx

/-- The projection `[F,F]/[F,R] → S`. -/
def coverProjection :
    Cover S →* S :=
  QuotientGroup.lift
    (centralRelatorsInDerived S)
    (derivedEvaluation S)
    (centralRelatorsInDerived_le_ker S)

/-- The free-presentation cover is surjective over a perfect target. -/
theorem coverProjection_surjective
    (hperfect : Group.IsPerfect S) :
    Function.Surjective (coverProjection S) :=
  QuotientGroup.lift_surjective_of_surjective
    (centralRelatorsInDerived S)
    (derivedEvaluation S)
    (derivedEvaluation_surjective S hperfect)
    (centralRelatorsInDerived_le_ker S)

/-- The kernel of the free-presentation cover is central. -/
theorem coverProjection_ker_le_center :
    (coverProjection S).ker ≤
      Subgroup.center (Cover S) := by
  intro u hu
  obtain ⟨d, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (centralRelatorsInDerived S) u
  have hdRelations :
      (d : Free S) ∈ relations S := by
    apply MonoidHom.mem_ker.mpr
    exact MonoidHom.mem_ker.mp hu
  rw [Subgroup.mem_center_iff]
  intro x
  induction x using QuotientGroup.induction_on with
  | H e =>
      rw [← commutatorElement_eq_one_iff_mul_comm]
      change
        ⁅QuotientGroup.mk'
            (centralRelatorsInDerived S) e,
          QuotientGroup.mk'
            (centralRelatorsInDerived S) d⁆ = 1
      rw [← map_commutatorElement]
      apply
        (QuotientGroup.eq_one_iff
          (⁅e, d⁆ : derived S)).2
      change
        ⁅(e : Free S), (d : Free S)⁆ ∈
          centralRelators S
      rw [centralRelators]
      exact
        Subgroup.commutator_mem_commutator
          (Subgroup.mem_top _) hdRelations

/-- The canonical central extension obtained from a free presentation of
a perfect group. -/
def centralExtension
    (hperfect : Group.IsPerfect S) :
    CentralExtension (Cover S) S where
  projection := coverProjection S
  surjective := coverProjection_surjective S hperfect
  ker_le_center := coverProjection_ker_le_center S

end FreePresentation
end GroupTheory
end McKayConjecture
