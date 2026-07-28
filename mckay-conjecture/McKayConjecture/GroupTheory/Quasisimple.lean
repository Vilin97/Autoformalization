/-
Copyright (c) 2026 Yawara Ishida.
Copyright (c) 2026 Clawristotle contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida, Clawristotle contributors
-/
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Quasisimple groups

This heartbeat-clean foundation is adapted from Yawara Ishida's
Apache-licensed `odd-order` development.  A group is quasisimple when it is
perfect and its quotient by its center is simple.  These are the groups on
which the classification-dependent inductive McKay hypothesis is imposed.

The file also proves the basic fact that every proper normal subgroup of a
quasisimple group is central.
-/

noncomputable section

open Subgroup QuotientGroup
open scoped IsMulCommutative commutatorElement Pointwise

universe u v

namespace McKayConjecture.GroupTheory

/-- A group is quasisimple when it is perfect and its central quotient is
simple. -/
structure IsQuasisimple (G : Type u) [Group G] : Prop where
  isPerfect : Group.IsPerfect G
  isSimpleGroup_quotient : IsSimpleGroup (G ⧸ center G)

variable {G : Type u} [Group G]

/-- A surjective homomorphism sends the center into the center. -/
theorem map_center_le_center_of_surjective
    {H : Type v} [Group H] {f : G →* H}
    (hf : Function.Surjective f) :
    (center G).map f ≤ center H := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro h
  obtain ⟨g, rfl⟩ := hf h
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]

/-- A group isomorphism maps the center onto the center. -/
theorem map_center_mulEquiv {H : Type v} [Group H] (e : G ≃* H) :
    (center G).map e.toMonoidHom = center H := by
  refine le_antisymm
    (map_center_le_center_of_surjective e.surjective) ?_
  intro h hh
  refine ⟨e.symm h, Subgroup.mem_center_iff.mpr (fun g ↦ e.injective ?_),
    e.apply_symm_apply h⟩
  simp only [map_mul, MulEquiv.apply_symm_apply]
  exact Subgroup.mem_center_iff.mp hh (e g)

/-- If the image of the center under a homomorphism is the whole codomain,
then the codomain is commutative. -/
theorem isMulCommutative_of_map_center_eq_top
    {H : Type v} [Group H] {f : G →* H}
    (h : (center G).map f = ⊤) :
    IsMulCommutative H :=
  IsMulCommutative.of_comm fun x y ↦ by
    have hx : x ∈ (center G).map f :=
      h ▸ Subgroup.mem_top x
    have hy : y ∈ (center G).map f :=
      h ▸ Subgroup.mem_top y
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, _, rfl⟩ := hy
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp ha b]

/-- The commutator subgroup of a commutative group is trivial. -/
theorem commutator_eq_bot_of_isMulCommutative
    [IsMulCommutative G] :
    commutator G = ⊥ := by
  rw [_root_.commutator_def, eq_bot_iff,
    Subgroup.commutator_le]
  intro g₁ _ g₂ _
  exact Subgroup.mem_bot.mpr
    (commutatorElement_eq_one_iff_mul_comm.mpr
      (mul_comm' g₁ g₂))

/-- A normal subgroup whose join with the center is the whole group contains
the commutator subgroup. -/
theorem commutator_le_of_sup_center_eq_top
    {N : Subgroup G} (hN : N.Normal)
    (h : N ⊔ center G = ⊤) :
    commutator G ≤ N := by
  letI := hN
  have hcover :
      (center G).map (QuotientGroup.mk' N) = ⊤ := by
    have hmap :=
      congrArg (Subgroup.map (QuotientGroup.mk' N)) h
    have hNbot : N.map (QuotientGroup.mk' N) = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr
        (QuotientGroup.ker_mk' N).symm.le
    rw [Subgroup.map_sup, hNbot, bot_sup_eq,
      Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective N)] at hmap
    exact hmap
  haveI : IsMulCommutative (G ⧸ N) :=
    isMulCommutative_of_map_center_eq_top hcover
  have hmapcomm :
      (commutator G).map (QuotientGroup.mk' N) = ⊥ := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective N),
      ← _root_.commutator_def,
      commutator_eq_bot_of_isMulCommutative]
  have hle := (Subgroup.map_eq_bot_iff _).mp hmapcomm
  rwa [QuotientGroup.ker_mk'] at hle

/-- When `G/Z(G)` is simple, a normal subgroup not contained in the center
joins the center to give all of `G`. -/
theorem normal_sup_center_eq_top
    (hs : IsSimpleGroup (G ⧸ center G))
    {N : Subgroup G} (hN : N.Normal) (hnle : ¬N ≤ center G) :
    N ⊔ center G = ⊤ := by
  letI := hs
  have hmapne :
      N.map (QuotientGroup.mk' (center G)) ≠ ⊥ := by
    intro hbot
    apply hnle
    intro n hn
    have hmem :
        QuotientGroup.mk' (center G) n ∈
          N.map (QuotientGroup.mk' (center G)) :=
      Subgroup.mem_map_of_mem _ hn
    rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker,
      QuotientGroup.ker_mk'] at hmem
    exact hmem
  have hnormal :
      (N.map (QuotientGroup.mk' (center G))).Normal :=
    Subgroup.Normal.map hN _
      (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · exact (hmapne hbot).elim
  · have hcomap :=
      congrArg
        (Subgroup.comap (QuotientGroup.mk' (center G))) htop
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      Subgroup.comap_top] at hcomap

namespace IsQuasisimple

/-- A quasisimple group is nontrivial. -/
theorem nontrivial (hq : IsQuasisimple G) : Nontrivial G := by
  letI := hq.isSimpleGroup_quotient
  obtain ⟨q₁, q₂, hne⟩ :=
    exists_pair_ne (G ⧸ center G)
  obtain ⟨g₁, rfl⟩ :=
    QuotientGroup.mk'_surjective (center G) q₁
  obtain ⟨g₂, rfl⟩ :=
    QuotientGroup.mk'_surjective (center G) q₂
  exact ⟨g₁, g₂, fun h ↦ hne (by rw [h])⟩

/-- The center of a quasisimple group is proper. -/
theorem center_ne_top (hq : IsQuasisimple G) :
    center G ≠ ⊤ := by
  intro h
  letI := hq.isSimpleGroup_quotient
  have hone : ∀ q : G ⧸ center G, q = 1 := by
    intro q
    obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective (center G) q
    apply (QuotientGroup.eq_one_iff x).mpr
    rw [h]
    exact Subgroup.mem_top x
  obtain ⟨q₁, q₂, hne⟩ :=
    exists_pair_ne (G ⧸ center G)
  exact hne ((hone q₁).trans (hone q₂).symm)

/-- A quasisimple group is noncommutative. -/
theorem not_isMulCommutative (hq : IsQuasisimple G) :
    ¬IsMulCommutative G := by
  intro _
  apply hq.center_ne_top
  apply (Subgroup.eq_top_iff' _).mpr
  intro g
  exact Subgroup.mem_center_iff.mpr
    (fun h ↦ mul_comm' h g)

/-- Every proper normal subgroup of a quasisimple group is central. -/
theorem normal_le_center
    (hq : IsQuasisimple G) {N : Subgroup G}
    (hN : N.Normal) (hne : N ≠ ⊤) :
    N ≤ center G := by
  by_contra hnle
  have hsup :=
    normal_sup_center_eq_top
      hq.isSimpleGroup_quotient hN hnle
  have hle :=
    commutator_le_of_sup_center_eq_top hN hsup
  rw [hq.isPerfect.commutator_eq_top] at hle
  exact hne (top_le_iff.mp hle)

/-- Quasisimplicity is invariant under group isomorphism. -/
theorem of_mulEquiv {H : Type v} [Group H]
    (e : G ≃* H) (hq : IsQuasisimple G) :
    IsQuasisimple H := by
  refine ⟨?_, ?_⟩
  · letI := hq.isPerfect
    exact Group.IsPerfect.ofSurjective
      (f := e.toMonoidHom) e.surjective
  · letI := hq.isSimpleGroup_quotient
    exact
      ((QuotientGroup.congr
        (center G) (center H) e
        (map_center_mulEquiv e)).symm).isSimpleGroup

end IsQuasisimple
end McKayConjecture.GroupTheory
