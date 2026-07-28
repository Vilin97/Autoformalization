/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import McKayConjecture.Statement

/-!
# Sylow normalizers in intermediate subgroups

This file records the elementary group-theoretic facts used by the final
normalizer induction in the proof of the McKay conjecture.  If an intermediate
subgroup `N` contains a Sylow subgroup `P`, then `P` is still Sylow in `N`.  If
`N` also contains `N_G(P)`, the normalizer computed inside `N` is naturally
isomorphic to `N_G(P)`.

The final section supplies strict cardinality lemmas for well-founded induction
over proper subgroups of a finite group.
-/

noncomputable section

universe u

namespace McKayConjecture.InductiveMcKay

variable {G : Type u} [Group G] {p : ℕ}

/-- A Sylow subgroup of `G`, regarded as a Sylow subgroup of an intermediate
subgroup containing it. -/
abbrev sylowIn (P : Sylow p G) (N : Subgroup G) (hP : (P : Subgroup G) ≤ N) :
    Sylow p N :=
  P.subtype hP

@[simp]
theorem coe_sylowIn (P : Sylow p G) (N : Subgroup G)
    (hP : (P : Subgroup G) ≤ N) :
    (sylowIn P N hP : Subgroup N) = (P : Subgroup G).subgroupOf N :=
  rfl

/-- The normalizer of `P` computed in an intermediate subgroup `N` is the
subgroup of `N` cut out by the ambient normalizer. -/
theorem normalizer_sylowIn_eq_subgroupOf (P : Sylow p G) (N : Subgroup G)
    (hP : (P : Subgroup G) ≤ N) :
    Subgroup.normalizer (sylowIn P N hP : Set N) =
      (Subgroup.normalizer (P : Set G)).subgroupOf N := by
  change
    Subgroup.normalizer ((P : Subgroup G).subgroupOf N : Set N) =
      (Subgroup.normalizer (P : Set G)).subgroupOf N
  exact (Subgroup.subgroupOf_normalizer_eq hP).symm

/-- When `N_G(P) ≤ N`, the normalizer computed inside `N` is naturally
isomorphic to the ambient normalizer `N_G(P)`. -/
def normalizerInEquivNormalizer (P : Sylow p G) (N : Subgroup G)
    (hP : (P : Subgroup G) ≤ N)
    (hNormalizer : Subgroup.normalizer (P : Set G) ≤ N) :
    Subgroup.normalizer (sylowIn P N hP : Set N) ≃*
      Subgroup.normalizer (P : Set G) :=
  (MulEquiv.subgroupCongr (normalizer_sylowIn_eq_subgroupOf P N hP)).trans
    (Subgroup.subgroupOfEquivOfLe hNormalizer)

@[simp]
theorem normalizerInEquivNormalizer_apply_coe (P : Sylow p G) (N : Subgroup G)
    (hP : (P : Subgroup G) ≤ N)
    (hNormalizer : Subgroup.normalizer (P : Set G) ≤ N)
    (x : Subgroup.normalizer (sylowIn P N hP : Set N)) :
    ((normalizerInEquivNormalizer P N hP hNormalizer x :
        Subgroup.normalizer (P : Set G)) : G) = x.1.1 :=
  rfl

/-- Under the inclusion `N ↪ G`, the normalizer computed inside `N` maps to
the ambient normalizer, provided the latter lies in `N`. -/
theorem map_normalizer_sylowIn_eq (P : Sylow p G) (N : Subgroup G)
    (hP : (P : Subgroup G) ≤ N)
    (hNormalizer : Subgroup.normalizer (P : Set G) ≤ N) :
    (Subgroup.normalizer (sylowIn P N hP : Set N)).map N.subtype =
      Subgroup.normalizer (P : Set G) := by
  rw [normalizer_sylowIn_eq_subgroupOf P N hP]
  exact Subgroup.map_subgroupOf_eq_of_le hNormalizer

/-- A proper subgroup of a finite subgroup has strictly smaller cardinality. -/
theorem natCard_lt_of_lt [Finite G] {H K : Subgroup G} (hHK : H < K) :
    Nat.card H < Nat.card K := by
  obtain ⟨x, hxK, hxH⟩ := SetLike.exists_of_lt hHK
  have hx : ¬((⟨x, hxK⟩ : K) ∈ H.subgroupOf K) := hxH
  have hcard := Finite.card_subtype_lt hx
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK.le).toEquiv] at hcard
  exact hcard

/-- A proper subgroup of a finite group has strictly smaller cardinality than
the ambient group. -/
theorem natCard_lt_of_lt_top [Finite G] {N : Subgroup G} (hN : N < ⊤) :
    Nat.card N < Nat.card G := by
  rw [← Subgroup.card_top (G := G)]
  exact natCard_lt_of_lt hN

/-- Strong induction over subgroups of a finite group, justified by subgroup
cardinality.  This is the recursion principle used by normalizer induction. -/
theorem subgroup_strong_induction [Finite G] {motive : Subgroup G → Prop}
    (step : ∀ H : Subgroup G, (∀ K : Subgroup G, K < H → motive K) → motive H)
    (H : Subgroup G) : motive H := by
  refine Nat.strong_induction_on (Nat.card H)
    (p := fun n => ∀ H : Subgroup G, Nat.card H = n → motive H) ?_ H rfl
  intro n ih H hcard
  apply step H
  intro K hKH
  exact ih (Nat.card K) (hcard ▸ natCard_lt_of_lt hKH) K rfl

end McKayConjecture.InductiveMcKay
