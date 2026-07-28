/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Data.SetLike.Fintype
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Order.Minimal

/-!
# Minimal normal subgroups

This file packages nontrivial minimal normal subgroups and the elementary
finite-group facts used in reduction arguments: existence below every
nontrivial normal subgroup, equality-or-disjointness, and commutation of
distinct minimal normal subgroups.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

open scoped IsMulCommutative

variable {G : Type u} [Group G]

/-- A minimal normal subgroup is a minimal element among the nontrivial
normal subgroups. -/
def IsMinimalNormal (N : Subgroup G) : Prop :=
  Minimal (fun M : Subgroup G ↦ M.Normal ∧ M ≠ ⊥) N

namespace IsMinimalNormal

variable {N M : Subgroup G}

/-- A minimal normal subgroup is normal. -/
theorem normal (hN : IsMinimalNormal N) :
    N.Normal :=
  hN.1.1

/-- A minimal normal subgroup is nontrivial. -/
theorem ne_bot (hN : IsMinimalNormal N) :
    N ≠ ⊥ :=
  hN.1.2

/-- Any nontrivial normal subgroup contained in a minimal normal subgroup
is equal to it. -/
theorem eq_of_normal_le
    (hN : IsMinimalNormal N)
    (hMnormal : M.Normal) (hMne : M ≠ ⊥)
    (hMN : M ≤ N) :
    M = N :=
  le_antisymm hMN (hN.2 ⟨hMnormal, hMne⟩ hMN)

/-- A normal subgroup contained in a minimal normal subgroup is either
trivial or the whole minimal normal subgroup. -/
theorem eq_bot_or_eq
    (hN : IsMinimalNormal N)
    (hMnormal : M.Normal) (hMN : M ≤ N) :
    M = ⊥ ∨ M = N := by
  by_cases hM : M = ⊥
  · exact Or.inl hM
  · exact Or.inr (hN.eq_of_normal_le hMnormal hM hMN)

/-- Two minimal normal subgroups are equal or disjoint. -/
theorem eq_or_disjoint
    (hN : IsMinimalNormal N)
    (hM : IsMinimalNormal M) :
    N = M ∨ Disjoint N M := by
  letI : N.Normal := hN.normal
  letI : M.Normal := hM.normal
  by_cases hInf : N ⊓ M = ⊥
  · exact Or.inr (by simpa [disjoint_iff] using hInf.le)
  · left
    have hNleInf :
        N ≤ N ⊓ M :=
      hN.2 ⟨(inferInstance : (N ⊓ M).Normal), hInf⟩ inf_le_left
    have hNleM : N ≤ M :=
      hNleInf.trans inf_le_right
    have hMleN : M ≤ N :=
      hM.2 ⟨hN.normal, hN.ne_bot⟩ hNleM
    exact le_antisymm hNleM hMleN

/-- Distinct minimal normal subgroups are disjoint. -/
theorem disjoint_of_ne
    (hN : IsMinimalNormal N)
    (hM : IsMinimalNormal M)
    (hne : N ≠ M) :
    Disjoint N M :=
  (hN.eq_or_disjoint hM).resolve_left hne

/-- Elements of distinct minimal normal subgroups commute. -/
theorem commute_of_ne
    (hN : IsMinimalNormal N)
    (hM : IsMinimalNormal M)
    (hne : N ≠ M)
    {x y : G} (hx : x ∈ N) (hy : y ∈ M) :
    Commute x y :=
  Subgroup.commute_of_normal_of_disjoint
    N M hN.normal hM.normal
      (hN.disjoint_of_ne hM hne) x y hx hy

/-- Minimal normal subgroups transport across group isomorphisms. -/
theorem map_equiv
    {H : Type*} [Group H]
    (hN : IsMinimalNormal N) (e : G ≃* H) :
    IsMinimalNormal (N.map e.toMonoidHom) := by
  constructor
  · constructor
    · exact Subgroup.Normal.map hN.normal
        e.toMonoidHom e.surjective
    · intro hbot
      exact hN.ne_bot
        ((N.map_eq_bot_iff_of_injective
          e.injective).mp hbot)
  · intro L hL hLle
    have hcomapNormal :
        (L.comap e.toMonoidHom).Normal :=
      Subgroup.Normal.comap hL.1 e.toMonoidHom
    have hcomapNe :
        L.comap e.toMonoidHom ≠ ⊥ := by
      intro hbot
      apply hL.2
      calc
        L =
            (L.comap e.toMonoidHom).map
              e.toMonoidHom :=
          (Subgroup.map_comap_eq_self_of_surjective
            e.surjective L).symm
        _ = ⊥ := by rw [hbot, Subgroup.map_bot]
    have hcomapLe :
        L.comap e.toMonoidHom ≤ N := by
      rw [← Subgroup.comap_map_eq_self_of_injective
        (f := e.toMonoidHom) e.injective N]
      exact Subgroup.comap_mono hLle
    have hNle :
        N ≤ L.comap e.toMonoidHom :=
      hN.2 ⟨hcomapNormal, hcomapNe⟩ hcomapLe
    have hmapLe :
        N.map e.toMonoidHom ≤
          (L.comap e.toMonoidHom).map
            e.toMonoidHom :=
      Subgroup.map_mono hNle
    rw [Subgroup.map_comap_eq_self_of_surjective
      e.surjective L] at hmapLe
    exact hmapLe

/-- A minimal normal subgroup contained in the center is a simple group. -/
theorem isSimpleGroup_of_le_center
    (hN : IsMinimalNormal N)
    (hcenter : N ≤ Subgroup.center G) :
    IsSimpleGroup N := by
  rw [Subgroup.isSimpleGroup_iff]
  refine ⟨hN.ne_bot, ?_⟩
  intro L hLN _
  have hLnormal : L.Normal :=
    ⟨fun x hx g ↦ by
      simpa [Subgroup.mem_center_iff.mp
        (hcenter (hLN hx)) g] using hx⟩
  exact hN.eq_bot_or_eq hLnormal hLN

/-- A central minimal normal subgroup has prime order. -/
theorem prime_natCard_of_le_center
    (hN : IsMinimalNormal N)
    (hcenter : N ≤ Subgroup.center G) :
    (Nat.card N).Prime := by
  letI : IsMulCommutative N :=
    ⟨⟨fun x y ↦
      Subtype.ext
        ((Subgroup.mem_center_iff.mp
          (hcenter x.property) (y : G)).symm)⟩⟩
  letI : CommGroup N := inferInstance
  letI : IsSimpleGroup N :=
    hN.isSimpleGroup_of_le_center hcenter
  exact IsSimpleGroup.prime_card

end IsMinimalNormal

/-- Every nontrivial normal subgroup of a finite group contains a minimal
normal subgroup. -/
theorem exists_minimalNormal_le
    [Finite G] {N : Subgroup G}
    (hNnormal : N.Normal) (hNne : N ≠ ⊥) :
    ∃ M : Subgroup G, IsMinimalNormal M ∧ M ≤ N := by
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨M, hMN, hM⟩ :=
    exists_minimal_le_of_wellFoundedLT
      (fun L : Subgroup G ↦ L.Normal ∧ L ≠ ⊥)
      N ⟨hNnormal, hNne⟩
  exact ⟨M, hM, hMN⟩

/-- Every nontrivial finite group has a minimal normal subgroup. -/
theorem exists_minimalNormal
    [Finite G] [Nontrivial G] :
    ∃ M : Subgroup G, IsMinimalNormal M := by
  obtain ⟨M, hM, _⟩ :=
    exists_minimalNormal_le
      (G := G) (N := ⊤) inferInstance (top_ne_bot)
  exact ⟨M, hM⟩

/-- The socle is the subgroup generated by all minimal normal subgroups. -/
def socle (G : Type u) [Group G] : Subgroup G :=
  sSup {N : Subgroup G | IsMinimalNormal N}

/-- Every minimal normal subgroup lies in the socle. -/
theorem le_socle {N : Subgroup G}
    (hN : IsMinimalNormal N) :
    N ≤ socle G :=
  le_sSup hN

/-- The socle is normal. -/
instance socle_normal :
    (socle G).Normal :=
  Subgroup.sSup_normal
    {N : Subgroup G | IsMinimalNormal N}
    (fun _ hN ↦ hN.normal)

/-- An isomorphism maps the source socle into the target socle. -/
theorem map_socle_le_equiv
    {H : Type*} [Group H] (e : G ≃* H) :
    (socle G).map e.toMonoidHom ≤ socle H := by
  rw [socle, sSup_eq_iSup,
    Subgroup.map_iSup]
  apply iSup_le
  intro N
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro hN
  simpa [socle, sSup_eq_iSup] using
    (le_socle (hN.map_equiv e))

/-- Group isomorphisms carry socles to socles. -/
theorem map_socle_equiv
    {H : Type*} [Group H] (e : G ≃* H) :
    (socle G).map e.toMonoidHom = socle H := by
  apply le_antisymm
  · exact map_socle_le_equiv e
  · intro y hy
    have hreverse :
        (socle H).map e.symm.toMonoidHom ≤ socle G :=
      map_socle_le_equiv e.symm
    have hx : e.symm y ∈ socle G :=
      hreverse ⟨y, hy, rfl⟩
    exact ⟨e.symm y, hx, e.apply_symm_apply y⟩

/-- The socle is characteristic. -/
instance socle_characteristic :
    (socle G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  exact map_socle_equiv

/-- A nontrivial finite group has nontrivial socle. -/
theorem socle_ne_bot [Finite G] [Nontrivial G] :
    socle G ≠ ⊥ := by
  obtain ⟨N, hN⟩ :=
    exists_minimalNormal (G := G)
  intro hsocle
  exact hN.ne_bot
    (eq_bot_iff.mpr ((le_socle hN).trans_eq hsocle))

end GroupTheory
end McKayConjecture
