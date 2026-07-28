/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Sylow

/-!
# The largest normal `p`-subgroup

The subgroup `pCore p G`, traditionally denoted `O_p(G)`, is the supremum
of all normal `p`-subgroups of `G`.  It is itself a normal `p`-subgroup,
contains every other normal `p`-subgroup, and is characteristic.

This object is one of the basic group-theoretic inputs in the minimal
counterexample reduction for the McKay theorem.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory

variable (p : ℕ) (G : Type u) [Group G]

/-- The set of normal `p`-subgroups of `G`. -/
def normalPSubgroups : Set (Subgroup G) :=
  {N | IsPGroup p N ∧ N.Normal}

/-- The largest normal `p`-subgroup of `G`, traditionally denoted
`O_p(G)`. -/
def pCore : Subgroup G :=
  sSup (normalPSubgroups p G)

variable {p G}

/-- Every normal `p`-subgroup lies in the `p`-core. -/
theorem le_pCore {N : Subgroup G}
    (hpN : IsPGroup p N) (hN : N.Normal) :
    N ≤ pCore p G :=
  le_sSup ⟨hpN, hN⟩

/-- The `p`-core is a `p`-group. -/
theorem pCore_isPGroup :
    IsPGroup p (pCore p G) := by
  apply Sylow.sSup_of_normal
  · intro N hN
    exact hN.1
  · intro N hN
    exact hN.2

/-- The `p`-core is normal. -/
instance pCore_normal :
    (pCore p G).Normal :=
  Subgroup.sSup_normal (normalPSubgroups p G)
    (fun _ hN ↦ hN.2)

/-- For a normal subgroup, containment in the `p`-core is equivalent to
being a `p`-group. -/
theorem le_pCore_iff_of_normal {N : Subgroup G}
    (hN : N.Normal) :
    N ≤ pCore p G ↔ IsPGroup p N := by
  constructor
  · intro hle
    exact pCore_isPGroup.to_le hle
  · intro hpN
    exact le_pCore hpN hN

/-- The `p`-core is contained in every Sylow `p`-subgroup. -/
theorem pCore_le_sylow (P : Sylow p G) :
    pCore p G ≤ P :=
  pCore_isPGroup.le_sylow_of_normal P

/-- A normal Sylow `p`-subgroup is the `p`-core. -/
theorem pCore_eq_sylow_of_normal (P : Sylow p G)
    (hP : (P : Subgroup G).Normal) :
    pCore p G = P := by
  apply le_antisymm
  · exact pCore_le_sylow P
  · exact le_pCore P.isPGroup' hP

/-- A `p`-group has full `p`-core. -/
theorem pCore_eq_top_of_isPGroup
    (hG : IsPGroup p G) :
    pCore p G = ⊤ := by
  apply top_unique
  exact le_pCore (hG.to_subgroup ⊤) inferInstance

/-- The `p`-core is the whole group exactly for `p`-groups. -/
theorem pCore_eq_top_iff :
    pCore p G = ⊤ ↔ IsPGroup p G := by
  constructor
  · intro htop
    have htopP :
        IsPGroup p (⊤ : Subgroup G) := by
      rw [← htop]
      exact pCore_isPGroup
    exact htopP.of_equiv Subgroup.topEquiv
  · exact pCore_eq_top_of_isPGroup

/-- The `p`-core is characteristic. -/
instance pCore_characteristic :
    (pCore p G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro e
  apply le_pCore
  · exact pCore_isPGroup.map e.toMonoidHom
  · exact Subgroup.Normal.map inferInstance
      e.toMonoidHom e.surjective

/-- Mapping the `p`-core along a surjective homomorphism lands in the
`p`-core of the target. -/
theorem map_pCore_le {H : Type v} [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    (pCore p G).map f ≤ pCore p H := by
  apply le_pCore
  · exact pCore_isPGroup.map f
  · exact Subgroup.Normal.map inferInstance f hf

/-- Pulling back a target `p`-core along a homomorphism with `p`-group
kernel lands in the source `p`-core. -/
theorem comap_pCore_le_of_ker_isPGroup
    {H : Type v} [Group H]
    (f : G →* H) (hker : IsPGroup p f.ker) :
    (pCore p H).comap f ≤ pCore p G := by
  apply le_pCore
  · exact pCore_isPGroup.comap_of_ker_isPGroup f hker
  · exact Subgroup.Normal.comap inferInstance f

/-- A surjective homomorphism with `p`-group kernel maps the `p`-core
onto the `p`-core. -/
theorem map_pCore_eq_of_ker_isPGroup
    {H : Type v} [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) :
    (pCore p G).map f = pCore p H := by
  apply le_antisymm
  · exact map_pCore_le f hf
  · have hle :
        (pCore p H).comap f ≤ pCore p G :=
      comap_pCore_le_of_ker_isPGroup f hker
    have hmap :
        ((pCore p H).comap f).map f ≤
          (pCore p G).map f :=
      Subgroup.map_mono hle
    rw [Subgroup.map_comap_eq_self_of_surjective hf] at hmap
    exact hmap

/-- Group isomorphisms carry `p`-cores to `p`-cores. -/
theorem map_pCore_equiv {H : Type v} [Group H]
    (e : G ≃* H) :
    (pCore p G).map e.toMonoidHom = pCore p H := by
  apply le_antisymm
  · exact map_pCore_le e.toMonoidHom e.surjective
  · intro y hy
    have hreverse :
        (pCore p H).map e.symm.toMonoidHom ≤ pCore p G :=
      map_pCore_le e.symm.toMonoidHom e.symm.surjective
    have hx : e.symm y ∈ pCore p G :=
      hreverse ⟨y, hy, rfl⟩
    exact ⟨e.symm y, hx, e.apply_symm_apply y⟩

/-- The `p`-core is trivial exactly when every normal `p`-subgroup is
trivial. -/
theorem pCore_eq_bot_iff :
    pCore p G = ⊥ ↔
      ∀ N : Subgroup G, IsPGroup p N → N.Normal → N = ⊥ := by
  constructor
  · intro hcore N hpN hN
    exact eq_bot_iff.mpr ((le_pCore hpN hN).trans_eq hcore)
  · intro h
    exact h (pCore p G) pCore_isPGroup inferInstance

/-- A nontrivial normal `p`-subgroup forces the `p`-core to be
nontrivial. -/
theorem pCore_ne_bot_of_normal
    {N : Subgroup G} (hpN : IsPGroup p N)
    (hN : N.Normal) (hne : N ≠ ⊥) :
    pCore p G ≠ ⊥ := by
  intro hcore
  exact hne (eq_bot_iff.mpr ((le_pCore hpN hN).trans_eq hcore))

/-- The centralizer of the characteristic `p`-core is characteristic. -/
instance pCore_centralizer_characteristic :
    (Subgroup.centralizer (pCore p G : Set G)).Characteristic :=
  inferInstance

/-- The centralizer of the `p`-core is the whole group exactly when the
`p`-core is central. -/
theorem centralizer_pCore_eq_top_iff :
    Subgroup.centralizer (pCore p G : Set G) = ⊤ ↔
      pCore p G ≤ Subgroup.center G :=
  Subgroup.centralizer_eq_top_iff_subset

/-- A noncentral `p`-core has a proper characteristic centralizer. -/
theorem centralizer_pCore_lt_top
    (h : ¬pCore p G ≤ Subgroup.center G) :
    Subgroup.centralizer (pCore p G : Set G) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  exact h ((centralizer_pCore_eq_top_iff
    (p := p) (G := G)).mp htop)

/-- Factoring out the `p`-core leaves a group with trivial `p`-core. -/
theorem pCore_quotient_pCore_eq_bot :
    pCore p (G ⧸ pCore p G) = ⊥ := by
  let q : G →* G ⧸ pCore p G :=
    QuotientGroup.mk' (pCore p G)
  have hker : IsPGroup p q.ker := by
    change
      IsPGroup p
        (QuotientGroup.mk' (pCore p G)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hmap :=
    map_pCore_eq_of_ker_isPGroup
      q (QuotientGroup.mk'_surjective
        (pCore p G)) hker
  have hmapBot :
      (pCore p G).map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    simp [q, QuotientGroup.ker_mk']
  rw [hmapBot] at hmap
  exact hmap.symm

end GroupTheory
end McKayConjecture
