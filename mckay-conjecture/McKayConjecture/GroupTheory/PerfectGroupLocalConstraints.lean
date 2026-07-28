/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.GroupTheory.Transfer
import McKayConjecture.GroupTheory.QuasisimpleSylow

/-!
# Elementary local constraints on finite perfect groups

This file collects group-theoretic filters that are useful before any
classification-dependent local-character verification.

The main new constraint is a transfer argument: a Sylow subgroup for the
least prime divisor of the order of a nontrivial finite perfect group cannot
be cyclic.  Indeed, Burnside transfer is then onto that cyclic Sylow
subgroup.  Its image would be both perfect and commutative, hence trivial,
contradicting the fact that the prime divides the group order.

For quasisimple groups we also record the resulting elementary exclusions:
they are neither solvable, nilpotent, `p`-groups, nor Z-groups, and their
orders are not squarefree.
-/

noncomputable section

open scoped IsMulCommutative

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G]

/-- If every automorphism of a group is equal, then every inner
automorphism is the identity and the group is commutative. -/
theorem isMulCommutative_of_subsingleton_mulAut
    [Subsingleton (MulAut G)] :
    IsMulCommutative G := by
  rw [isMulCommutative_iff]
  intro a b
  have hconj :
      MulAut.conj a = (1 : MulAut G) :=
    Subsingleton.elim _ _
  have hab :
      a * b * a⁻¹ = b := by
    have hvalue :=
      congrArg (fun e : MulAut G ↦ e b) hconj
    have hone : (1 : MulAut G) b = b := rfl
    simpa only [MulAut.conj_apply] using hvalue.trans hone
  calc
    a * b = (a * b * a⁻¹) * a := by simp [mul_assoc]
    _ = b * a := by rw [hab]

/-- In a nontrivial finite perfect group, the normalizer of a nontrivial
Sylow subgroup is not contained in its centralizer.

Otherwise Burnside transfer is onto the Sylow subgroup.  The image is
perfect, while the normalizer-centralizer containment makes the Sylow
subgroup commutative, forcing it to be trivial. -/
theorem perfect_sylow_normalizer_not_le_centralizer
    [Finite G] [Nontrivial G] [Group.IsPerfect G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G)
    (hp : p ∣ Nat.card G) :
    ¬Subgroup.normalizer (P : Set G) ≤
      Subgroup.centralizer (P : Set G) := by
  intro hcentralizer
  let hcentralizer' :
      Subgroup.normalizer (P : Set G) ≤
        Subgroup.centralizer (P : Set G) :=
    hcentralizer
  let f : G →* P :=
    MonoidHom.transferSylow P hcentralizer'
  have hrestricted :
      Function.Bijective
        (f.domRestrict (P : Subgroup G)) := by
    exact
      (MonoidHom.transferSylow_domRestrict_eq_pow
        P hcentralizer').symm ▸
          (P.isPGroup'.powEquiv' P.not_dvd_index).bijective
  have hsurjective : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hrestricted.2 y
    exact ⟨x.1, hx⟩
  letI : IsMulCommutative P :=
    ⟨⟨fun a b ↦
      Subtype.ext
        (hcentralizer' (Subgroup.le_normalizer b.2) a a.2)⟩⟩
  letI : Group.IsPerfect P :=
    Group.IsPerfect.ofSurjective hsurjective
  haveI : Subsingleton P :=
    Group.IsPerfect.subsingleton_of_isMulCommutative
  have hPbot :
      (P : Subgroup G) = ⊥ :=
    Subgroup.eq_bot_of_subsingleton (P : Subgroup G)
  exact P.ne_bot_of_dvd_card hp hPbot

/-- A Sylow subgroup at the least prime divisor of the order of a
nontrivial finite perfect group is not cyclic. -/
theorem perfect_sylow_not_isCyclic_of_minFac_eq
    [Finite G] [Nontrivial G] [Group.IsPerfect G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G)
    (hp : (Nat.card G).minFac = p) :
    ¬IsCyclic P := by
  intro hcyclic
  apply
    perfect_sylow_normalizer_not_le_centralizer
      P (by
        rw [← hp]
        exact Nat.minFac_dvd _)
  exact hcyclic.normalizer_le_centralizer hp

namespace IsQuasisimple

/-- A quasisimple group is not solvable. -/
theorem not_isSolvable
    (hG : IsQuasisimple G) :
    ¬Group.IsSolvable G := by
  letI : Nontrivial G := hG.nontrivial
  letI : Group.IsPerfect G := hG.isPerfect
  exact Group.IsPerfect.not_isSolvable G

/-- A finite quasisimple group is not nilpotent. -/
theorem not_isNilpotent
    [Finite G]
    (hG : IsQuasisimple G) :
    ¬Group.IsNilpotent G := by
  letI : Nontrivial G := hG.nontrivial
  letI : Group.IsPerfect G := hG.isPerfect
  exact Group.IsPerfect.not_isNilpotent G

/-- A finite quasisimple group is not a `p`-group. -/
theorem not_isPGroup
    [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hG : IsQuasisimple G) :
    ¬IsPGroup p G := by
  intro hpG
  exact hG.not_isNilpotent hpG.isNilpotent

/-- A finite quasisimple group is not a Z-group (a group all of whose
Sylow subgroups are cyclic). -/
theorem not_isZGroup
    [Finite G]
    (hG : IsQuasisimple G) :
    ¬IsZGroup G := by
  intro hZ
  letI : IsZGroup G := hZ
  exact hG.not_isSolvable inferInstance

/-- In particular, the order of a finite quasisimple group is not
squarefree. -/
theorem not_squarefree_card
    [Finite G]
    (hG : IsQuasisimple G) :
    ¬Squarefree (Nat.card G) := by
  intro hsquarefree
  exact hG.not_isZGroup
    (IsZGroup.of_squarefree hsquarefree)

/-- A normal Sylow subgroup of a finite quasisimple group is exactly a
central Sylow subgroup. -/
theorem sylow_normal_iff_le_center
    [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hG : IsQuasisimple G)
    (P : Sylow p G) :
    (P : Subgroup G).Normal ↔
      (P : Subgroup G) ≤ Subgroup.center G := by
  constructor
  · exact hG.normal_sylow_le_center P
  · intro hcentral
    refine ⟨?_⟩
    intro x hx g
    have hcomm :
        g * x = x * g :=
      Subgroup.mem_center_iff.mp (hcentral hx) g
    rw [hcomm]
    simpa using hx

/-- The Sylow normalizer of a finite quasisimple group is never contained
in the Sylow centralizer when the prime divides the group order. -/
theorem sylow_normalizer_not_le_centralizer
    [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hG : IsQuasisimple G)
    (P : Sylow p G)
    (hp : p ∣ Nat.card G) :
    ¬Subgroup.normalizer (P : Set G) ≤
      Subgroup.centralizer (P : Set G) := by
  letI : Nontrivial G := hG.nontrivial
  letI : Group.IsPerfect G := hG.isPerfect
  exact
    perfect_sylow_normalizer_not_le_centralizer
      P hp

/-- Hence a self-normalizing Sylow subgroup of a finite quasisimple group
cannot be cyclic.  Self-normalizing alone is not excluded. -/
theorem self_normalizing_sylow_not_isCyclic
    [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hG : IsQuasisimple G)
    (P : Sylow p G)
    (hp : p ∣ Nat.card G)
    (hself :
      Subgroup.normalizer (P : Set G) =
        (P : Subgroup G)) :
    ¬IsCyclic P := by
  intro hcyclic
  apply hG.sylow_normalizer_not_le_centralizer P hp
  rw [hself]
  letI : IsMulCommutative P :=
    hcyclic.isMulCommutative
  exact (P : Subgroup G).le_centralizer

/-- At the least prime divisor of its order, a Sylow subgroup of a finite
quasisimple group cannot be cyclic. -/
theorem sylow_not_isCyclic_of_minFac_eq
    [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hG : IsQuasisimple G)
    (P : Sylow p G)
    (hp : (Nat.card G).minFac = p) :
    ¬IsCyclic P := by
  letI : Nontrivial G := hG.nontrivial
  letI : Group.IsPerfect G := hG.isPerfect
  exact
    perfect_sylow_not_isCyclic_of_minFac_eq
      P hp

/-- In particular, if `2` divides the order of a finite quasisimple group,
then none of its Sylow `2`-subgroups is cyclic. -/
theorem sylow_two_not_isCyclic
    [Finite G]
    (hG : IsQuasisimple G)
    (P : Sylow 2 G)
    (h2 : 2 ∣ Nat.card G) :
    ¬IsCyclic P := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply hG.sylow_not_isCyclic_of_minFac_eq P
  exact (Nat.minFac_eq_two_iff (Nat.card G)).mpr h2

/-- A quasisimple group has a nontrivial full automorphism group. -/
theorem not_subsingleton_mulAut
    (hG : IsQuasisimple G) :
    ¬Subsingleton (MulAut G) := by
  intro hAut
  letI : Subsingleton (MulAut G) := hAut
  exact hG.not_isMulCommutative
    isMulCommutative_of_subsingleton_mulAut

end IsQuasisimple

end GroupTheory
end McKayConjecture
