/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow
import McKayConjecture.GroupTheory.Quasisimple

/-!
# Sylow subgroups of finite quasisimple groups

A normal nilpotent subgroup of a finite quasisimple group is central.
Indeed, every proper normal subgroup of a quasisimple group is central,
while the whole group cannot be nilpotent: a quasisimple group is
nontrivial and perfect, and a nontrivial perfect group is not nilpotent.

For a prime `p`, finite `p`-groups are nilpotent.  Consequently every
normal `p`-subgroup, and in particular every normal Sylow `p`-subgroup,
of a finite quasisimple group lies in the center.  Contrapositively, a
noncentral Sylow subgroup has a proper normalizer.

The primality assumption is essential for the passage from `IsPGroup p`
to nilpotence; it is carried by `[Fact p.Prime]`, as in mathlib's Sylow
API.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G]

/-- A nontrivial finite `p`-group is not perfect. -/
theorem IsPGroup.not_isPerfect_of_finite
    [Finite G] [Nontrivial G] {p : ℕ}
    [Fact p.Prime] (hpG : IsPGroup p G) :
    ¬ Group.IsPerfect G := by
  intro hperfect
  letI : Group.IsPerfect G := hperfect
  exact Group.IsPerfect.not_isNilpotent G hpG.isNilpotent

/-- Every normal nilpotent subgroup of a finite quasisimple group lies in
the center. -/
theorem IsQuasisimple.normal_isNilpotent_le_center
    [Finite G] (hG : IsQuasisimple G)
    {N : Subgroup G} (hNnormal : N.Normal)
    (hNnilpotent : Group.IsNilpotent N) :
    N ≤ Subgroup.center G := by
  by_cases hNtop : N = ⊤
  · subst N
    letI : Nontrivial G := hG.nontrivial
    letI : Group.IsPerfect G := hG.isPerfect
    letI : Group.IsNilpotent (⊤ : Subgroup G) :=
      hNnilpotent
    have hGnilpotent : Group.IsNilpotent G :=
      Group.nilpotent_of_mulEquiv Subgroup.topEquiv
    exact False.elim
      (Group.IsPerfect.not_isNilpotent G hGnilpotent)
  · exact hG.normal_le_center hNnormal hNtop

/-- Every normal `p`-subgroup of a finite quasisimple group lies in the
center. -/
theorem IsQuasisimple.normal_isPGroup_le_center
    [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsQuasisimple G) {N : Subgroup G}
    (hpN : IsPGroup p N) (hNnormal : N.Normal) :
    N ≤ Subgroup.center G :=
  hG.normal_isNilpotent_le_center
    hNnormal hpN.isNilpotent

/-- A normal Sylow subgroup of a finite quasisimple group is central. -/
theorem IsQuasisimple.normal_sylow_le_center
    [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsQuasisimple G) (P : Sylow p G)
    (hPnormal : (P : Subgroup G).Normal) :
    (P : Subgroup G) ≤ Subgroup.center G :=
  hG.normal_isPGroup_le_center
    P.isPGroup' hPnormal

/-- A noncentral Sylow subgroup of a finite quasisimple group has a
proper normalizer. -/
theorem IsQuasisimple.normalizer_sylow_lt_top_of_not_le_center
    [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsQuasisimple G) (P : Sylow p G)
    (hPnoncentral :
      ¬(P : Subgroup G) ≤ Subgroup.center G) :
    Subgroup.normalizer (P : Set G) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro hnormalizer
  have hPnormal : (P : Subgroup G).Normal :=
    Subgroup.normalizer_eq_top_iff.mp hnormalizer
  exact hPnoncentral
    (hG.normal_sylow_le_center P hPnormal)

end GroupTheory
end McKayConjecture
