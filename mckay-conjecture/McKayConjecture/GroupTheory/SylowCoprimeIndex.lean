/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Sylow

/-!
# Sylow subgroups inside subgroups of prime-to-`p` index

If a subgroup `H ≤ G` has index prime to `p`, then a Sylow `p`-subgroup
of `H`, mapped into `G`, is already a Sylow `p`-subgroup of `G`.
Consequently every prescribed Sylow subgroup of `G` has a conjugate
contained in `H`.

This elementary bridge is useful for active Clifford orbits: their inertia
subgroups have prime-to-`p` index, so one may choose an orbit representative
whose inertia subgroup contains the prescribed ambient Sylow subgroup.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory
namespace Sylow

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A Sylow subgroup of a prime-to-`p` index subgroup, mapped into the
ambient group, is an ambient Sylow subgroup. -/
def mapSubtypeOfNotDvdIndex
    (H : Subgroup G)
    (hH : ¬p ∣ H.index)
    (Q : Sylow p H) :
    Sylow p G :=
  (Q.isPGroup'.map H.subtype).toSylow <| by
    rw [Subgroup.index_map_subtype]
    exact
      Nat.Prime.not_dvd_mul Fact.out
        Q.not_dvd_index hH

@[simp]
theorem coe_mapSubtypeOfNotDvdIndex
    (H : Subgroup G)
    (hH : ¬p ∣ H.index)
    (Q : Sylow p H) :
    (mapSubtypeOfNotDvdIndex H hH Q : Subgroup G) =
      (Q : Subgroup H).map H.subtype :=
  rfl

/-- The mapped Sylow subgroup is contained in the subgroup through which
it was constructed. -/
theorem mapSubtypeOfNotDvdIndex_le
    (H : Subgroup G)
    (hH : ¬p ∣ H.index)
    (Q : Sylow p H) :
    (mapSubtypeOfNotDvdIndex H hH Q : Subgroup G) ≤ H := by
  rw [coe_mapSubtypeOfNotDvdIndex]
  exact
    (Subgroup.map_le_range H.subtype (Q : Subgroup H)).trans
      H.range_subtype.le

/-- A subgroup of prime-to-`p` index contains an ambient Sylow
`p`-subgroup. -/
theorem exists_le_of_not_dvd_index
    (H : Subgroup G)
    (hH : ¬p ∣ H.index) :
    ∃ Q : Sylow p G, (Q : Subgroup G) ≤ H :=
  ⟨mapSubtypeOfNotDvdIndex H hH default,
    mapSubtypeOfNotDvdIndex_le H hH default⟩

/-- Every prescribed ambient Sylow subgroup has a conjugate contained in
a subgroup of prime-to-`p` index. -/
theorem exists_smul_le_of_not_dvd_index
    (P : Sylow p G)
    (H : Subgroup G)
    (hH : ¬p ∣ H.index) :
    ∃ g : G, (g • P : Sylow p G) ≤ H := by
  let Q : Sylow p G :=
    mapSubtypeOfNotDvdIndex H hH default
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g, ?_⟩
  rw [hg]
  exact mapSubtypeOfNotDvdIndex_le H hH default

end Sylow
end GroupTheory
end McKayConjecture
