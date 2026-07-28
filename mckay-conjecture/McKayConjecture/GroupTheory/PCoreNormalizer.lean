/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.PCore

/-!
# The `p`-core and Sylow normalizers

The center and the `p`-core of a group are contained in the normalizer of
every Sylow `p`-subgroup.  Consequently, adjoining either subgroup to a
Sylow normalizer does not enlarge it.

These elementary identities are used in the minimal-counterexample step of
the McKay reduction.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G] {p : ℕ}

/-- The center lies in the normalizer of a Sylow subgroup. -/
theorem center_le_sylowNormalizer (P : Sylow p G) :
    Subgroup.center G ≤ Subgroup.normalizer (P : Set G) :=
  Subgroup.center_le_normalizer (P : Set G)

/-- The `p`-core lies in the normalizer of a Sylow subgroup. -/
theorem pCore_le_sylowNormalizer (P : Sylow p G) :
    pCore p G ≤ Subgroup.normalizer (P : Set G) :=
  (pCore_le_sylow P).trans Subgroup.le_normalizer

/-- The join of the center and the `p`-core lies in every Sylow
normalizer. -/
theorem center_sup_pCore_le_sylowNormalizer (P : Sylow p G) :
    Subgroup.center G ⊔ pCore p G ≤
      Subgroup.normalizer (P : Set G) :=
  sup_le (center_le_sylowNormalizer P)
    (pCore_le_sylowNormalizer P)

/-- Adjoining the center and the `p`-core to a Sylow normalizer does not
change the normalizer. -/
@[simp]
theorem center_sup_pCore_sup_sylowNormalizer (P : Sylow p G) :
    (Subgroup.center G ⊔ pCore p G) ⊔
        Subgroup.normalizer (P : Set G) =
      Subgroup.normalizer (P : Set G) :=
  sup_eq_right.mpr (center_sup_pCore_le_sylowNormalizer P)

/-- If the center, the `p`-core, and a Sylow normalizer generate the whole
group, then the Sylow subgroup is normal. -/
theorem sylow_normal_of_center_sup_pCore_sup_normalizer_eq_top
    (P : Sylow p G)
    (hgenerate :
      (Subgroup.center G ⊔ pCore p G) ⊔
          Subgroup.normalizer (P : Set G) =
        ⊤) :
    (P : Subgroup G).Normal := by
  rw [center_sup_pCore_sup_sylowNormalizer P] at hgenerate
  exact Subgroup.normalizer_eq_top_iff.mp hgenerate

end GroupTheory
end McKayConjecture
