/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Complement

/-!
# Lifting complementary subgroups from a quotient

Let `D` be a normal subgroup of a group `H`.  A subgroup of `H ⧸ D`
lifts to its full preimage in `H`.  If that quotient subgroup complements
the image of a subgroup `K` containing `D`, then the two full preimages
generate `H` and intersect in exactly `D`.

These elementary consequences of the subgroup correspondence theorem are
packaged here so applications can use quotient complements without repeatedly
unfolding maps and comaps.
-/

namespace McKayConjecture
namespace GroupTheory

variable {H : Type*} [Group H]

/-- The full preimage in `H` of a subgroup of `H ⧸ D`. -/
def quotientComplementLift
    (D : Subgroup H) [D.Normal]
    (Ubar : Subgroup (H ⧸ D)) :
    Subgroup H :=
  Ubar.comap (QuotientGroup.mk' D)

/-- The normal subgroup defining the quotient lies in every full preimage. -/
theorem normal_le_quotientComplementLift
    (D : Subgroup H) [D.Normal]
    (Ubar : Subgroup (H ⧸ D)) :
    D ≤ quotientComplementLift D Ubar :=
  QuotientGroup.le_comap_mk' D Ubar

/-- Mapping a lifted quotient subgroup back to the quotient recovers it. -/
@[simp]
theorem map_quotientComplementLift
    (D : Subgroup H) [D.Normal]
    (Ubar : Subgroup (H ⧸ D)) :
    (quotientComplementLift D Ubar).map
        (QuotientGroup.mk' D) =
      Ubar :=
  Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective D) Ubar

/-- If `Ubar` complements the quotient image of `K`, then `K` and the
full preimage of `Ubar` generate the ambient group. -/
theorem quotientComplementLift_sup_eq_top
    (D K : Subgroup H) [D.Normal]
    (hDK : D ≤ K)
    (Ubar : Subgroup (H ⧸ D))
    (hcomplement :
      (K.map (QuotientGroup.mk' D)).IsComplement' Ubar) :
    K ⊔ quotientComplementLift D Ubar = ⊤ := by
  have hcomapK :
      (K.map (QuotientGroup.mk' D)).comap
          (QuotientGroup.mk' D) =
        K := by
    rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hDK]
  rw [
    ← hcomapK,
    quotientComplementLift,
    Subgroup.comap_sup_eq
      (QuotientGroup.mk' D) _ _
      (QuotientGroup.mk'_surjective D),
    hcomplement.sup_eq_top,
    Subgroup.comap_top
  ]

/-- If `Ubar` complements the quotient image of `K`, then `K` meets the
full preimage of `Ubar` in exactly the quotient kernel `D`. -/
theorem quotientComplementLift_inf_eq_normal
    (D K : Subgroup H) [D.Normal]
    (hDK : D ≤ K)
    (Ubar : Subgroup (H ⧸ D))
    (hcomplement :
      (K.map (QuotientGroup.mk' D)).IsComplement' Ubar) :
    K ⊓ quotientComplementLift D Ubar = D := by
  have hcomapK :
      (K.map (QuotientGroup.mk' D)).comap
          (QuotientGroup.mk' D) =
        K := by
    rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hDK]
  rw [
    ← hcomapK,
    quotientComplementLift,
    ← Subgroup.comap_inf,
    hcomplement.disjoint.eq_bot,
    MonoidHom.comap_bot,
    QuotientGroup.ker_mk'
  ]

end GroupTheory
end McKayConjecture
