/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Subgroup.Centralizer
import McKayConjecture.GroupTheory.QuotientEquivalenceTransport

/-!
# Automorphisms restricted to invariant subgroups

An automorphism carrying a subgroup to itself restricts to that subgroup
and descends to the corresponding quotient.  This file also records the
elementary invariance formulas for normalizers and fixed-point subgroups.

The constructions are deliberately phrased for one automorphism and one
proof of invariance.  Applications can assemble them into homomorphisms of
automorphism groups when the acting group is fixed.
-/

namespace McKayConjecture
namespace GroupTheory

universe u

variable {G : Type u} [Group G]

/-- Restrict an automorphism to a subgroup that it maps to itself. -/
def invariantSubgroupAutomorphism
    (e : MulAut G) (H : Subgroup G)
    (hH : H.map e.toMonoidHom = H) :
    MulAut H :=
  (e.subgroupMap H).trans
    (MulEquiv.subgroupCongr hH)

@[simp]
theorem invariantSubgroupAutomorphism_apply_coe
    (e : MulAut G) (H : Subgroup G)
    (hH : H.map e.toMonoidHom = H)
    (x : H) :
    ((invariantSubgroupAutomorphism e H hH x : H) : G) =
      e x :=
  rfl

@[simp]
theorem invariantSubgroupAutomorphism_symm_apply_coe
    (e : MulAut G) (H : Subgroup G)
    (hH : H.map e.toMonoidHom = H)
    (x : H) :
    (((invariantSubgroupAutomorphism e H hH).symm x : H) : G) =
      e.symm x := by
  apply e.injective
  simpa only [
    e.apply_symm_apply,
    invariantSubgroupAutomorphism_apply_coe
  ] using
    congrArg Subtype.val
      ((invariantSubgroupAutomorphism e H hH).apply_symm_apply x)

/-- The restricted automorphism commutes with the subgroup inclusion. -/
theorem invariantSubgroupAutomorphism_subtype_commutes
    (e : MulAut G) (H : Subgroup G)
    (hH : H.map e.toMonoidHom = H) :
    e.toMonoidHom.comp H.subtype =
      H.subtype.comp
        (invariantSubgroupAutomorphism
          e H hH).toMonoidHom := by
  ext x
  rfl

variable (N : Subgroup G) [N.Normal]

/-- Descend an automorphism preserving a normal subgroup to the quotient. -/
def invariantQuotientAutomorphism
    (e : MulAut G)
    (hN : N.map e.toMonoidHom = N) :
    MulAut (G ⧸ N) :=
  quotientMulEquivOfSubgroupEquiv
    e
    (invariantSubgroupAutomorphism e N hN)
    (invariantSubgroupAutomorphism_subtype_commutes
      e N hN)

@[simp]
theorem invariantQuotientAutomorphism_mk
    (e : MulAut G)
    (hN : N.map e.toMonoidHom = N)
    (g : G) :
    invariantQuotientAutomorphism N e hN
        (QuotientGroup.mk' N g) =
      QuotientGroup.mk' N (e g) :=
  quotientMulEquivOfSubgroupEquiv_mk
    e
    (invariantSubgroupAutomorphism e N hN)
    (invariantSubgroupAutomorphism_subtype_commutes
      e N hN)
    g

omit [N.Normal] in
/-- An equivalence carries a centralizer onto the centralizer of the
transported subgroup. -/
theorem map_equiv_centralizer_eq
    {H : Type*} [Group H]
    (e : G ≃* H) (K : Subgroup G) :
    (Subgroup.centralizer (K : Set G)).map
        e.toMonoidHom =
      Subgroup.centralizer
        (K.map e.toMonoidHom : Set H) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    calc
      e.toMonoidHom k * e.toMonoidHom x =
          e.toMonoidHom (k * x) :=
        (map_mul e.toMonoidHom k x).symm
      _ = e.toMonoidHom (x * k) :=
        congrArg e.toMonoidHom
          (Subgroup.mem_centralizer_iff.mp hx k hk)
      _ = e.toMonoidHom x * e.toMonoidHom k :=
        map_mul e.toMonoidHom x k
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change
      ∀ k : G, k ∈ K →
        k * e.symm y = e.symm y * k
    intro k hk
    apply e.injective
    simpa only [
      map_mul,
      e.apply_symm_apply
    ] using
      (Subgroup.mem_centralizer_iff.mp hy
        (e k) ⟨k, hk, rfl⟩)

omit [N.Normal] in
/-- Preserving a subgroup also preserves its normalizer. -/
theorem map_equiv_normalizer_eq_of_map_eq
    (e : MulAut G) (P : Subgroup G)
    (hP : P.map e.toMonoidHom = P) :
    (Subgroup.normalizer (P : Set G)).map
        e.toMonoidHom =
      Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.map_equiv_normalizer_eq, hP]

omit [N.Normal] in
/-- If an automorphism preserves `K` and `P`, it preserves the fixed-point
subgroup `K ∩ C_G(P)`. -/
theorem map_inf_centralizer_eq_of_map_eq
    (e : MulAut G) (K P : Subgroup G)
    (hK : K.map e.toMonoidHom = K)
    (hP : P.map e.toMonoidHom = P) :
    (K ⊓ Subgroup.centralizer (P : Set G)).map
        e.toMonoidHom =
      K ⊓ Subgroup.centralizer (P : Set G) := by
  rw [
    Subgroup.map_inf _ _ _ e.injective,
    hK,
    map_equiv_centralizer_eq,
    hP
  ]

end GroupTheory
end McKayConjecture
