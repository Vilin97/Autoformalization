/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Sylow

/-!
# Intersecting a Sylow subgroup with a normal subgroup

Let `N ⫳ G` and let `P` be a Sylow `p`-subgroup of the finite group
`G`.  Then `P ∩ N`, viewed inside `N`, is a Sylow `p`-subgroup of `N`.

This file packages that Sylow subgroup and records the ambient and internal
normalizer maps used in reduction arguments.  It also states the exact
Sylow-conjugacy selection result: for any chosen Sylow subgroup `Q` of a
subgroup `N`, some conjugate of an ambient Sylow subgroup has intersection
with `N` equal to `Q`.
-/

noncomputable section

open scoped Pointwise

universe u

namespace McKayConjecture.GroupTheory

variable {G : Type u} [Group G] {p : ℕ}

/-! ## Conjugation and subgroup restriction -/

/-- Restricting a conjugated subgroup to a normal subgroup agrees with
conjugating the restricted subgroup by the induced automorphism. -/
theorem conjNormal_smul_comap_subtype
    (N : Subgroup G) [N.Normal] (g : G) (H : Subgroup G) :
    (MulAut.conjNormal g : MulAut N) • H.comap N.subtype =
      (MulAut.conj g • H).comap N.subtype := by
  ext n
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Subgroup.mem_comap, Subgroup.mem_comap,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  change
    (((MulAut.conjNormal g).symm n : N) : G) ∈ H ↔
      (MulAut.conj g).symm (n : G) ∈ H
  rw [MulAut.conjNormal_symm_apply]
  rfl

/-! ## Selecting an ambient Sylow by its intersection -/

/-- Any selected Sylow subgroup of `N` occurs as the intersection with
`N` of a conjugate of any fixed ambient Sylow subgroup.

Normality of `N` is not needed for this selection statement. -/
theorem exists_smul_comap_subtype_eq
    [Fact p.Prime] [Finite (Sylow p G)]
    (N : Subgroup G) (P : Sylow p G) (Q : Sylow p N) :
    ∃ g : G,
      ((g • P : Sylow p G) : Subgroup G).comap N.subtype =
        (Q : Subgroup N) := by
  obtain ⟨R, hR⟩ := Q.exists_comap_subtype_eq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P R
  exact ⟨g, by rw [hg]; exact hR⟩

/-- Ambient form of `exists_smul_comap_subtype_eq`: after mapping back
into `G`, the selected intersection is `(g • P) ∩ N`. -/
theorem exists_smul_inf_eq_map
    [Fact p.Prime] [Finite (Sylow p G)]
    (N : Subgroup G) (P : Sylow p G) (Q : Sylow p N) :
    ∃ g : G,
      ((g • P : Sylow p G) : Subgroup G) ⊓ N =
        (Q : Subgroup N).map N.subtype := by
  obtain ⟨g, hg⟩ :=
    exists_smul_comap_subtype_eq N P Q
  refine ⟨g, ?_⟩
  rw [← hg, Subgroup.comap_subtype,
    Subgroup.subgroupOf_map_subtype]

/-! ## The canonical Sylow intersection -/

variable [Finite G] [Fact p.Prime]
variable (N : Subgroup G) [N.Normal]
variable (P : Sylow p G)

/-- There exists a Sylow subgroup of `N` whose underlying subgroup is the
preimage of `P`, equivalently `P ∩ N`. -/
theorem exists_sylow_eq_comap :
    ∃ Q : Sylow p N,
      (Q : Subgroup N) =
        (P : Subgroup G).comap N.subtype := by
  let Q₀ : Sylow p N := Sylow.nonempty.some
  obtain ⟨g, hg⟩ :=
    exists_smul_comap_subtype_eq N P Q₀
  let Q : Sylow p N :=
    (MulAut.conjNormal g : MulAut N).symm • Q₀
  refine ⟨Q, ?_⟩
  have hconj :
      (MulAut.conjNormal g : MulAut N) •
          (P : Subgroup G).comap N.subtype =
        ((g • P : Sylow p G) : Subgroup G).comap N.subtype :=
    conjNormal_smul_comap_subtype N g (P : Subgroup G)
  change
    ((MulAut.conjNormal g : MulAut N).symm • Q₀ : Sylow p N) =
      (P : Subgroup G).comap N.subtype
  rw [Sylow.pointwise_smul_def, ← hg, ← hconj,
    ← mul_smul]
  rw [← MulAut.inv_def]
  simp

/-- The canonical Sylow `p`-subgroup `P ∩ N` of `N`. -/
def sylowNormalIntersection : Sylow p N :=
  Classical.choose (exists_sylow_eq_comap N P)

@[simp]
theorem coe_sylowNormalIntersection :
    (sylowNormalIntersection N P : Subgroup N) =
      (P : Subgroup G).comap N.subtype :=
  Classical.choose_spec (exists_sylow_eq_comap N P)

@[simp]
theorem mem_sylowNormalIntersection (n : N) :
    n ∈ sylowNormalIntersection N P ↔ (n : G) ∈ P := by
  change n ∈ (sylowNormalIntersection N P : Subgroup N) ↔ _
  rw [coe_sylowNormalIntersection]
  rfl

/-- Mapping the canonical Sylow subgroup of `N` into `G` gives the
ambient intersection `P ∩ N`. -/
@[simp]
theorem map_sylowNormalIntersection :
    (sylowNormalIntersection N P : Subgroup N).map N.subtype =
      (P : Subgroup G) ⊓ N := by
  rw [coe_sylowNormalIntersection,
    Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype]

/-- The subgroup `P ∩ N`, viewed as a subgroup of `N`, is exactly the
canonical Sylow intersection. -/
@[simp]
theorem subgroupOf_inf_eq_sylowNormalIntersection :
    ((P : Subgroup G) ⊓ N).subgroupOf N =
      (sylowNormalIntersection N P : Subgroup N) := by
  apply Subgroup.ext
  intro n
  simp [coe_sylowNormalIntersection]

/-! ## Normalizer containment and restriction -/

omit [Finite G] [Fact (Nat.Prime p)] in
/-- Every element normalizing `H` also normalizes `H ∩ N`, because `N`
is normal in `G`. -/
theorem normalizer_le_normalizer_inf (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer
        ((H ⊓ N : Subgroup G) : Set G) := by
  have hN :
      Subgroup.normalizer (H : Set G) ≤
        Subgroup.normalizer (N : Set G) :=
    Subgroup.le_normalizer_of_normal
  exact
    (le_inf le_rfl hN).trans
      Subgroup.inf_normalizer_le_normalizer_inf

/-- Inclusion of the ambient normalizer of `P` into the ambient
normalizer of `P ∩ N`. -/
def ambientNormalizerHom :
    Subgroup.normalizer (P : Set G) →*
      Subgroup.normalizer
        (((P : Subgroup G) ⊓ N : Subgroup G) : Set G) :=
  Subgroup.inclusion
    (normalizer_le_normalizer_inf N (P : Subgroup G))

omit [Finite G] [Fact (Nat.Prime p)] in
@[simp]
theorem ambientNormalizerHom_apply_coe
    (x : Subgroup.normalizer (P : Set G)) :
    ((ambientNormalizerHom N P x :
        Subgroup.normalizer
          (((P : Subgroup G) ⊓ N : Subgroup G) : Set G)) : G) =
      x :=
  rfl

omit [Finite G] [Fact (Nat.Prime p)] in
theorem ambientNormalizerHom_injective :
    Function.Injective (ambientNormalizerHom N P) :=
  Subgroup.inclusion_injective
    (normalizer_le_normalizer_inf N (P : Subgroup G))

/-- Restricting the ambient normalizer of `P ∩ N` to `N` gives exactly
the internal normalizer of the canonical Sylow intersection. -/
theorem subgroupOf_ambientNormalizer_eq_internal :
    (Subgroup.normalizer
        (((P : Subgroup G) ⊓ N : Subgroup G) : Set G)).subgroupOf N =
      Subgroup.normalizer
        ((sylowNormalIntersection N P : Subgroup N) : Set N) := by
  calc
    (Subgroup.normalizer
        (((P : Subgroup G) ⊓ N : Subgroup G) : Set G)).subgroupOf N =
        Subgroup.normalizer
          ((((P : Subgroup G) ⊓ N).subgroupOf N :
            Subgroup N) : Set N) :=
      Subgroup.subgroupOf_normalizer_eq inf_le_right
    _ = Subgroup.normalizer
          ((sylowNormalIntersection N P : Subgroup N) : Set N) := by
      rw [subgroupOf_inf_eq_sylowNormalIntersection]

/-- Canonical equivalence between the ambient intersection normalizer
restricted to `N` and the normalizer computed internally in `N`. -/
def ambientInternalNormalizerEquiv :
    (Subgroup.normalizer
        (((P : Subgroup G) ⊓ N : Subgroup G) : Set G)).subgroupOf N ≃*
      Subgroup.normalizer
        ((sylowNormalIntersection N P : Subgroup N) : Set N) :=
  MulEquiv.subgroupCongr
    (subgroupOf_ambientNormalizer_eq_internal N P)

@[simp]
theorem ambientInternalNormalizerEquiv_apply_coe
    (x :
      (Subgroup.normalizer
        (((P : Subgroup G) ⊓ N : Subgroup G) : Set G)).subgroupOf N) :
    ((ambientInternalNormalizerEquiv N P x :
        Subgroup.normalizer
          ((sylowNormalIntersection N P : Subgroup N) : Set N)) : N) =
      x :=
  rfl

/-- The part of `N_G(P)` lying in `N` is contained in the internal
normalizer of `P ∩ N`. -/
theorem restrictedNormalizer_le_internal :
    (Subgroup.normalizer (P : Set G)).subgroupOf N ≤
      Subgroup.normalizer
        ((sylowNormalIntersection N P : Subgroup N) : Set N) := by
  rw [← subgroupOf_ambientNormalizer_eq_internal N P]
  exact Subgroup.subgroupOf_mono N
    (normalizer_le_normalizer_inf N (P : Subgroup G))

/-- Restriction homomorphism
`N_G(P) ∩ N → N_N(P ∩ N)`. -/
def restrictedNormalizerHom :
    (Subgroup.normalizer (P : Set G)).subgroupOf N →*
      Subgroup.normalizer
        ((sylowNormalIntersection N P : Subgroup N) : Set N) :=
  Subgroup.inclusion (restrictedNormalizer_le_internal N P)

@[simp]
theorem restrictedNormalizerHom_apply_coe
    (x : (Subgroup.normalizer (P : Set G)).subgroupOf N) :
    ((restrictedNormalizerHom N P x :
        Subgroup.normalizer
          ((sylowNormalIntersection N P : Subgroup N) : Set N)) : N) =
      x :=
  rfl

theorem restrictedNormalizerHom_injective :
    Function.Injective (restrictedNormalizerHom N P) :=
  Subgroup.inclusion_injective
    (restrictedNormalizer_le_internal N P)

end McKayConjecture.GroupTheory
