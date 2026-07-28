/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Sylow

/-!
# Fusion control on Sylow fixed points

Let a finite group `G` act on a type `X`, and let `P` be a Sylow
`p`-subgroup.  If two `P`-fixed points lie in the same `G`-orbit, then they
are already conjugate under `N_G(P)`.

The proof applies Sylow conjugacy inside the stabilizer of the target point.
If `g • x = y`, both `P` and `g • P` are Sylow subgroups of `G_y`.  A
conjugator `h ∈ G_y` from `g • P` back to `P` makes `h * g` normalize `P`,
while it still sends `x` to `y`.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory
namespace Sylow

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {X : Type v} [MulAction G X]

/-- Two `P`-fixed points in the same ambient orbit are related by an element
of the normalizer of `P`. -/
theorem exists_normalizer_smul_eq_of_fixed
    (P : Sylow p G)
    {x y : X}
    (hx : x ∈ MulAction.fixedPoints P X)
    (hy : y ∈ MulAction.fixedPoints P X)
    (hxy : y ∈ MulAction.orbit G x) :
    ∃ n : Subgroup.normalizer (P : Set G),
      (n : G) • x = y := by
  obtain ⟨g, hg⟩ :=
    MulAction.mem_orbit_iff.mp hxy
  have hPx :
      (P : Subgroup G) ≤ MulAction.stabilizer G x := by
    intro a ha
    rw [MulAction.mem_stabilizer_iff]
    exact hx ⟨a, ha⟩
  have hPy :
      (P : Subgroup G) ≤ MulAction.stabilizer G y := by
    intro a ha
    rw [MulAction.mem_stabilizer_iff]
    exact hy ⟨a, ha⟩
  have hgP :
      (g • P : Sylow p G) ≤
        MulAction.stabilizer G y := by
    rw [← hg,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact Subgroup.map_mono hPx
  obtain ⟨h, hh⟩ :=
    MulAction.exists_smul_eq
      (MulAction.stabilizer G y)
      ((g • P).subtype hgP)
      (P.subtype hPy)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def,
    smul_smul] at hh
  have hn :
      (h : G) * g ∈
        Subgroup.normalizer (P : Set G) :=
    Sylow.smul_eq_iff_mem_normalizer.mp
      (Sylow.subtype_injective hh)
  refine ⟨⟨(h : G) * g, hn⟩, ?_⟩
  change ((h : G) * g) • x = y
  rw [mul_smul, hg,
    MulAction.mem_stabilizer_iff.mp h.property]

/-- Orbit-membership form of Sylow fixed-point fusion control. -/
theorem mem_normalizer_orbit_of_fixed
    (P : Sylow p G)
    {x y : X}
    (hx : x ∈ MulAction.fixedPoints P X)
    (hy : y ∈ MulAction.fixedPoints P X)
    (hxy : y ∈ MulAction.orbit G x) :
    y ∈
      MulAction.orbit
        (Subgroup.normalizer (P : Set G)) x := by
  obtain ⟨n, hn⟩ :=
    exists_normalizer_smul_eq_of_fixed P hx hy hxy
  exact ⟨n, hn⟩

/-- On the `P`-fixed locus, ambient `G`-fusion is exactly fusion under the
normalizer of `P`. -/
theorem mem_orbit_iff_mem_normalizer_orbit_of_fixed
    (P : Sylow p G)
    {x y : X}
    (hx : x ∈ MulAction.fixedPoints P X)
    (hy : y ∈ MulAction.fixedPoints P X) :
    y ∈ MulAction.orbit G x ↔
      y ∈
        MulAction.orbit
          (Subgroup.normalizer (P : Set G)) x := by
  constructor
  · exact mem_normalizer_orbit_of_fixed P hx hy
  · exact MulAction.mem_orbit_of_mem_orbit_subgroup

/-- Any intermediate subgroup containing `N_G(P)` controls ambient fusion
between `P`-fixed points. -/
theorem mem_subgroup_orbit_of_fixed_of_normalizer_le
    (P : Sylow p G)
    (H : Subgroup G)
    (hN : Subgroup.normalizer (P : Set G) ≤ H)
    {x y : X}
    (hx : x ∈ MulAction.fixedPoints P X)
    (hy : y ∈ MulAction.fixedPoints P X)
    (hxy : y ∈ MulAction.orbit G x) :
    y ∈ MulAction.orbit H x := by
  obtain ⟨n, hn⟩ :=
    exists_normalizer_smul_eq_of_fixed P hx hy hxy
  exact
    ⟨⟨n, hN n.property⟩,
      by simpa only [MulAction.subgroup_smul_def] using hn⟩

end Sylow
end GroupTheory
end McKayConjecture
