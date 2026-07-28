/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Conjugation on a normal subgroup

The kernel of the conjugation action on a normal subgroup `N` is its ambient
centralizer.  Thus the first isomorphism theorem identifies
`G / C_G(N)` with the subgroup of `Aut(N)` induced by `G`.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G]
variable {N : Subgroup G} [N.Normal]

/-- The kernel of the ambient conjugation action on a normal subgroup is its
centralizer. -/
theorem ker_conjNormal :
    (MulAut.conjNormal (H := N)).ker =
      Subgroup.centralizer (N : Set G) := by
  ext g
  constructor
  · intro hg n hn
    have heval :=
      congrArg
        (fun e : MulAut N ↦
          e (⟨n, hn⟩ : N)) hg
    have hconj : g * n * g⁻¹ = n := by
      exact congrArg Subtype.val heval
    exact ((mul_inv_eq_iff_eq_mul).mp hconj).symm
  · intro hg
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    change g * (n : G) * g⁻¹ = n
    calc
      g * (n : G) * g⁻¹ =
          (n : G) * g * g⁻¹ := by
        rw [hg n n.property]
      _ = n := by simp

omit [N.Normal] in
/-- The part of the ambient centralizer lying inside `N` is exactly the
center of `N`. -/
theorem centralizer_subgroupOf_eq_center :
    (Subgroup.centralizer (N : Set G)).subgroupOf N =
      Subgroup.center N := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact hx y y.property
  · intro hx y hy
    let yN : N := ⟨y, hy⟩
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hx yN)

omit [N.Normal] in
/-- If `N` is centerless, it is disjoint from its ambient centralizer. -/
theorem disjoint_centralizer_of_center_eq_bot
    (hcenter : Subgroup.center N = ⊥) :
    Disjoint N (Subgroup.centralizer (N : Set G)) := by
  rw [disjoint_iff, inf_comm,
    ← Subgroup.subgroupOf_map_subtype,
    centralizer_subgroupOf_eq_center,
    hcenter, Subgroup.map_bot]

/-- The group induced by conjugation on `N`. -/
abbrev ConjugationImage (N : Subgroup G) [N.Normal] :=
  (MulAut.conjNormal (H := N)).range

/-- First isomorphism theorem for the conjugation action:
`G / C_G(N) ≃ im(G → Aut(N))`. -/
def quotientCentralizerEquivConjugationImage :
    G ⧸ Subgroup.centralizer (N : Set G) ≃*
      ConjugationImage N :=
  (QuotientGroup.quotientMulEquivOfEq
      (ker_conjNormal (N := N)).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (MulAut.conjNormal (H := N)))

end GroupTheory
end McKayConjecture
