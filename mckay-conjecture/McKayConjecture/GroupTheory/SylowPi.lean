/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Sylow

/-!
# Sylow subgroups of finite indexed products

For a finite family of groups, the coordinatewise product of Sylow
`p`-subgroups is Sylow in the dependent product.  We also identify its
normalizer coordinatewise and package that identification as a canonical
multiplicative equivalence.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory

namespace Subgroup

variable {ι : Type u} {G : ι → Type v} [∀ i, Group (G i)]

/-- The subgroup defined by a coordinatewise membership condition is
canonically isomorphic to the dependent product of the subgroup types. -/
def piMulEquiv (H : ∀ i, Subgroup (G i)) :
    Subgroup.pi Set.univ H ≃* ∀ i, H i where
  toFun x i :=
    ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  invFun x :=
    ⟨fun i ↦ x i, fun i _ ↦ (x i).2⟩
  left_inv _x :=
    Subtype.ext (funext fun _ ↦ rfl)
  right_inv _x :=
    funext fun _i ↦ Subtype.ext rfl
  map_mul' _ _ :=
    rfl

@[simp]
theorem piMulEquiv_apply_coe
    (H : ∀ i, Subgroup (G i))
    (x : Subgroup.pi Set.univ H) (i : ι) :
    ((piMulEquiv H x) i : G i) = x.1 i :=
  rfl

@[simp]
theorem piMulEquiv_symm_apply_coe
    (H : ∀ i, Subgroup (G i))
    (x : ∀ i, H i) (i : ι) :
    ((piMulEquiv H).symm x).1 i = x i :=
  rfl

/-- A finite dependent product of `p`-groups is a `p`-group. -/
theorem isPGroup_pi
    [Finite ι] {p : ℕ}
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsPGroup p (H i)) :
    IsPGroup p (Subgroup.pi Set.univ H) := by
  letI : Fintype ι := Fintype.ofFinite ι
  have hprod : IsPGroup p (∀ i, H i) := by
    intro x
    choose k hk using fun i ↦ hH i (x i)
    refine ⟨∑ i, k i, ?_⟩
    funext i
    have hki : k i ≤ ∑ j, k j :=
      Finset.single_le_sum
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    change (x i) ^ (p ^ (∑ j, k j)) = 1
    rw [← Nat.add_sub_of_le hki, pow_add, pow_mul,
      hk i, one_pow]
  exact hprod.of_equiv (piMulEquiv H).symm

end Subgroup

namespace Sylow

variable {ι : Type u} {G : ι → Type v} [∀ i, Group (G i)]
variable {p : ℕ}

/-- The coordinatewise product of a finite family of Sylow `p`-subgroups. -/
def pi [Finite ι] (P : ∀ i, Sylow p (G i)) :
    Sylow p (∀ i, G i) where
  toSubgroup :=
    Subgroup.pi Set.univ fun i ↦ (P i : Subgroup (G i))
  isPGroup' :=
    Subgroup.isPGroup_pi
      (fun i ↦ (P i : Subgroup (G i)))
      (fun i ↦ (P i).isPGroup')
  is_maximal' := by
    classical
    intro Q hQ hPQ
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_pi]
      intro i _
      let e : (∀ j, G j) →* G i :=
        Pi.evalMonoidHom G i
      have hmapP :
          (P i : Subgroup (G i)) ≤ Q.map e := by
        intro y hy
        refine ⟨Pi.mulSingle i y, hPQ ?_, ?_⟩
        · rw [Subgroup.mulSingle_mem_pi]
          exact fun _ ↦ hy
        · simp [e]
      have hmapEq :
          Q.map e = (P i : Subgroup (G i)) :=
        (P i).is_maximal' (hQ.map e) hmapP
      rw [← hmapEq]
      exact ⟨x, hx, rfl⟩
    · exact hPQ

@[simp, norm_cast]
theorem coe_pi [Finite ι] (P : ∀ i, Sylow p (G i)) :
    (pi P : Subgroup (∀ i, G i)) =
      Subgroup.pi Set.univ
        (fun i ↦ (P i : Subgroup (G i))) :=
  rfl

end Sylow

namespace Subgroup

variable {ι : Type u} {G : ι → Type v} [∀ i, Group (G i)]

/-- The normalizer of a coordinatewise product subgroup is the
coordinatewise product of the factor normalizers. -/
theorem normalizer_pi
    (H : ∀ i, Subgroup (G i)) :
    _root_.Subgroup.normalizer
        (Subgroup.pi Set.univ H :
          Set (∀ i, G i)) =
      Subgroup.pi Set.univ
        (fun i ↦
          _root_.Subgroup.normalizer
            (H i : Set (G i))) := by
  classical
  ext x
  constructor
  · intro hx
    rw [_root_.Subgroup.mem_pi]
    intro i _
    rw [_root_.Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hsingle :
          Pi.mulSingle i y ∈
            Subgroup.pi Set.univ H := by
        rw [_root_.Subgroup.mulSingle_mem_pi]
        exact fun _ ↦ hy
      have hconj :=
        ((_root_.Subgroup.mem_normalizer_iff.mp hx)
          (Pi.mulSingle i y)).mp hsingle
      have hcoord :=
        ((_root_.Subgroup.mem_pi Set.univ).mp hconj) i
          (Set.mem_univ i)
      simpa using hcoord
    · intro hy
      have hconj :
          x * Pi.mulSingle i y * x⁻¹ ∈
            Subgroup.pi Set.univ H := by
        rw [_root_.Subgroup.mem_pi]
        intro j _
        by_cases hji : j = i
        · subst j
          simpa using hy
        · simp [Pi.mulSingle, hji]
      have hsingle :=
        ((_root_.Subgroup.mem_normalizer_iff.mp hx)
          (Pi.mulSingle i y)).mpr hconj
      rw [_root_.Subgroup.mulSingle_mem_pi] at hsingle
      exact hsingle (Set.mem_univ i)
  · intro hx
    rw [_root_.Subgroup.mem_normalizer_iff]
    intro y
    rw [_root_.Subgroup.mem_pi] at hx ⊢
    constructor
    · intro hy i _
      exact
        (_root_.Subgroup.mem_normalizer_iff.mp
          (hx i (Set.mem_univ i)) (y i)).mp
          (hy i (Set.mem_univ i))
    · intro hy i _
      exact
        (_root_.Subgroup.mem_normalizer_iff.mp
          (hx i (Set.mem_univ i)) (y i)).mpr
          (hy i (Set.mem_univ i))

/-- The canonical coordinatewise isomorphism between the normalizer of a
product subgroup and the product of the factor normalizers. -/
def normalizerPiMulEquiv
    (H : ∀ i, Subgroup (G i)) :
    _root_.Subgroup.normalizer
        (Subgroup.pi Set.univ H :
          Set (∀ i, G i)) ≃*
      ∀ i,
        _root_.Subgroup.normalizer
          (H i : Set (G i)) :=
  (MulEquiv.subgroupCongr (normalizer_pi H)).trans
    (piMulEquiv fun i ↦
      _root_.Subgroup.normalizer
        (H i : Set (G i)))

@[simp]
theorem normalizerPiMulEquiv_apply_coe
    (H : ∀ i, Subgroup (G i))
    (x :
      _root_.Subgroup.normalizer
        (Subgroup.pi Set.univ H :
          Set (∀ i, G i)))
    (i : ι) :
    ((normalizerPiMulEquiv H x) i : G i) =
      x.1 i :=
  rfl

@[simp]
theorem normalizerPiMulEquiv_symm_apply_coe
    (H : ∀ i, Subgroup (G i))
    (x : ∀ i,
      _root_.Subgroup.normalizer
        (H i : Set (G i)))
    (i : ι) :
    ((normalizerPiMulEquiv H).symm x).1 i =
      x i :=
  rfl

end Subgroup

end GroupTheory
end McKayConjecture
