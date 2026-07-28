/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Irreducible
import McKayConjecture.GroupTheory.MinimalNormalAbelian
import McKayConjecture.GroupTheory.MinimalNormalCharacteristic
import McKayConjecture.GroupTheory.NormalConjugation

/-!
# Abelian minimal normal subgroups as irreducible modules

An abelian minimal normal subgroup of prime exponent is naturally a vector
space over `ZMod p`.  Ambient conjugation is linear, and minimal normality
says precisely that this conjugation representation is irreducible.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

open scoped IsMulCommutative

variable {G : Type u} [Group G]
variable {N : Subgroup G}

/-- The canonical `ZMod p`-module structure on the additive form of an
abelian group of exponent `p`. -/
@[instance_reducible]
def primeExponentZModModule
    [IsMulCommutative N]
    (p : ℕ) (hpow : ∀ x : N, x ^ p = 1) :
    Module (ZMod p) (Additive N) := by
  letI : CommGroup N := inferInstance
  exact AddCommGroup.zmodModule (n := p) (by
    intro x
    change x.toMul ^ p = 1
    exact hpow x.toMul)

/-- Conjugation by `G` on an abelian normal subgroup, regarded as a linear
representation over `ZMod p`. -/
def normalConjugationRepresentation
    [IsMulCommutative N]
    (hNnormal : N.Normal) (p : ℕ) [Fact p.Prime]
    [Module (ZMod p) (Additive N)] :
    Representation (ZMod p) G (Additive N) := by
  letI : N.Normal := hNnormal
  exact
    { toFun := fun g ↦
        AddMonoidHom.toZModLinearMap p
          (MulEquiv.toAdditive
            (MulAut.conjNormal (H := N) g)).toAddMonoidHom
      map_one' := by
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        simp only [AddMonoidHom.coe_toZModLinearMap]
        simp [MulEquiv.toAdditive]
      map_mul' := by
        intro g h
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        simp [AddMonoidHom.coe_toZModLinearMap,
          MulEquiv.toAdditive] }

@[simp]
theorem normalConjugationRepresentation_apply
    [IsMulCommutative N]
    (hNnormal : N.Normal) (p : ℕ) [Fact p.Prime]
    [Module (ZMod p) (Additive N)]
    (g : G) (x : Additive N) :
    normalConjugationRepresentation
        (N := N) hNnormal p g x =
      Additive.ofMul
        (@MulAut.conjNormal G _ N hNnormal g x.toMul) :=
  by
    change
      Additive.ofMul
          (@MulAut.conjNormal G _ N hNnormal g x.toMul) =
        Additive.ofMul
          (@MulAut.conjNormal G _ N hNnormal g x.toMul)
    rfl

/-- The kernel of the linear conjugation representation is the ambient
centralizer of the normal subgroup. -/
theorem ker_normalConjugationRepresentation
    [IsMulCommutative N]
    (hNnormal : N.Normal) (p : ℕ) [Fact p.Prime]
    [Module (ZMod p) (Additive N)] :
    (normalConjugationRepresentation
      (N := N) hNnormal p).ker =
        Subgroup.centralizer (N : Set G) := by
  letI : N.Normal := hNnormal
  rw [← ker_conjNormal (N := N)]
  ext g
  constructor
  · intro hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply MulEquiv.ext
    intro x
    have heval :=
      congrArg
        (fun f : Module.End (ZMod p) (Additive N) ↦
          f (Additive.ofMul x)) hg
    apply Additive.ofMul.injective
    exact heval
  · intro hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply LinearMap.ext
    intro x
    have heval :=
      congrArg
        (fun e : MulAut N ↦ e x.toMul) hg
    apply Additive.toMul.injective
    exact heval

namespace IsMinimalNormal

/-- The conjugation representation on a minimal normal subgroup is
irreducible over any field over which its additive group is a module. -/
theorem normalConjugationRepresentation_isIrreducible
    {p : ℕ} [Fact p.Prime]
    [IsMulCommutative N]
    [Module (ZMod p) (Additive N)]
    (hN : IsMinimalNormal N) :
    Representation.IsIrreducible
      (normalConjugationRepresentation
        (N := N) hN.normal p) := by
  letI : N.Normal := hN.normal
  letI : Nontrivial N :=
    N.nontrivial_iff_ne_bot.mpr hN.ne_bot
  let ρ :=
    normalConjugationRepresentation
      (N := N) hN.normal p
  refine
    { exists_pair_ne := ⟨⊥, ⊤, ?_⟩
      eq_bot_or_eq_top := fun S ↦ ?_ }
  · intro h
    obtain ⟨x, hx⟩ :=
      exists_ne (0 : Additive N)
    apply hx
    have hxbot :
        x ∈ (⊥ :
          Subrepresentation ρ) := by
      rw [h]
      exact Submodule.mem_top
    change x = 0 at hxbot
    exact hxbot
  let K : Subgroup N :=
    AddSubgroup.toSubgroup'
      S.toSubmodule.toAddSubgroup
  have hKinv :
      ∀ (g : G) (x : N), x ∈ K →
        MulAut.conjNormal g x ∈ K := by
    intro g x hx
    change
      Additive.ofMul (MulAut.conjNormal g x) ∈
        S.toSubmodule
    have hxS :
        Additive.ofMul x ∈ S.toSubmodule := hx
    exact S.apply_mem_toSubmodule g hxS
  rcases hN.eq_bot_or_top_of_conj_invariant
      K hKinv with hbot | htop
  · left
    apply Subrepresentation.ext
    apply Submodule.ext
    intro x
    constructor
    · intro hx
      have hxK : x.toMul ∈ K := hx
      rw [hbot] at hxK
      exact hxK
    · intro hx
      have hxzero : x = 0 := by
        change x = 0 at hx
        exact hx
      subst x
      exact S.toSubmodule.zero_mem
  · right
    apply Subrepresentation.ext
    apply Submodule.ext
    intro x
    constructor
    · intro hx
      exact Submodule.mem_top
    · intro hx
      have hxK : x.toMul ∈ K := by
        rw [htop]
        exact Subgroup.mem_top x.toMul
      exact hxK

/-- A finite abelian minimal normal subgroup, equipped with its canonical
`ZMod p` structure for any prime divisor `p` of its order, is an irreducible
`G`-module under conjugation. -/
theorem abelianConjugationRepresentation_isIrreducible
    [Finite G] [IsMulCommutative N]
    (hN : IsMinimalNormal N)
    {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Nat.card N) :
    letI : Module (ZMod p) (Additive N) :=
      primeExponentZModModule p (hN.pow_prime_eq_one hp)
    Representation.IsIrreducible
      (normalConjugationRepresentation
        (N := N) hN.normal p) := by
  letI : Module (ZMod p) (Additive N) :=
    primeExponentZModModule p (hN.pow_prime_eq_one hp)
  exact hN.normalConjugationRepresentation_isIrreducible

end IsMinimalNormal

end GroupTheory
end McKayConjecture
