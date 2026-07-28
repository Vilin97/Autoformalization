/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Clifford theory for restricted modules

This file contains the module-theoretic core of Clifford's theorem over an
arbitrary field.  If `H` is normal in `G`, the action of `g : G` is semilinear
for the automorphism of `k[H]` induced by conjugation.  Consequently,
conjugation preserves simple constituents.  For an irreducible
`G`-representation, the conjugates of every nonzero `k[H]`-submodule span the
whole restricted representation, and a finite-dimensional restriction is
semisimple.

The proofs were ported from Yawara Ishida's general-field Clifford development
in the odd-order project.
-/

namespace McKayConjecture.CliffordModule

open Representation
open scoped MonoidAlgebra

variable {G : Type*} [Group G]

/-- The automorphism `h ↦ g * h * g⁻¹` of a normal subgroup. -/
noncomputable def conjNormalMulAut (H : Subgroup G) [H.Normal] (g : G) : H ≃* H :=
  (MulEquiv.subgroupMap (MulAut.conj g) H).trans
    (MulEquiv.subgroupCongr (Subgroup.Normal.conj_smul_eq_self g H))

@[simp]
theorem conjNormalMulAut_apply_coe (H : Subgroup G) [H.Normal] (g : G) (h : H) :
    (conjNormalMulAut H g h : G) = g * (h : G) * g⁻¹ :=
  rfl

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]

section Restriction

variable (ρ : Representation k G V) (H : Subgroup G) [hH : H.Normal]

/-- The restriction of `ρ` to `H`, exposed as a representation so that its
monoid-algebra module is available. -/
abbrev resRep : Representation k H V :=
  ρ.comp H.subtype

omit hH in
@[simp]
theorem resRep_apply (h : H) : resRep ρ H h = ρ (h : G) :=
  rfl

variable {H}

/-- The ring automorphism of `k[H]` induced by conjugation by `g`. -/
noncomputable def conjMonoidAlgRingHom (g : G) : k[H] →+* k[H] :=
  MonoidAlgebra.mapDomainRingHom k (conjNormalMulAut H g).toMonoidHom

theorem conjMonoidAlgRingHom_single (g : G) (h : H) (c : k) :
    conjMonoidAlgRingHom (k := k) (H := H) g (MonoidAlgebra.single h c) =
      MonoidAlgebra.single (conjNormalMulAut H g h) c := by
  simp [conjMonoidAlgRingHom]

theorem conjMonoidAlgRingHom_surjective (g : G) :
    Function.Surjective (conjMonoidAlgRingHom (k := k) (H := H) g) :=
  (MonoidAlgebra.mapDomainRingEquiv k (conjNormalMulAut H g)).surjective

instance conjMonoidAlgRingHom_isSurjective (g : G) :
    RingHomSurjective (conjMonoidAlgRingHom (k := k) (H := H) g) :=
  ⟨conjMonoidAlgRingHom_surjective (k := k) (H := H) g⟩

set_option backward.isDefEq.respectTransparency false in
/-- The action of `g` as a semilinear endomorphism of the restricted module. -/
noncomputable def conjSemilinearEnd (g : G) :
    (resRep ρ H).asModule →ₛₗ[conjMonoidAlgRingHom (k := k) (H := H) g]
      (resRep ρ H).asModule where
  toFun v := (show (resRep ρ H).asModule from ρ g v)
  map_add' v w := by simp
  map_smul' s v := by
    induction s using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
        change ρ g ((x + y) • v) = _
        rw [add_smul, map_add, map_add, add_smul]
        exact congrArg₂ (· + ·) hx hy
    | single h c =>
        have hHh : (conjNormalMulAut H g h : G) = g * (h : G) * g⁻¹ := rfl
        rw [conjMonoidAlgRingHom_single]
        change ρ g (MonoidAlgebra.single h c • v) =
          MonoidAlgebra.single (conjNormalMulAut H g h) c •
            (show (resRep ρ H).asModule from ρ g v)
        rw [Representation.single_smul, Representation.single_smul, resRep_apply,
          resRep_apply, map_smul]
        congr 1
        change ρ g (ρ (h : G) v) = ρ ((conjNormalMulAut H g h : G)) (ρ g v)
        rw [hHh, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group

@[simp]
theorem conjSemilinearEnd_apply (g : G) (v : (resRep ρ H).asModule) :
    conjSemilinearEnd (H := H) ρ g v =
      (show (resRep ρ H).asModule from ρ g v) :=
  rfl

theorem conjSemilinearEnd_bijective (g : G) :
    Function.Bijective (conjSemilinearEnd (H := H) ρ g) :=
  ρ.apply_bijective g

set_option backward.isDefEq.respectTransparency false in
/-- Characterization of membership in the conjugate of a submodule. -/
theorem mem_map_conjSemilinearEnd (g : G)
    (N : Submodule k[H] (resRep ρ H).asModule)
    (w : (resRep ρ H).asModule) :
    w ∈ N.map (conjSemilinearEnd (H := H) ρ g) ↔
      ∃ v ∈ N, (show (resRep ρ H).asModule from ρ g v) = w := by
  simp only [Submodule.mem_map, conjSemilinearEnd_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Conjugation sends a simple constituent of a restriction to a simple
constituent. -/
theorem isSimpleModule_map_conjSemilinearEnd
    (g : G) (N : Submodule k[H] (resRep ρ H).asModule)
    [IsSimpleModule k[H] N] :
    IsSimpleModule k[H]
      (N.map (conjSemilinearEnd (H := H) ρ g) :
        Submodule k[H] (resRep ρ H).asModule) := by
  have hatomN : IsAtom N := IsSimpleModule.isAtom
  have hmap :
      (Submodule.orderIsoMapComapOfBijective
        (conjSemilinearEnd (H := H) ρ g)
        (conjSemilinearEnd_bijective (H := H) ρ g)) N =
        N.map (conjSemilinearEnd (H := H) ρ g) :=
    rfl
  rw [isSimpleModule_iff_isAtom, ← hmap]
  exact (OrderIso.isAtom_iff _ N).mpr hatomN

/-- A nonzero `G`-invariant submodule of the restriction of an irreducible
representation is the whole restricted module. -/
theorem eq_top_of_forall_map_conjSemilinearEnd_le
    [ρ.IsIrreducible] (W : Submodule k[H] (resRep ρ H).asModule) (hW : W ≠ ⊥)
    (hinv : ∀ g : G, W.map (conjSemilinearEnd (H := H) ρ g) ≤ W) :
    W = ⊤ := by
  let Wρ : Subrepresentation ρ :=
    { toSubmodule := W.restrictScalars k
      apply_mem_toSubmodule := fun g v hv => by
        have hv' : v ∈ W := hv
        have : (show (resRep ρ H).asModule from ρ g v) ∈ W :=
          hinv g (Submodule.mem_map_of_mem hv')
        exact this }
  rcases IsSimpleOrder.eq_bot_or_eq_top Wρ with hbot | htop
  · have h0 : W.restrictScalars k = ⊥ :=
      congrArg Subrepresentation.toSubmodule hbot
    refine absurd (eq_bot_iff.mpr fun v hv => ?_) hW
    have hv' : v ∈ W.restrictScalars k := hv
    rw [h0] at hv'
    simpa using hv'
  · have h1 : W.restrictScalars k = ⊤ :=
      congrArg Subrepresentation.toSubmodule htop
    refine eq_top_iff.mpr fun v _ => ?_
    have hv' : v ∈ W.restrictScalars k := h1 ▸ Submodule.mem_top
    exact hv'

/-- Conjugation by the identity fixes every submodule. -/
theorem map_conjSemilinearEnd_one
    (W : Submodule k[H] (resRep ρ H).asModule) :
    W.map (conjSemilinearEnd (H := H) ρ 1) = W := by
  ext v
  rw [mem_map_conjSemilinearEnd]
  refine ⟨?_, fun hv => ⟨v, hv, ?_⟩⟩
  · rintro ⟨w, hw, rfl⟩
    have : (show (resRep ρ H).asModule from ρ (1 : G) w) = w := by
      rw [map_one]
      rfl
    rwa [this]
  · show (show (resRep ρ H).asModule from ρ (1 : G) v) = v
    rw [map_one]
    rfl

/-- Successive conjugations of a submodule agree with conjugation by the
product. -/
theorem map_map_conjSemilinearEnd
    (W : Submodule k[H] (resRep ρ H).asModule) (g₁ g₂ : G) :
    (W.map (conjSemilinearEnd (H := H) ρ g₂)).map
        (conjSemilinearEnd (H := H) ρ g₁) =
      W.map (conjSemilinearEnd (H := H) ρ (g₁ * g₂)) := by
  ext v
  simp only [mem_map_conjSemilinearEnd]
  constructor
  · rintro ⟨u, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, by rw [map_mul]; rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact
      ⟨(show (resRep ρ H).asModule from ρ g₂ w), ⟨w, hw, rfl⟩,
        by rw [map_mul]; rfl⟩

/-- In an irreducible representation, the conjugates of every nonzero
submodule of the restriction span the whole restricted module. -/
theorem iSup_map_conjSemilinearEnd_eq_top [ρ.IsIrreducible]
    (W : Submodule k[H] (resRep ρ H).asModule) (hW : W ≠ ⊥) :
    ⨆ g : G, W.map (conjSemilinearEnd (H := H) ρ g) = ⊤ := by
  refine eq_top_of_forall_map_conjSemilinearEnd_le ρ _ ?_ ?_
  · intro h
    refine hW (le_bot_iff.mp ?_)
    calc
      W = W.map (conjSemilinearEnd (H := H) ρ 1) :=
        (map_conjSemilinearEnd_one ρ W).symm
      _ ≤ ⨆ g : G, W.map (conjSemilinearEnd (H := H) ρ g) :=
        le_iSup (fun g : G => W.map (conjSemilinearEnd (H := H) ρ g)) 1
      _ = ⊥ := h
  · intro g'
    rw [Submodule.map_iSup]
    refine iSup_le fun g => ?_
    rw [map_map_conjSemilinearEnd]
    exact
      le_iSup (fun g => W.map (conjSemilinearEnd (H := H) ρ g)) (g' * g)

set_option backward.isDefEq.respectTransparency false in
/-- If every conjugate of a simple constituent is isomorphic to it, the
restricted module is isotypic of that type. -/
theorem isIsotypicOfType_of_conjugates [ρ.IsIrreducible]
    (W : Submodule k[H] (resRep ρ H).asModule) (hW : W ≠ ⊥)
    [IsSimpleModule k[H] W]
    (hconj : ∀ g : G,
      Nonempty (W ≃ₗ[k[H]] W.map (conjSemilinearEnd (H := H) ρ g))) :
    IsIsotypicOfType k[H] (resRep ρ H).asModule W := by
  intro m _
  haveI : ∀ S :
      Set.range (fun g : G => W.map (conjSemilinearEnd (H := H) ρ g)),
      IsSimpleModule k[H]
        (S : Submodule k[H] (resRep ρ H).asModule) := by
    rintro ⟨_, g, rfl⟩
    exact isSimpleModule_map_conjSemilinearEnd ρ g W
  obtain ⟨S, hS, ⟨e⟩⟩ :=
    Submodule.linearEquiv_of_sSup_eq_top m
      (Set.range (fun g : G =>
        W.map (conjSemilinearEnd (H := H) ρ g)))
      (by
        rw [sSup_range]
        exact iSup_map_conjSemilinearEnd_eq_top ρ W hW)
  obtain ⟨g, rfl⟩ := hS
  exact ⟨e.trans (hconj g).some.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- A finite-dimensional irreducible representation restricts to a
semisimple module over the group algebra of a normal subgroup. -/
theorem isSemisimpleModule_resRep_of_isIrreducible
    [ρ.IsIrreducible] [Module.Finite k V] [Nontrivial V] :
    IsSemisimpleModule k[H] (resRep ρ H).asModule := by
  haveI : Nontrivial (resRep ρ H).asModule := ‹Nontrivial V›
  haveI : IsArtinian k (resRep ρ H).asModule := inferInstance
  haveI : IsArtinian k[H] (resRep ρ H).asModule :=
    isArtinian_of_tower k inferInstance
  obtain ⟨W₀, hW₀atom, -⟩ :=
    (IsAtomic.eq_bot_or_exists_atom_le
      (⊤ : Submodule k[H] (resRep ρ H).asModule)).resolve_left (by simp)
  haveI : IsSimpleModule k[H] W₀ :=
    isSimpleModule_iff_isAtom.mpr hW₀atom
  refine IsSemisimpleModule.of_sSup_simples_eq_top ?_
  rw [eq_top_iff,
    ← iSup_map_conjSemilinearEnd_eq_top ρ W₀ hW₀atom.1]
  exact
    iSup_le fun g =>
      le_sSup (isSimpleModule_map_conjSemilinearEnd ρ g W₀)

end Restriction

end McKayConjecture.CliffordModule
