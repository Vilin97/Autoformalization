/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import McKayConjecture.Character.Extension
import McKayConjecture.Character.Linear
import McKayConjecture.Character.Twist

/-!
# Extensions differ by a linear character

This file ports the representation-theoretic argument from Yawara Ishida's
`OddOrder.GroupTheory.RepresentationTheory.ExtensionLinearTwist` to the
project's `IrreducibleCharacter` and `IsExtensionAlong` APIs.

Let `H ⫳ K`, and suppose two irreducible characters of `K` both extend the
same irreducible character of `H`.  After identifying their restrictions,
Schur's lemma shows that the pointwise quotient of the two ambient
representations is scalar.  Those scalars form a linear character of `K`,
trivial on `H`, and twisting the first extension by it gives the second.

## Main result

* `IrreducibleCharacter.IsExtensionAlong.exists_eq_twist`:
  two extensions of the same irreducible normal-subgroup character differ by
  a linear character trivial on the subgroup.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Corollary 6.17.
* Peterfalvi, §3 (1.7)(b).
-/

noncomputable section

open CategoryTheory
open Module (finrank)

universe u

namespace McKayConjecture
namespace IrreducibleCharacter

variable {K : Type u} [Group K]
variable {H : Subgroup K} [hH : H.Normal]

/-! ### Transporting an ambient representation -/

/-- Transport a complex representation along a linear equivalence of its
carrier. -/
def transportRepresentation
    {W X : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ K W) (e : W ≃ₗ[ℂ] X) :
    Representation ℂ K X :=
  ((e.conjRingEquiv :
      Module.End ℂ W ≃+* Module.End ℂ X).toRingHom.toMonoidHom).comp ρ

@[simp]
theorem transportRepresentation_apply
    {W X : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ K W) (e : W ≃ₗ[ℂ] X) (g : K) :
    transportRepresentation ρ e g = e.conj (ρ g) :=
  rfl

/-- Transporting a finite-dimensional representation preserves its
character. -/
theorem transportRepresentation_character
    {W X : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) (e : W ≃ₗ[ℂ] X) :
    (transportRepresentation ρ e).character = ρ.character := by
  funext g
  change LinearMap.trace ℂ X (e.conj (ρ g)) =
    LinearMap.trace ℂ W (ρ g)
  exact LinearMap.trace_conj' (ρ g) e

/-! ### Equality with an irreducible character -/

/-- A finite-dimensional representation with the same character as an
irreducible representation is equivalent to it.

This is the character-completeness lemma used in the Apache reference.  The
second representation is not assumed irreducible.
-/
theorem Representation.nonempty_equiv_of_character_eq_irreducible
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (σ : Representation ℂ G W)
    (hchar : σ.character = ρ.character) :
    Nonempty (ρ.Equiv σ) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hρσ :=
    Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
  have hρρ :=
    Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  rw [hchar] at hρσ
  have hEnd : finrank ℂ (Representation.IntertwiningMap ρ ρ) = 1 := by
    have hbij : Function.Bijective
        (Algebra.linearMap ℂ (Representation.IntertwiningMap ρ ρ)) :=
      Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
        (ρ := ρ)
    rw [← (LinearEquiv.ofBijective _ hbij).finrank_eq,
      Module.finrank_self]
  have hHom : finrank ℂ (Representation.IntertwiningMap ρ σ) = 1 := by
    have hcast :
        (finrank ℂ (Representation.IntertwiningMap ρ σ) : ℂ) =
          (finrank ℂ (Representation.IntertwiningMap ρ ρ) : ℂ) :=
      hρσ.symm.trans hρρ
    have h :
        finrank ℂ (Representation.IntertwiningMap ρ σ) =
          finrank ℂ (Representation.IntertwiningMap ρ ρ) := by
      exact_mod_cast hcast
    rw [h, hEnd]
  haveI : Nontrivial (Representation.IntertwiningMap ρ σ) :=
    Module.nontrivial_of_finrank_pos (by rw [hHom]; norm_num)
  obtain ⟨T, hT⟩ :=
    exists_ne (0 : Representation.IntertwiningMap ρ σ)
  have hker : T.ker = ⊥ := by
    rcases (show IsSimpleOrder (Subrepresentation ρ) from
      ‹Representation.IsIrreducible ρ›).eq_bot_or_eq_top T.ker with h | h
    · exact h
    · exfalso
      apply hT
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      have hv : v ∈ T.ker := by
        have hsub :
            T.ker.toSubmodule =
              (⊤ : Subrepresentation ρ).toSubmodule := by
          rw [h]
        have : v ∈ T.ker.toSubmodule := by
          rw [hsub]
          exact Submodule.mem_top
        exact this
      rw [Representation.IntertwiningMap.mem_ker] at hv
      simpa using hv
  have hinjective : Function.Injective T.toLinearMap := by
    rw [← LinearMap.ker_eq_bot]
    have hsub :
        T.ker.toSubmodule = LinearMap.ker T.toLinearMap := rfl
    rw [← hsub, hker]
    rfl
  have hdim : finrank ℂ V = finrank ℂ W := by
    have h := congrFun hchar 1
    rw [Representation.char_one, Representation.char_one] at h
    exact_mod_cast h.symm
  have hsurjective : Function.Surjective T.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      hinjective
  exact
    ⟨Representation.IntertwiningMap.ofBijective T
      ⟨hinjective, hsurjective⟩⟩

/-- Irreducibility transports along an equivalence of complex
representations. -/
theorem Representation.IsIrreducible.of_equiv
    {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    [Representation.IsIrreducible ρ] (φ : ρ.Equiv σ) :
    Representation.IsIrreducible σ := by
  have hbij : Function.Bijective
      (Representation.IntertwiningMap.equivLinearMapAsModule
        ρ σ φ.toIntertwiningMap) :=
    φ.toLinearEquiv.bijective
  let L := LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule
      ρ σ φ.toIntertwiningMap) hbij
  haveI := (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp
    ‹Representation.IsIrreducible ρ›
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact IsSimpleModule.congr L.symm

/-! ### Classification of extensions -/

namespace IsExtensionAlong

variable {χ : IrreducibleCharacter H}
variable {ψ₁ ψ₂ : IrreducibleCharacter K}

/-- Two irreducible extensions of the same normal-subgroup character differ
by a linear character that is trivial on the subgroup. -/
theorem exists_eq_twist
    [Finite K]
    (hψ₁ : IsExtensionAlong H.subtype χ ψ₁)
    (hψ₂ : IsExtensionAlong H.subtype χ ψ₂) :
    ∃ lam : K →* ℂˣ,
      (∀ h : H, lam (h : K) = 1) ∧
        ψ₂ = IrreducibleCharacter.twist lam ψ₁ := by
  classical
  let ρθ : Representation ℂ H χ.realization :=
    χ.realization.ρ
  let ρ₁ : Representation ℂ K ψ₁.realization :=
    ψ₁.realization.ρ
  let ρ₂ : Representation ℂ K ψ₂.realization :=
    ψ₂.realization.ρ
  letI : Representation.IsIrreducible ρθ :=
    CliffordRestriction.isIrreducible_of_simple χ.realization
  let res₁ : Representation ℂ H ψ₁.realization :=
    ρ₁.comp H.subtype
  let res₂ : Representation ℂ H ψ₂.realization :=
    ρ₂.comp H.subtype
  have hchar₁ : res₁.character = ρθ.character := by
    funext h
    calc
      res₁.character h =
          ψ₁.realization.character (h : K) := rfl
      _ = ψ₁.values (h : K) :=
        congrFun ψ₁.realization_character (h : K)
      _ = χ.values h := hψ₁ h
      _ = χ.realization.character h :=
        (congrFun χ.realization_character h).symm
      _ = ρθ.character h := rfl
  have hchar₂ : res₂.character = ρθ.character := by
    funext h
    calc
      res₂.character h =
          ψ₂.realization.character (h : K) := rfl
      _ = ψ₂.values (h : K) :=
        congrFun ψ₂.realization_character (h : K)
      _ = χ.values h := hψ₂ h
      _ = χ.realization.character h :=
        (congrFun χ.realization_character h).symm
      _ = ρθ.character h := rfl
  obtain ⟨Φ₁⟩ :=
    Representation.nonempty_equiv_of_character_eq_irreducible
      ρθ res₁ hchar₁
  obtain ⟨Φ₂⟩ :=
    Representation.nonempty_equiv_of_character_eq_irreducible
      ρθ res₂ hchar₂
  letI : Representation.IsIrreducible res₁ :=
    Representation.IsIrreducible.of_equiv Φ₁
  let T : res₂.Equiv res₁ := Φ₂.symm.trans Φ₁
  let ρ₂' : Representation ℂ K ψ₁.realization :=
    transportRepresentation ρ₂ T.toLinearEquiv
  have hchar₂' :
      ρ₂'.character = ρ₂.character :=
    transportRepresentation_character
      ρ₂ T.toLinearEquiv
  have hagree : ∀ h : H,
      ρ₂' (h : K) = ρ₁ (h : K) := by
    intro h
    rw [show ρ₂' (h : K) =
      T.toLinearEquiv.conj (ρ₂ (h : K)) from rfl]
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply]
    have hintertwine := T.isIntertwining' h
    have hv :=
      LinearMap.congr_fun hintertwine (T.toLinearEquiv.symm v)
    simp only [LinearMap.comp_apply] at hv
    calc
      T.toLinearEquiv
          (ρ₂ (h : K)
            (T.toLinearEquiv.symm v)) =
        res₁ h
          (T.toLinearMap (T.toLinearEquiv.symm v)) := hv
      _ = ρ₁ (h : K) v := by
        rw [show T.toLinearMap (T.toLinearEquiv.symm v) =
          T.toLinearEquiv (T.toLinearEquiv.symm v) from rfl,
          T.toLinearEquiv.apply_symm_apply]
        rfl
  have hagreeUnits : ∀ h : H,
      ρ₂'.asGroupHom (h : K) =
        ρ₁.asGroupHom (h : K) := fun h =>
    Units.ext (by
      rw [Representation.asGroupHom_apply,
        Representation.asGroupHom_apply, hagree h])
  have hcomm : ∀ (y : K) (h : H),
      ρ₁.asGroupHom (h : K) *
          (ρ₂'.asGroupHom y *
            (ρ₁.asGroupHom y)⁻¹) =
        (ρ₂'.asGroupHom y *
            (ρ₁.asGroupHom y)⁻¹) *
          ρ₁.asGroupHom (h : K) := by
    intro y h
    have hmem : y⁻¹ * (h : K) * y ∈ H := by
      simpa using hH.conj_mem (h : K) h.property y⁻¹
    have hconj₁ :
        (ρ₁.asGroupHom y)⁻¹ *
            ρ₁.asGroupHom (h : K) *
            ρ₁.asGroupHom y =
          ρ₁.asGroupHom
            (y⁻¹ * (h : K) * y) := by
      rw [← map_inv, ← map_mul, ← map_mul]
    have hconj₂ :
        ρ₂'.asGroupHom y *
            ρ₂'.asGroupHom (y⁻¹ * (h : K) * y) =
          ρ₂'.asGroupHom (h : K) * ρ₂'.asGroupHom y := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    have hagreeConj :
        ρ₂'.asGroupHom (y⁻¹ * (h : K) * y) =
          ρ₁.asGroupHom
            (y⁻¹ * (h : K) * y) :=
      hagreeUnits ⟨y⁻¹ * (h : K) * y, hmem⟩
    calc
      ρ₁.asGroupHom (h : K) *
          (ρ₂'.asGroupHom y *
            (ρ₁.asGroupHom y)⁻¹) =
        ρ₁.asGroupHom (h : K) *
            ρ₂'.asGroupHom y *
            (ρ₁.asGroupHom y)⁻¹ := by
          group
      _ = ρ₂'.asGroupHom (h : K) *
            ρ₂'.asGroupHom y *
            (ρ₁.asGroupHom y)⁻¹ := by
          rw [hagreeUnits h]
      _ = ρ₂'.asGroupHom y *
            ρ₂'.asGroupHom (y⁻¹ * (h : K) * y) *
            (ρ₁.asGroupHom y)⁻¹ := by
          rw [hconj₂]
      _ = ρ₂'.asGroupHom y *
            ρ₁.asGroupHom
              (y⁻¹ * (h : K) * y) *
            (ρ₁.asGroupHom y)⁻¹ := by
          rw [hagreeConj]
      _ = ρ₂'.asGroupHom y *
            ((ρ₁.asGroupHom y)⁻¹ *
              ρ₁.asGroupHom (h : K) *
              ρ₁.asGroupHom y) *
            (ρ₁.asGroupHom y)⁻¹ := by
          rw [hconj₁]
      _ = (ρ₂'.asGroupHom y *
            (ρ₁.asGroupHom y)⁻¹) *
          ρ₁.asGroupHom (h : K) := by
          group
  have hSchur : ∀ y : K, ∃ c : ℂ,
      ((ρ₂'.asGroupHom y *
          (ρ₁.asGroupHom y)⁻¹ :
            (Module.End ℂ ψ₁.realization)ˣ) :
          Module.End ℂ ψ₁.realization) =
        c • LinearMap.id := by
    intro y
    refine RepresentationTheory.exists_smul_id_of_forall_mul_comm
      res₁ _ (fun h => ?_)
    have h := congrArg Units.val (hcomm y h)
    simpa only [res₁, MonoidHom.comp_apply, Subgroup.subtype_apply,
      Units.val_mul, Representation.asGroupHom_apply] using h
  choose c hc using hSchur
  haveI : Nontrivial ψ₁.realization :=
    CliffordRestriction.nontrivial_of_simple ψ₁.realization
  have scalar_injective : ∀ {a b : ℂ},
      (a • LinearMap.id :
          Module.End ℂ ψ₁.realization) =
        b • LinearMap.id → a = b := by
    intro a b hab
    obtain ⟨v, hv⟩ := exists_ne (0 : ψ₁.realization)
    have h := LinearMap.congr_fun hab v
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at h
    exact smul_left_injective ℂ hv h
  haveI : Nontrivial (Module.End ℂ ψ₁.realization) :=
    ⟨1, 0, fun h => by
      obtain ⟨v, hv⟩ := exists_ne (0 : ψ₁.realization)
      exact hv (by simpa using LinearMap.congr_fun h v)⟩
  have c_ne_zero : ∀ y : K, c y ≠ 0 := by
    intro y hy
    have h := hc y
    rw [hy, zero_smul] at h
    exact Units.ne_zero
      (ρ₂'.asGroupHom y *
        (ρ₁.asGroupHom y)⁻¹) h
  have scalar_central : ∀ (y : K)
      (x : (Module.End ℂ ψ₁.realization)ˣ),
      (ρ₂'.asGroupHom y *
          (ρ₁.asGroupHom y)⁻¹) * x =
        x * (ρ₂'.asGroupHom y *
          (ρ₁.asGroupHom y)⁻¹) := by
    intro y x
    apply Units.ext
    rw [Units.val_mul, hc y, Units.val_mul, hc y]
    apply LinearMap.ext
    intro v
    simp
  have quotient_mul : ∀ y₁ y₂ : K,
      ρ₂'.asGroupHom (y₁ * y₂) *
          (ρ₁.asGroupHom (y₁ * y₂))⁻¹ =
        (ρ₂'.asGroupHom y₂ *
            (ρ₁.asGroupHom y₂)⁻¹) *
          (ρ₂'.asGroupHom y₁ *
            (ρ₁.asGroupHom y₁)⁻¹) := by
    intro y₁ y₂
    have h :
        ρ₂'.asGroupHom (y₁ * y₂) *
            (ρ₁.asGroupHom (y₁ * y₂))⁻¹ =
          ρ₂'.asGroupHom y₁ *
            (ρ₂'.asGroupHom y₂ *
              (ρ₁.asGroupHom y₂)⁻¹) *
            (ρ₁.asGroupHom y₁)⁻¹ := by
      simp only [map_mul]
      group
    rw [h, ← scalar_central y₂ (ρ₂'.asGroupHom y₁)]
    group
  have c_mul : ∀ y₁ y₂ : K,
      c (y₁ * y₂) = c y₁ * c y₂ := by
    intro y₁ y₂
    have hreverse : c (y₁ * y₂) = c y₂ * c y₁ := by
      apply scalar_injective
      rw [← hc (y₁ * y₂), quotient_mul y₁ y₂,
        Units.val_mul, hc y₁, hc y₂]
      apply LinearMap.ext
      intro v
      simp [smul_smul, mul_comm]
    rw [hreverse, mul_comm]
  have c_one : c 1 = 1 := by
    apply scalar_injective
    rw [← hc 1]
    have h :
        (ρ₂'.asGroupHom (1 : K) *
            (ρ₁.asGroupHom (1 : K))⁻¹ :
          (Module.End ℂ ψ₁.realization)ˣ) = 1 := by
      simp
    rw [h, one_smul]
    rfl
  have c_subgroup : ∀ h : H, c (h : K) = 1 := by
    intro h
    apply scalar_injective
    rw [← hc (h : K)]
    have hquot :
        (ρ₂'.asGroupHom (h : K) *
            (ρ₁.asGroupHom (h : K))⁻¹ :
          (Module.End ℂ ψ₁.realization)ˣ) = 1 := by
      rw [hagreeUnits h, mul_inv_cancel]
    rw [hquot, one_smul]
    rfl
  let lam : K →* ℂˣ :=
    { toFun := fun y => Units.mk0 (c y) (c_ne_zero y)
      map_one' := Units.ext (by simpa using c_one)
      map_mul' := fun y₁ y₂ =>
        Units.ext (by simpa using c_mul y₁ y₂) }
  refine ⟨lam, fun h => Units.ext (by simpa [lam] using c_subgroup h), ?_⟩
  apply IrreducibleCharacter.ext
  funext y
  have hoperator :
      ρ₂' y = c y • ρ₁ y := by
    have h :
        (ρ₂'.asGroupHom y *
            (ρ₁.asGroupHom y)⁻¹) *
            ρ₁.asGroupHom y =
          ρ₂'.asGroupHom y := by
      group
    have hval := congrArg Units.val h
    rw [Units.val_mul, hc y, Representation.asGroupHom_apply,
      Representation.asGroupHom_apply] at hval
    rw [← hval]
    apply LinearMap.ext
    intro v
    simp
  calc
    ψ₂.values y = ψ₂.realization.character y :=
      (congrFun ψ₂.realization_character y).symm
    _ = ρ₂.character y := rfl
    _ = ρ₂'.character y := (congrFun hchar₂' y).symm
    _ = LinearMap.trace ℂ ψ₁.realization
        (c y • ρ₁ y) := by
          rw [Representation.character, hoperator]
    _ = c y * ρ₁.character y := by
          rw [map_smul]
          rfl
    _ = (lam y : ℂ) * ψ₁.values y := by
      rw [← congrFun ψ₁.realization_character y]
      rfl
    _ = (IrreducibleCharacter.twist lam ψ₁).values y := by
      rw [twist_values]

omit hH in
/-- Conversely, twisting an extension by a linear character trivial on the
normal subgroup gives another extension of the same character. -/
theorem twist_isExtensionAlong
    (hψ₁ : IsExtensionAlong H.subtype χ ψ₁)
    (lam : K →* ℂˣ)
    (hlam : ∀ h : H, lam (h : K) = 1) :
    IsExtensionAlong H.subtype χ
      (IrreducibleCharacter.twist lam ψ₁) :=
  hψ₁.twist_of_eq_one lam hlam

end IsExtensionAlong

end IrreducibleCharacter
end McKayConjecture
