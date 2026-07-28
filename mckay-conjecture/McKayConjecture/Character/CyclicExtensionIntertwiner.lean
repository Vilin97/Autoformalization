/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Tactic.Group

/-!
# Intertwiners for cyclic extensions

This is the first half of the representation-level cyclic quotient extension
theorem, ported from Yawara Ishida's
`OddOrder.GroupTheory.RepresentationTheory.CyclicExtension`.

Let `H ⫳ K`, let `F` be algebraically closed, and let `ρ` be an irreducible
finite-dimensional representation of `H`.  If `ρ` is equivalent to its
conjugate by `g : K`, this file constructs a unit `P` of `End_F(V)` such that

* `P ρ(h) = ρ(g h g⁻¹) P`; and
* `P ^ t = ρ(g ^ t)` whenever `g ^ t ∈ H`.

The normalization uses Schur's lemma and extraction of an `m`-th root in the
algebraically closed field.  No hypothesis relating `char F` to `|H|` is
needed.

The construction itself is in `CyclicExtensionConstruction.lean`.

## References

* Bender--Glauberman, *Local Analysis for the Odd Order Theorem*,
  Proposition 2.2(b).
-/

noncomputable section

namespace McKayConjecture.RepresentationTheory

variable {K : Type*} [Group K] {H : Subgroup K} [hH : H.Normal]
variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-! ### Conjugation on a normal subgroup -/

namespace ClassFunction

/-- The automorphism of a normal subgroup induced by conjugation by an
ambient element. -/
abbrev conjByMulEquiv (g : K) : H ≃* H :=
  MulAut.conjNormal g

@[simp]
theorem conjByMulEquiv_apply (g : K) (h : H) :
    (conjByMulEquiv (K := K) (H := H) g h : K) =
      g * (h : K) * g⁻¹ :=
  rfl

@[simp]
theorem conjByMulEquiv_one (h : H) :
    conjByMulEquiv (K := K) (H := H) (1 : K) h = h := by
  apply Subtype.ext
  simp

/-- Conjugation automorphisms compose as a left action. -/
theorem conjByMulEquiv_mul (g₁ g₂ : K) (h : H) :
    conjByMulEquiv (K := K) (H := H) g₁
        (conjByMulEquiv (K := K) (H := H) g₂ h) =
      conjByMulEquiv (K := K) (H := H) (g₁ * g₂) h := by
  apply Subtype.ext
  simp only [conjByMulEquiv_apply]
  group

end ClassFunction

/-! ### The conjugate representation -/

/-- The conjugate representation `ρ^g` of a representation of a normal
subgroup, with `(ρ^g)(h) = ρ(g h g⁻¹)`. -/
def conjRep (ρ : Representation F H V) (g : K) :
    Representation F H V :=
  ρ.comp (ClassFunction.conjByMulEquiv (K := K) (H := H) g).toMonoidHom

@[simp]
theorem conjRep_apply (ρ : Representation F H V) (g : K) (h : H) :
    conjRep ρ g h =
      ρ (ClassFunction.conjByMulEquiv (K := K) (H := H) g h) :=
  rfl

/-- The character of a conjugate representation is obtained by conjugating
the argument. -/
theorem conjRep_character [FiniteDimensional F V]
    (ρ : Representation F H V) (g : K) (h : H) :
    (conjRep ρ g).character h =
      ρ.character
        (ClassFunction.conjByMulEquiv (K := K) (H := H) g h) :=
  rfl

/-- Irreducibility ascends along arbitrary precomposition. -/
theorem Representation.isIrreducible_of_isIrreducible_comp
    {G' H' : Type*} [Group G'] [Group H'] {f : H' →* G'}
    (σ : Representation F G' V)
    (hσ : Representation.IsIrreducible (σ.comp f)) :
    Representation.IsIrreducible σ := by
  have hsimple : IsSimpleOrder (Subrepresentation (σ.comp f)) := hσ
  haveI := hsimple.toNontrivial
  let restrictSubrepresentation :
      Subrepresentation σ → Subrepresentation (σ.comp f) := fun R =>
    { toSubmodule := R.toSubmodule
      apply_mem_toSubmodule := fun h _v hv =>
        R.apply_mem_toSubmodule (f h) hv }
  have hbotσ : (⊥ : Subrepresentation σ).toSubmodule = ⊥ := rfl
  have htopσ : (⊤ : Subrepresentation σ).toSubmodule = ⊤ := rfl
  have hbotComp :
      (⊥ : Subrepresentation (σ.comp f)).toSubmodule = ⊥ := rfl
  have htopComp :
      (⊤ : Subrepresentation (σ.comp f)).toSubmodule = ⊤ := rfl
  have hVne : (⊥ : Submodule F V) ≠ ⊤ := fun h =>
    bot_ne_top (α := Subrepresentation (σ.comp f))
      (Subrepresentation.toSubmodule_injective
        (by rw [hbotComp, htopComp]; exact h))
  haveI : Nontrivial (Subrepresentation σ) :=
    ⟨⟨⊥, ⊤, fun h =>
      hVne (by rw [← hbotσ, h, htopσ])⟩⟩
  exact ⟨fun S => by
    rcases hsimple.eq_bot_or_eq_top (restrictSubrepresentation S) with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective
        ((congrArg Subrepresentation.toSubmodule h).trans hbotComp))
    · exact Or.inr (Subrepresentation.toSubmodule_injective
        ((congrArg Subrepresentation.toSubmodule h).trans htopComp))⟩

/-- Conjugating an irreducible representation preserves irreducibility. -/
theorem isIrreducible_conjRep
    (ρ : Representation F H V) [Representation.IsIrreducible ρ]
    (g : K) : Representation.IsIrreducible (conjRep ρ g) := by
  have hcomp : (conjRep ρ g).comp
      (ClassFunction.conjByMulEquiv (K := K) (H := H) g⁻¹).toMonoidHom =
        ρ := by
    refine MonoidHom.ext fun h => ?_
    calc
      ((conjRep ρ g).comp
          (ClassFunction.conjByMulEquiv
            (K := K) (H := H) g⁻¹).toMonoidHom) h =
          ρ (ClassFunction.conjByMulEquiv (K := K) (H := H) g
            (ClassFunction.conjByMulEquiv
              (K := K) (H := H) g⁻¹ h)) := rfl
      _ = ρ h := by
        rw [ClassFunction.conjByMulEquiv_mul, mul_inv_cancel,
          ClassFunction.conjByMulEquiv_one]
  exact Representation.isIrreducible_of_isIrreducible_comp
    (conjRep ρ g)
    (hcomp ▸ ‹Representation.IsIrreducible ρ›)

/-! ### The intertwining unit -/

/-- An equivalence `ρ ≅ ρ^g` gives a unit `P` of the endomorphism ring
satisfying `P ρ(h) = ρ(g h g⁻¹) P`. -/
theorem exists_conjugation_unit_of_nonempty_equiv
    (ρ : Representation F H V) (g : K)
    (hequiv : Nonempty (ρ.Equiv (conjRep ρ g))) :
    ∃ P : (Module.End F V)ˣ, ∀ h : H,
      P * ρ.asGroupHom h =
        ρ.asGroupHom
          (ClassFunction.conjByMulEquiv (K := K) (H := H) g h) * P := by
  obtain ⟨φ⟩ := hequiv
  refine ⟨⟨φ.toLinearMap, φ.toLinearEquiv.symm.toLinearMap,
    LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩, fun h => ?_⟩
  · rw [Module.End.mul_apply]
    exact φ.toLinearEquiv.apply_symm_apply v
  · rw [Module.End.mul_apply]
    exact φ.toLinearEquiv.symm_apply_apply v
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    change φ.toLinearMap * (ρ.asGroupHom h : Module.End F V) =
      (ρ.asGroupHom
        (ClassFunction.conjByMulEquiv (K := K) (H := H) g h) :
          Module.End F V) * φ.toLinearMap
    rw [Representation.asGroupHom_apply, Representation.asGroupHom_apply,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact φ.isIntertwining' h

/-! ### Schur normalization -/

section Normalization

variable [FiniteDimensional F V]

/-- Schur's lemma in commutant form over an algebraically closed field. -/
theorem exists_smul_id_of_forall_mul_comm
    {G' : Type*} [Group G'] [IsAlgClosed F]
    (ρ : Representation F G' V) [Representation.IsIrreducible ρ]
    (T : Module.End F V) (hT : ∀ x : G', ρ x * T = T * ρ x) :
    ∃ c : F, T = c • LinearMap.id := by
  have hT' : ∀ (x : G') (v : V), T (ρ x v) = ρ x (T v) :=
    fun x v => by
      have h := LinearMap.congr_fun (hT x) v
      simpa only [Module.End.mul_apply] using h.symm
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective
      (T.intertwiningMap_of_isIntertwiningMap ρ ρ hT')
  refine ⟨c, ?_⟩
  have hlinear :
      T =
        (algebraMap F (Representation.IntertwiningMap ρ ρ) c).toLinearMap := by
    rw [hc]
    rfl
  rw [hlinear, Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.toLinearMap_smul]
  congr 1

variable {ρ : Representation F H V} {g : K}
  {P : (Module.End F V)ˣ}

omit [FiniteDimensional F V] in
/-- The inverse of a conjugation unit conjugates in the opposite direction. -/
theorem conjugation_unit_inv_comm
    (hP : ∀ h : H, P * ρ.asGroupHom h =
      ρ.asGroupHom
        (ClassFunction.conjByMulEquiv (K := K) (H := H) g h) * P)
    (h : H) :
    P⁻¹ * ρ.asGroupHom h =
      ρ.asGroupHom
        (ClassFunction.conjByMulEquiv (K := K) (H := H) g⁻¹ h) * P⁻¹ := by
  have key := hP
    (ClassFunction.conjByMulEquiv (K := K) (H := H) g⁻¹ h)
  rw [ClassFunction.conjByMulEquiv_mul, mul_inv_cancel,
    ClassFunction.conjByMulEquiv_one] at key
  calc
    P⁻¹ * ρ.asGroupHom h =
        P⁻¹ * (ρ.asGroupHom h * P) * P⁻¹ := by group
    _ = P⁻¹ *
        (P * ρ.asGroupHom
          (ClassFunction.conjByMulEquiv (K := K) (H := H) g⁻¹ h)) *
        P⁻¹ := by rw [← key]
    _ = ρ.asGroupHom
        (ClassFunction.conjByMulEquiv (K := K) (H := H) g⁻¹ h) * P⁻¹ := by
      group

omit [FiniteDimensional F V] in
/-- Iterating a conjugation unit gives conjugation by every integral power
of the ambient element. -/
theorem conjugation_unit_zpow_comm
    (hP : ∀ h : H, P * ρ.asGroupHom h =
      ρ.asGroupHom
        (ClassFunction.conjByMulEquiv (K := K) (H := H) g h) * P) :
    ∀ (i : ℤ) (h : H), P ^ i * ρ.asGroupHom h =
      ρ.asGroupHom
        (ClassFunction.conjByMulEquiv
          (K := K) (H := H) (g ^ i) h) * P ^ i := by
  intro i
  induction i using Int.induction_on with
  | zero =>
      intro h
      rw [zpow_zero P, zpow_zero g, ClassFunction.conjByMulEquiv_one,
        one_mul, mul_one]
  | succ i ih =>
      intro h
      rw [zpow_add_one P (i : ℤ), zpow_add_one g (i : ℤ)]
      calc
        P ^ (i : ℤ) * P * ρ.asGroupHom h =
            P ^ (i : ℤ) * (P * ρ.asGroupHom h) := by group
        _ = P ^ (i : ℤ) *
            (ρ.asGroupHom
              (ClassFunction.conjByMulEquiv
                (K := K) (H := H) g h) * P) := by
              rw [hP h]
        _ = P ^ (i : ℤ) * ρ.asGroupHom
              (ClassFunction.conjByMulEquiv
                (K := K) (H := H) g h) * P := by group
        _ = ρ.asGroupHom
              (ClassFunction.conjByMulEquiv
                (K := K) (H := H) (g ^ (i : ℤ))
                (ClassFunction.conjByMulEquiv
                  (K := K) (H := H) g h)) *
              P ^ (i : ℤ) * P := by
                rw [ih (ClassFunction.conjByMulEquiv
                  (K := K) (H := H) g h)]
        _ = ρ.asGroupHom
              (ClassFunction.conjByMulEquiv
                (K := K) (H := H) (g ^ (i : ℤ) * g) h) *
              (P ^ (i : ℤ) * P) := by
                rw [ClassFunction.conjByMulEquiv_mul]
                group
  | pred i ih =>
      intro h
      rw [zpow_sub_one P (-(i : ℤ)), zpow_sub_one g (-(i : ℤ))]
      calc
        P ^ (-(i : ℤ)) * P⁻¹ * ρ.asGroupHom h =
            P ^ (-(i : ℤ)) * (P⁻¹ * ρ.asGroupHom h) := by group
        _ = P ^ (-(i : ℤ)) *
            (ρ.asGroupHom
              (ClassFunction.conjByMulEquiv
                (K := K) (H := H) g⁻¹ h) * P⁻¹) := by
              rw [conjugation_unit_inv_comm hP h]
        _ = P ^ (-(i : ℤ)) * ρ.asGroupHom
              (ClassFunction.conjByMulEquiv
                (K := K) (H := H) g⁻¹ h) * P⁻¹ := by group
        _ = ρ.asGroupHom
              (ClassFunction.conjByMulEquiv
                (K := K) (H := H) (g ^ (-(i : ℤ)))
                (ClassFunction.conjByMulEquiv
                  (K := K) (H := H) g⁻¹ h)) *
              P ^ (-(i : ℤ)) * P⁻¹ := by
                rw [ih (ClassFunction.conjByMulEquiv
                  (K := K) (H := H) g⁻¹ h)]
        _ = ρ.asGroupHom
              (ClassFunction.conjByMulEquiv
                (K := K) (H := H) (g ^ (-(i : ℤ)) * g⁻¹) h) *
              (P ^ (-(i : ℤ)) * P⁻¹) := by
                rw [ClassFunction.conjByMulEquiv_mul]
                group

/-- A normalized conjugation unit.

For an irreducible `ρ` equivalent to `ρ^g`, the resulting `P` intertwines
conjugation by `g` and agrees with `ρ(g^t)` whenever `g^t` lies in `H`.
-/
theorem exists_normalized_conjugation_unit_of_nonempty_equiv
    [Finite K] [IsAlgClosed F]
    (ρ : Representation F H V) [Representation.IsIrreducible ρ]
    (g : K) (hequiv : Nonempty (ρ.Equiv (conjRep ρ g))) :
    ∃ P : (Module.End F V)ˣ,
      (∀ h : H, P * ρ.asGroupHom h =
        ρ.asGroupHom
          (ClassFunction.conjByMulEquiv (K := K) (H := H) g h) * P) ∧
      ∀ (t : ℤ) (ht : g ^ t ∈ H),
        P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩ := by
  obtain ⟨P₀, hP₀⟩ :=
    exists_conjugation_unit_of_nonempty_equiv ρ g hequiv
  set m : ℕ := orderOf (QuotientGroup.mk' H g) with hm
  have hm0 : 0 < m := orderOf_pos _
  have hgm : g ^ m ∈ H := by
    have h : (QuotientGroup.mk' H) (g ^ m) = 1 := by
      rw [map_pow]
      exact pow_orderOf_eq_one _
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hdvd : ∀ t : ℤ, g ^ t ∈ H → (m : ℤ) ∣ t := by
    intro t ht
    rw [hm, orderOf_dvd_iff_zpow_eq_one, ← map_zpow,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ht
  set R : (Module.End F V)ˣ :=
    ρ.asGroupHom ⟨g ^ m, hgm⟩ with hR
  have hTcomm : ∀ h : H,
      ρ h * ((R⁻¹ * P₀ ^ (m : ℤ) : (Module.End F V)ˣ) :
          Module.End F V) =
        ((R⁻¹ * P₀ ^ (m : ℤ) : (Module.End F V)ˣ) :
          Module.End F V) * ρ h := by
    intro h
    have hconj :
        ClassFunction.conjByMulEquiv
            (K := K) (H := H) (g ^ (m : ℤ)) h =
          ⟨g ^ m, hgm⟩ * h * (⟨g ^ m, hgm⟩ : H)⁻¹ := by
      apply Subtype.ext
      rw [ClassFunction.conjByMulEquiv_apply, zpow_natCast]
      rfl
    have hiter := conjugation_unit_zpow_comm hP₀ (m : ℤ) h
    rw [hconj, map_mul, map_mul, map_inv, ← hR] at hiter
    have hu : ρ.asGroupHom h * (R⁻¹ * P₀ ^ (m : ℤ)) =
        (R⁻¹ * P₀ ^ (m : ℤ)) * ρ.asGroupHom h := by
      calc
        ρ.asGroupHom h * (R⁻¹ * P₀ ^ (m : ℤ)) =
            R⁻¹ * (R * ρ.asGroupHom h * R⁻¹ * P₀ ^ (m : ℤ)) := by
              group
        _ = R⁻¹ * (P₀ ^ (m : ℤ) * ρ.asGroupHom h) := by
              rw [← hiter]
        _ = (R⁻¹ * P₀ ^ (m : ℤ)) * ρ.asGroupHom h := by
              group
    have h := congrArg Units.val hu
    simpa only [Units.val_mul, Representation.asGroupHom_apply] using h
  obtain ⟨c, hc⟩ :=
    exists_smul_id_of_forall_mul_comm ρ _ hTcomm
  haveI : Nontrivial V := by
    haveI hsimple : Nontrivial (Subrepresentation ρ) :=
      IsSimpleOrder.toNontrivial
    have hsubmodule : Nontrivial (Submodule F V) :=
      (Subrepresentation.toSubmodule_injective (ρ := ρ)).nontrivial
    exact (Submodule.nontrivial_iff F).mp hsubmodule
  haveI : Nontrivial (Module.End F V) :=
    ⟨1, 0, fun h => by
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact hv (by simpa using LinearMap.congr_fun h v)⟩
  have hc0 : c ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at hc
    exact Units.ne_zero (R⁻¹ * P₀ ^ (m : ℤ)) hc
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (c⁻¹) hm0
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow hm0.ne'] at hz
    exact inv_ne_zero hc0 hz.symm
  set scalarUnit : Fˣ →* (Module.End F V)ˣ :=
    Units.map (algebraMap F (Module.End F V)).toMonoidHom
  have scalarUnit_val : ∀ w : Fˣ,
      ((scalarUnit w : (Module.End F V)ˣ) : Module.End F V) =
        algebraMap F _ (w : F) := fun _ => rfl
  have scalarUnit_central :
      ∀ (w : Fˣ) (x : (Module.End F V)ˣ),
        scalarUnit w * x = x * scalarUnit w := fun w x =>
    Units.ext (by
      rw [Units.val_mul, Units.val_mul, scalarUnit_val]
      exact Algebra.commutes (w : F) (x : Module.End F V))
  refine ⟨scalarUnit (Units.mk0 z hz0) * P₀, fun h => ?_, ?_⟩
  · calc
      scalarUnit (Units.mk0 z hz0) * P₀ * ρ.asGroupHom h =
          scalarUnit (Units.mk0 z hz0) *
            (P₀ * ρ.asGroupHom h) := by group
      _ = scalarUnit (Units.mk0 z hz0) *
          (ρ.asGroupHom
            (ClassFunction.conjByMulEquiv
              (K := K) (H := H) g h) * P₀) := by
            rw [hP₀ h]
      _ = scalarUnit (Units.mk0 z hz0) *
            ρ.asGroupHom
              (ClassFunction.conjByMulEquiv
                (K := K) (H := H) g h) * P₀ := by group
      _ = ρ.asGroupHom
            (ClassFunction.conjByMulEquiv
              (K := K) (H := H) g h) *
            scalarUnit (Units.mk0 z hz0) * P₀ := by
              rw [scalarUnit_central]
      _ = ρ.asGroupHom
            (ClassFunction.conjByMulEquiv
              (K := K) (H := H) g h) *
            (scalarUnit (Units.mk0 z hz0) * P₀) := by group
  · intro t ht
    obtain ⟨s, rfl⟩ := hdvd t ht
    have hT : R⁻¹ * P₀ ^ (m : ℤ) =
        scalarUnit (Units.mk0 c hc0) := Units.ext (by
      rw [scalarUnit_val, hc]
      exact (Module.algebraMap_end_eq_smul_id F F V c).symm)
    have hP₀m : P₀ ^ (m : ℤ) =
        R * scalarUnit (Units.mk0 c hc0) := by
      rw [← hT]
      group
    have hscalar :
        scalarUnit (Units.mk0 z hz0) ^ (m : ℤ) *
            scalarUnit (Units.mk0 c hc0) = 1 := by
      rw [← map_zpow, ← map_mul]
      have hunit :
          Units.mk0 z hz0 ^ (m : ℤ) * Units.mk0 c hc0 = 1 :=
        Units.ext (by
          rw [Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
          change z ^ m * c = 1
          rw [hz, inv_mul_cancel₀ hc0])
      rw [hunit, map_one]
    have hmove :
        scalarUnit (Units.mk0 z hz0) ^ (m : ℤ) *
            (R * scalarUnit (Units.mk0 c hc0)) =
          R * (scalarUnit (Units.mk0 z hz0) ^ (m : ℤ) *
            scalarUnit (Units.mk0 c hc0)) := by
      rw [← map_zpow, ← mul_assoc, scalarUnit_central _ R, mul_assoc]
    calc
      (scalarUnit (Units.mk0 z hz0) * P₀) ^ ((m : ℤ) * s) =
          ((scalarUnit (Units.mk0 z hz0) * P₀) ^ (m : ℤ)) ^ s := by
            rw [zpow_mul]
      _ = (scalarUnit (Units.mk0 z hz0) ^ (m : ℤ) *
            P₀ ^ (m : ℤ)) ^ s := by
              rw [Commute.mul_zpow
                (scalarUnit_central (Units.mk0 z hz0) P₀)]
      _ = (scalarUnit (Units.mk0 z hz0) ^ (m : ℤ) *
            (R * scalarUnit (Units.mk0 c hc0))) ^ s := by
              rw [hP₀m]
      _ = (R * (scalarUnit (Units.mk0 z hz0) ^ (m : ℤ) *
            scalarUnit (Units.mk0 c hc0))) ^ s := by
              rw [hmove]
      _ = R ^ s := by rw [hscalar, mul_one]
      _ = ρ.asGroupHom ((⟨g ^ m, hgm⟩ : H) ^ s) := by
            rw [hR, ← map_zpow]
      _ = ρ.asGroupHom ⟨g ^ ((m : ℤ) * s), ht⟩ := by
        congr 1
        apply Subtype.ext
        rw [SubgroupClass.coe_zpow]
        change ((g ^ m : K)) ^ s = g ^ ((m : ℤ) * s)
        rw [← zpow_natCast g m, ← zpow_mul]

end Normalization

end McKayConjecture.RepresentationTheory
