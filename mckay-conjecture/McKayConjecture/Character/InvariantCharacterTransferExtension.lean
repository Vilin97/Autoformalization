/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Transfer

/-!
# Extending invariant characters by transfer

Let `H` be a finite-index normal subgroup of `G`, and let
`χ : H → A` be a conjugation-invariant homomorphism into a
commutative group.  The transfer associated to `χ` restricts to
`χ ^ [G : H]` on `H`.  If the index is coprime to the order of the
finite target, the power map is invertible, and composing transfer
with its inverse extends `χ` to `G`.

This is the elementary character-extension criterion relevant when
the quotient of an interior unit normalizer by its fixed-unit image is
a `p`-group and the target is the unit group of a finite field of
characteristic `p`.
-/

noncomputable section

namespace MonoidHom

open MulAction Subgroup Subgroup.leftTransversals

variable {G A : Type}
variable [Group G] [CommGroup A]
variable (H : Subgroup G) [H.Normal] [H.FiniteIndex]

/-- A homomorphism from a normal subgroup is conjugation-invariant if
conjugating its argument by any ambient group element does not change
its value. -/
def IsConjugationInvariant
    (χ : H →* A) : Prop :=
  ∀ (g : G) (h : H),
    χ ⟨g⁻¹ * (h : G) * g,
      (inferInstance : H.Normal).conj_mem' h h.property g⟩ =
      χ h

omit [H.FiniteIndex] in
/-- The `H`-coset of an element is fixed by left multiplication by an
element of a normal subgroup `H`. -/
theorem subgroup_smul_quotient_eq
    (h : H) (q : G ⧸ H) :
    (h : G) • q = q := by
  induction q using Quotient.inductionOn' with
  | _ g =>
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      change (((h : G) * g)⁻¹ * g) ∈ H
      simpa only [mul_inv_rev, mul_assoc, inv_inv] using
        (inferInstance : H.Normal).conj_mem'
          h⁻¹ (H.inv_mem h.property) g

/-- Transfer of a conjugation-invariant character restricts to the
index-th power of that character. -/
theorem transfer_domRestrict_eq_pow
    (χ : H →* A)
    (hχ : IsConjugationInvariant H χ) :
    (transfer χ).domRestrict H =
      χ ^ H.index := by
  apply MonoidHom.ext
  intro h
  let T : H.LeftTransversal := default
  letI := H.fintypeQuotientOfFiniteIndex
  change transfer χ (h : G) = χ h ^ H.index
  rw [transfer_def χ T]
  rw [Subgroup.leftTransversals.diff,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card,
    ← Finset.card_univ, ← Finset.prod_const]
  apply Finset.prod_congr rfl
  intro q _
  let t : G := T.2.leftQuotientEquiv q
  have hrepresentative :
      (((h : G) • T).2.leftQuotientEquiv q : G) =
        (h : G) * t := by
    rw [smul_apply_eq_smul_apply_inv_smul]
    change
      (h : G) *
          (T.2.leftQuotientEquiv ((h : G)⁻¹ • q) : G) =
        (h : G) * t
    have hq : (h : G)⁻¹ • q = q := by
      simpa using subgroup_smul_quotient_eq H h⁻¹ q
    rw [hq]
  let x : H :=
    ⟨t⁻¹ *
        (((h : G) • T).2.leftQuotientEquiv q : G),
      by
        rw [hrepresentative]
        simpa only [mul_assoc] using
          (inferInstance : H.Normal).conj_mem'
            h h.property t⟩
  let y : H :=
    ⟨t⁻¹ * (h : G) * t,
      (inferInstance : H.Normal).conj_mem'
        h h.property t⟩
  have hxy : x = y := by
    apply Subtype.ext
    change
      t⁻¹ *
          (((h : G) • T).2.leftQuotientEquiv q : G) =
        t⁻¹ * (h : G) * t
    rw [hrepresentative, mul_assoc]
  change χ x = χ h
  rw [hxy]
  convert hχ t h using 1

/-- In a finite commutative group, inverse to the `n`-th power map
when `n` is coprime to the group order. -/
def coprimePowerInverse
    [Finite A]
    {n : ℕ}
    (_hn : Nat.Coprime (Nat.card A) n) :
    A →* A where
  toFun := fun a => a ^ ((Nat.card A).gcdB n : ℤ)
  map_one' := one_zpow _
  map_mul' x y :=
    mul_zpow x y ((Nat.card A).gcdB n)

@[simp]
theorem coprimePowerInverse_apply_pow
    [Finite A]
    {n : ℕ}
    (hn : Nat.Coprime (Nat.card A) n)
    (a : A) :
    coprimePowerInverse hn (a ^ n) = a :=
  by
    change (a ^ n) ^ ((Nat.card A).gcdB n : ℤ) = a
    exact (powCoprime hn).left_inv a

/-- A conjugation-invariant character of a finite-index normal
subgroup extends whenever the subgroup index is coprime to the order
of the finite commutative target. -/
theorem exists_extension_of_isConjugationInvariant_of_coprime
    [Finite A]
    (χ : H →* A)
    (hχ : IsConjugationInvariant H χ)
    (hcoprime : Nat.Coprime (Nat.card A) H.index) :
    ∃ ψ : G →* A,
      ψ.domRestrict H = χ := by
  let ψ : G →* A :=
    (coprimePowerInverse hcoprime).comp (transfer χ)
  refine ⟨ψ, ?_⟩
  apply MonoidHom.ext
  intro h
  have htransfer :=
    congrArg
      (fun f : H →* A => f h)
      (transfer_domRestrict_eq_pow H χ hχ)
  change transfer χ (h : G) = χ h ^ H.index at htransfer
  change
    coprimePowerInverse hcoprime (transfer χ (h : G)) =
      χ h
  rw [htransfer]
  exact coprimePowerInverse_apply_pow hcoprime (χ h)

end MonoidHom
