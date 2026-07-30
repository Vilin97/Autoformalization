/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionPairing
import McKayConjecture.Character.Gallagher
import McKayConjecture.GroupTheory.FiniteDualOrthogonality

/-!
# Gallagher's extension norm on quotient cosets

If an irreducible character of a normal subgroup extends irreducibly
to the ambient finite group, its bilinear norm on every coset of the
normal subgroup is the order of that subgroup, provided the quotient
is abelian.  The cyclic-quotient statement is an immediate special
case.

The proof is finite Fourier inversion on the quotient.  Gallagher's
injectivity theorem makes the quotient-linear twists of the chosen
extension pairwise distinct, ordinary character orthogonality leaves
only the trivial twist, and finite-dual orthogonality isolates one
quotient fibre.
-/

noncomputable section

open scoped BigOperators IsMulCommutative

namespace McKayConjecture

variable {K : Type} [Group K] [Finite K]
variable (H : Subgroup K) [H.Normal]

noncomputable local instance (priority := 2000)
    gallagherCosetNormFintype
    (G : Type) [Group G] [Finite G] : Fintype G :=
  Fintype.ofFinite G

/-- The bilinear norm of an irreducible extension on any coset of a
normal subgroup with abelian quotient is the order of the subgroup. -/
theorem abelianQuotientExtension_coset_bilinearNorm
    [IsMulCommutative (K ⧸ H)]
    (θ : IrreducibleCharacter H)
    (ψ : IrreducibleCharacter K)
    (hψ :
      IrreducibleCharacter.IsExtensionAlong
        H.subtype θ ψ)
    (g : K) :
    ∑ h : H,
        ψ.values (g * (h : K)) *
          ψ.values ((g * (h : K))⁻¹) =
      (Nat.card H : ℂ) := by
  classical
  let Q : Type := K ⧸ H
  let qH : K →* Q := QuotientGroup.mk' H
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Fintype (Q →* ℂˣ) := Fintype.ofFinite _
  have hinflate_one :
      IrreducibleCharacter.inflateLinearCharacter H
          (1 : Q →* ℂˣ) =
        1 := by
    apply MonoidHom.ext
    intro x
    simp [IrreducibleCharacter.inflateLinearCharacter]
  have hpair :
      ∀ beta : Q →* ℂˣ,
        ClassFunction.normalizedPairing ψ.toClassFunction
          (IrreducibleCharacter.twist
            (IrreducibleCharacter.inflateLinearCharacter H beta)
            ψ).toClassFunction =
          if beta = 1 then 1 else 0 := by
    intro beta
    by_cases hbeta : beta = 1
    · subst beta
      rw [hinflate_one, IrreducibleCharacter.twist_one]
      simp
    · simp only [hbeta, ↓reduceIte]
      apply
        ClassFunction.normalizedPairing_irreducible_eq_zero_of_ne
      intro heq
      apply hbeta
      apply
        IrreducibleCharacter.quotientTwistExtension_injective hψ
      apply Subtype.ext
      change
        IrreducibleCharacter.twist
            (IrreducibleCharacter.inflateLinearCharacter H beta) ψ =
          IrreducibleCharacter.twist
            (IrreducibleCharacter.inflateLinearCharacter H 1) ψ
      rw [hinflate_one, IrreducibleCharacter.twist_one]
      exact heq.symm
  have hweighted :
      ∑ beta : Q →* ℂˣ,
          (beta (qH g) : ℂ) *
            ClassFunction.normalizedPairing ψ.toClassFunction
              (IrreducibleCharacter.twist
                (IrreducibleCharacter.inflateLinearCharacter H beta)
                ψ).toClassFunction =
        1 := by
    simp_rw [hpair]
    rw [Finset.sum_eq_single (1 : Q →* ℂˣ)]
    · simp
    · intro beta _ hbeta
      simp [hbeta]
    · simp
  have hweighted' :
      ∑ beta : Q →* ℂˣ,
          (beta (qH g) : ℂ) *
            ((Nat.card K : ℂ)⁻¹ *
              ∑ x : K,
                ψ.values x *
                  ((beta (qH x⁻¹) : ℂ) *
                    ψ.values x⁻¹)) =
        1 := by
    change
      ∑ beta : Q →* ℂˣ,
          (beta (qH g) : ℂ) *
            ((Nat.card K : ℂ)⁻¹ *
              ∑ x : K,
                ψ.values x *
                  (IrreducibleCharacter.twist
                    (IrreducibleCharacter.inflateLinearCharacter
                      H beta) ψ).values x⁻¹) =
        1 at hweighted
    simpa only [IrreducibleCharacter.twist_values,
      IrreducibleCharacter.inflateLinearCharacter_apply] using
        hweighted
  have hrearrange :
      (∑ beta : Q →* ℂˣ,
          (beta (qH g) : ℂ) *
            ((Nat.card K : ℂ)⁻¹ *
              ∑ x : K,
                ψ.values x *
                  ((beta (qH x⁻¹) : ℂ) *
                    ψ.values x⁻¹))) =
        (Nat.card K : ℂ)⁻¹ *
          ∑ x : K,
            ψ.values x * ψ.values x⁻¹ *
              ∑ beta : Q →* ℂˣ,
                (beta (qH g * (qH x)⁻¹) : ℂ) := by
    calc
      _ = (Nat.card K : ℂ)⁻¹ *
          ∑ beta : Q →* ℂˣ,
            ∑ x : K,
              (beta (qH g) : ℂ) *
                (ψ.values x *
                  ((beta (qH x⁻¹) : ℂ) *
                    ψ.values x⁻¹)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro beta _
              rw [Finset.mul_sum]
              rw [Finset.mul_sum, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              ring
      _ = (Nat.card K : ℂ)⁻¹ *
          ∑ x : K,
            ∑ beta : Q →* ℂˣ,
              (beta (qH g) : ℂ) *
                (ψ.values x *
                  ((beta (qH x⁻¹) : ℂ) *
                    ψ.values x⁻¹)) := by
              rw [Finset.sum_comm]
      _ = _ := by
              congr 1
              apply Finset.sum_congr rfl
              intro x _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro beta _
              simp only [map_inv, map_mul, Units.val_mul,
                Units.val_inv_eq_inv_val]
              ring
  rw [hrearrange] at hweighted'
  have hdual (x : K) :
      (∑ beta : Q →* ℂˣ,
          (beta (qH g * (qH x)⁻¹) : ℂ)) =
        if qH x = qH g
          then (Nat.card Q : ℂ)
          else 0 := by
    by_cases hx : qH x = qH g
    · simp only [hx, if_pos]
      simpa using
        (sum_complexUnitCharacters_apply_one
          (A := Q))
    · simp only [hx, if_false]
      apply sum_complexUnitCharacters_apply_eq_zero
      intro hone
      apply hx
      have hquotient : qH g = qH x := by
        exact mul_inv_eq_one.mp hone
      exact hquotient.symm
  simp_rw [hdual] at hweighted'
  let fiber :=
    {x : K // qH x = qH g}
  let fiberEquiv : H ≃ fiber := {
    toFun h := by
      refine ⟨g * (h : K), ?_⟩
      rw [map_mul, show qH (h : K) = 1 from
        (QuotientGroup.eq_one_iff (h : K)).mpr h.2,
        mul_one]
    invFun x := by
      refine
        ⟨g⁻¹ * (x : K), ?_⟩
      apply
        (QuotientGroup.eq_one_iff
          (g⁻¹ * (x : K))).mp
      change qH (g⁻¹ * (x : K)) = 1
      rw [map_mul, map_inv, x.property]
      simp
    left_inv h := by
      apply Subtype.ext
      simp
    right_inv x := by
      apply Subtype.ext
      simp
  }
  have hfiber :
      (∑ x : K,
          if qH x = qH g
            then ψ.values x * ψ.values x⁻¹
            else 0) =
        ∑ h : H,
          ψ.values (g * (h : K)) *
            ψ.values (g * (h : K))⁻¹ := by
    calc
      _ =
          ∑ x ∈
              Finset.univ.filter
                (fun x : K ↦ qH x = qH g),
            ψ.values x * ψ.values x⁻¹ := by
              symm
              exact
                Finset.sum_filter
                  (fun x : K ↦ qH x = qH g)
                  (fun x : K ↦
                    ψ.values x * ψ.values x⁻¹)
      _ =
          ∑ x : fiber,
            ψ.values (x : K) *
              ψ.values (x : K)⁻¹ := by
              exact
                Finset.sum_subtype
                  (Finset.univ.filter
                    (fun x : K ↦ qH x = qH g))
                  (by simp)
                  (fun x : K ↦
                    ψ.values x * ψ.values x⁻¹)
      _ = _ := by
        exact
          (Equiv.sum_comp fiberEquiv
            (fun x : fiber ↦
              ψ.values (x : K) *
                ψ.values (x : K)⁻¹)).symm
  change
    (Nat.card K : ℂ)⁻¹ *
        (∑ x : K,
          ψ.values x * ψ.values x⁻¹ *
            (if qH x = qH g
              then (Nat.card Q : ℂ)
              else 0)) =
      1 at hweighted'
  have hfactor :
      (∑ x : K,
          ψ.values x * ψ.values x⁻¹ *
            if qH x = qH g
              then (Nat.card Q : ℂ)
              else 0) =
        (Nat.card Q : ℂ) *
          ∑ x : K,
            if qH x = qH g
              then ψ.values x * ψ.values x⁻¹
              else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : qH x = qH g <;>
      simp [hx]
    ring
  rw [hfactor, hfiber] at hweighted'
  have hHne : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card H).ne'
  have hQne : (Nat.card Q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card Q).ne'
  have hcard :
      Nat.card K = Nat.card Q * Nat.card H :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup H
  rw [hcard, Nat.cast_mul] at hweighted'
  field_simp [hHne, hQne] at hweighted'
  exact hweighted'

/-- The bilinear norm of an irreducible extension on every coset of a
normal subgroup with cyclic quotient is the order of the subgroup. -/
theorem cyclicQuotientExtension_coset_bilinearNorm
    [IsCyclic (K ⧸ H)]
    (θ : IrreducibleCharacter H)
    (ψ : IrreducibleCharacter K)
    (hψ :
      IrreducibleCharacter.IsExtensionAlong
        H.subtype θ ψ)
    (g : K) :
    ∑ h : H,
        ψ.values (g * (h : K)) *
          ψ.values ((g * (h : K))⁻¹) =
      (Nat.card H : ℂ) := by
  exact
    abelianQuotientExtension_coset_bilinearNorm
      H θ ψ hψ g

end McKayConjecture
