/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCohomology
import McKayConjecture.CharacterTriple.FiniteFactorNormalization

/-!
# The determinant coboundary of a projective factor set

Taking determinants in the projective multiplication law shows that the
factor set raised to the dimension of the representation is an explicit
two-coboundary.  Consequently the class of the factor set on the same group
is annihilated by that dimension.

For a projective representation associated with a character triple, this
ambient statement does not by itself descend to the outer quotient: the
determinant cochain need not be constant on normal-subgroup cosets.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

universe u v w

variable {K : Type u} {G : Type v} {V : Type w}
variable [Field K] [Group G]
variable [AddCommGroup V] [Module K V]

/-- Pointwise determinant form of the projective multiplication law. -/
theorem determinant_coboundary_eq_factor_pow
    (P : ProjectiveRepresentation K G V) (g h : G) :
    LinearEquiv.det (P.operator h) /
          LinearEquiv.det (P.operator (g * h)) *
        LinearEquiv.det (P.operator g) =
      P.factor g h ^ Module.finrank K V := by
  have hdet :=
    congrArg
      (LinearEquiv.det :
        (V ≃ₗ[K] V) →* Kˣ)
      (P.map_mul g h)
  rw [
    (LinearEquiv.det :
      (V ≃ₗ[K] V) →* Kˣ).map_mul,
    (LinearEquiv.det :
      (V ≃ₗ[K] V) →* Kˣ).map_mul,
    ProjectiveRepresentation.det_scalarLinearEquiv] at hdet
  calc
    LinearEquiv.det (P.operator h) /
          LinearEquiv.det (P.operator (g * h)) *
        LinearEquiv.det (P.operator g) =
      (LinearEquiv.det (P.operator g) *
          LinearEquiv.det (P.operator h)) /
        LinearEquiv.det (P.operator (g * h)) := by
          simp only [div_eq_mul_inv]
          ac_rfl
    _ =
      (P.factor g h ^ Module.finrank K V *
          LinearEquiv.det (P.operator (g * h))) /
        LinearEquiv.det (P.operator (g * h)) := by
          rw [hdet]
    _ = P.factor g h ^ Module.finrank K V := by simp

/-- The determinant cochain witnesses that the projective factor raised to
the representation dimension is a multiplicative two-coboundary. -/
theorem factor_pow_finrank_isMulCoboundary₂
    (P : ProjectiveRepresentation K G V) :
    letI := trivialMulDistribMulAction G Kˣ
    groupCohomology.IsMulCoboundary₂
      (fun x : G × G ↦
        P.factor x.1 x.2 ^ Module.finrank K V) := by
  letI := trivialMulDistribMulAction G Kˣ
  let determinantCochain : G → Kˣ :=
    fun g ↦ LinearEquiv.det (P.operator g)
  refine ⟨determinantCochain, ?_⟩
  intro g h
  change
    determinantCochain h /
          determinantCochain (g * h) *
        determinantCochain g =
      P.factor g h ^ Module.finrank K V
  exact P.determinant_coboundary_eq_factor_pow g h

end ProjectiveRepresentation

namespace FactorSet

variable {G A : Type} [Group G] [CommGroup A]

/-- If the pointwise `n`th power of a factor set is a multiplicative
two-coboundary, then `n` annihilates its class in `H²`. -/
theorem nsmul_h2Class_eq_zero_of_pow_isMulCoboundary₂
    (α : FactorSet G A) (n : ℕ)
    (h :
      letI := trivialMulDistribMulAction G A
      groupCohomology.IsMulCoboundary₂
        (fun x : G × G ↦ α x.1 x.2 ^ n)) :
    letI := trivialMulDistribMulAction G A
    n • α.h2Class = 0 := by
  letI := trivialMulDistribMulAction G A
  change
    n • groupCohomology.H2π
        (Rep.ofMulDistribMulAction G A)
        α.toMathlibCocycle =
      0
  rw [← map_nsmul]
  apply (groupCohomology.H2π_eq_zero_iff
    (A := Rep.ofMulDistribMulAction G A)
    (n • α.toMathlibCocycle)).2
  have hcoboundary :
      (fun x : G × G ↦
        Additive.ofMul (α x.1 x.2 ^ n)) ∈
        groupCohomology.coboundaries₂
          (Rep.ofMulDistribMulAction G A) :=
    (groupCohomology.coboundariesOfIsMulCoboundary₂ h).2
  have hfun :
      (⇑(n • α.toMathlibCocycle) :
          G × G → Additive A) =
        fun x : G × G ↦
          Additive.ofMul (α x.1 x.2 ^ n) := by
    funext x
    change
      n • Additive.ofMul (α x.1 x.2) =
        Additive.ofMul (α x.1 x.2 ^ n)
    exact (ofMul_pow n (α x.1 x.2)).symm
  rw [hfun]
  exact hcoboundary

end FactorSet

namespace ProjectiveRepresentation

variable {K G V : Type}
variable [Field K] [Group G]
variable [AddCommGroup V] [Module K V]
variable [Nontrivial V]

/-- The class of a projective factor set on its ambient group is annihilated
by the representation dimension. -/
theorem finrank_nsmul_factorSet_h2Class_eq_zero
    (P : ProjectiveRepresentation K G V) :
    letI := trivialMulDistribMulAction G Kˣ
    Module.finrank K V • P.factorSet.h2Class = 0 := by
  exact
    P.factorSet.nsmul_h2Class_eq_zero_of_pow_isMulCoboundary₂
      (Module.finrank K V)
      P.factor_pow_finrank_isMulCoboundary₂

end ProjectiveRepresentation

end CharacterTriple
end McKayConjecture
