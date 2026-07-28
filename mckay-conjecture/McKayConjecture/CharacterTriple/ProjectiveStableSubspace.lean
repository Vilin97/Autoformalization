/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveIrreducible

/-!
# Restricting a projective representation to a stable subspace

A submodule preserved by all chosen projective operators is automatically
preserved by their inverses: the inverse of the operator at `g` is a
nonzero scalar multiple of the operator at `g⁻¹`.  Hence every stable
submodule inherits a projective representation with exactly the same
factor, not merely a cohomologous factor.

This is the basic linear-algebra interface needed when a Dade--Glauberman
multiplicity space is replaced by a selected Sylow-linear summand.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K : Type u} {G : Type v} {V : Type w}
variable [Field K] [Group G]
variable [AddCommGroup V] [Module K V]

/-- The inverse of a chosen projective operator preserves every stable
submodule. -/
theorem IsStable.operator_symm_mem
    {P : ProjectiveRepresentation K G V}
    {S : Submodule K V}
    (hS : P.IsStable S)
    (g : G) {v : V} (hv : v ∈ S) :
    (P.operator g).symm v ∈ S := by
  let c : Kˣ :=
    P.factor g g⁻¹ * P.factor 1 1
  have hmul :
      P.operator g * P.operator g⁻¹ =
        scalarLinearEquiv K V c := by
    calc
      P.operator g * P.operator g⁻¹ =
          scalarLinearEquiv K V (P.factor g g⁻¹) *
            P.operator (g * g⁻¹) :=
        P.map_mul g g⁻¹
      _ =
          scalarLinearEquiv K V (P.factor g g⁻¹) *
            P.operator 1 := by simp only [mul_inv_cancel]
      _ =
          scalarLinearEquiv K V (P.factor g g⁻¹) *
            scalarLinearEquiv K V (P.factor 1 1) := by
        rw [P.operator_one_eq_scalar_left 1]
      _ = scalarLinearEquiv K V c := by
        rw [← scalarLinearEquiv_mul]
  have hinverse :
      (P.operator g).symm =
        scalarLinearEquiv K V c⁻¹ * P.operator g⁻¹ := by
    apply mul_left_cancel (a := P.operator g)
    calc
      P.operator g * (P.operator g).symm = 1 := by
        change P.operator g * (P.operator g)⁻¹ = 1
        exact mul_inv_cancel (P.operator g)
      _ =
          scalarLinearEquiv K V c⁻¹ *
            scalarLinearEquiv K V c := by
        symm
        rw [← scalarLinearEquiv_mul, inv_mul_cancel, map_one]
      _ =
          scalarLinearEquiv K V c⁻¹ *
            (P.operator g * P.operator g⁻¹) := by
        rw [hmul]
      _ =
          P.operator g *
            (scalarLinearEquiv K V c⁻¹ *
              P.operator g⁻¹) := by
        rw [← mul_assoc,
          scalarLinearEquiv_comm K V c⁻¹ (P.operator g),
          mul_assoc]
  rw [hinverse]
  rw [LinearEquiv.mul_apply, scalarLinearEquiv_apply]
  rw [Units.val_inv_eq_inv_val]
  exact S.smul_mem (c⁻¹ : K) (hS g⁻¹ hv)

/-- The chosen operator restricted to a stable submodule. -/
def stableOperator
    (P : ProjectiveRepresentation K G V)
    (S : Submodule K V)
    (hS : P.IsStable S)
    (g : G) :
    S ≃ₗ[K] S where
  toFun v := ⟨P.operator g (v : V), hS g v.property⟩
  invFun v :=
    ⟨(P.operator g).symm (v : V),
      hS.operator_symm_mem g v.property⟩
  left_inv v := by
    apply Subtype.ext
    exact (P.operator g).symm_apply_apply (v : V)
  right_inv v := by
    apply Subtype.ext
    exact (P.operator g).apply_symm_apply (v : V)
  map_add' v w := by
    apply Subtype.ext
    exact map_add (P.operator g) (v : V) (w : V)
  map_smul' c v := by
    apply Subtype.ext
    exact map_smul (P.operator g) c (v : V)

@[simp]
theorem stableOperator_coe
    (P : ProjectiveRepresentation K G V)
    (S : Submodule K V)
    (hS : P.IsStable S)
    (g : G) (v : S) :
    ((stableOperator P S hS g v : S) : V) =
      P.operator g (v : V) :=
  rfl

/-- The projective representation inherited by a stable submodule.  Its
factor is definitionally the original factor. -/
def restrictStable
    (P : ProjectiveRepresentation K G V)
    (S : Submodule K V)
    (hS : P.IsStable S) :
    ProjectiveRepresentation K G S where
  operator := stableOperator P S hS
  factor := P.factor
  map_mul g h := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact DFunLike.congr_fun (P.map_mul g h) (v : V)

@[simp]
theorem restrictStable_operator_coe
    (P : ProjectiveRepresentation K G V)
    (S : Submodule K V)
    (hS : P.IsStable S)
    (g : G) (v : S) :
    (((restrictStable P S hS).operator g v : S) : V) =
      P.operator g (v : V) :=
  rfl

@[simp]
theorem restrictStable_factor
    (P : ProjectiveRepresentation K G V)
    (S : Submodule K V)
    (hS : P.IsStable S)
    (g h : G) :
    (restrictStable P S hS).factor g h =
      P.factor g h :=
  rfl

/-- Restriction to a nonzero stable submodule preserves the factor set
literally. -/
theorem restrictStable_factorSet
    (P : ProjectiveRepresentation K G V)
    (S : Submodule K V)
    (hS : P.IsStable S)
    [Nontrivial V] [Nontrivial S] :
    (restrictStable P S hS).factorSet =
      P.factorSet := by
  apply FactorSet.ext
  intro g h
  rfl

/-- Normalization is inherited by every stable submodule. -/
theorem restrictStable_isNormalized
    (P : ProjectiveRepresentation K G V)
    (S : Submodule K V)
    (hS : P.IsStable S)
    (hP : P.IsNormalized) :
    (restrictStable P S hS).IsNormalized := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change P.operator 1 v = v
  rw [hP]
  rfl

/-- The simultaneous scalar eigenspace for the operators pulled back along
`j`.  The scalar parameter need not be a homomorphism: for a genuinely
projective action its multiplication law is twisted by the pulled-back
factor. -/
def scalarRestrictionSubmodule
    {H : Type*} [Group H]
    (P : ProjectiveRepresentation K G V)
    (j : H →* G)
    (mu : H → Kˣ) :
    Submodule K V where
  carrier :=
    {v | ∀ h : H,
      P.operator (j h) v = (mu h : K) • v}
  zero_mem' := by
    intro h
    simp
  add_mem' := by
    intro v w hv hw h
    rw [map_add, hv h, hw h, smul_add]
  smul_mem' := by
    intro c v hv h
    rw [map_smul, hv h, smul_comm]

@[simp]
theorem mem_scalarRestrictionSubmodule_iff
    {H : Type*} [Group H]
    (P : ProjectiveRepresentation K G V)
    (j : H →* G)
    (mu : H → Kˣ)
    (v : V) :
    v ∈ scalarRestrictionSubmodule P j mu ↔
      ∀ h : H,
        P.operator (j h) v = (mu h : K) • v :=
  Iff.rfl

/-- On the selected scalar summand, rescaling changes the scalar at an
element in the image of `j` from `mu h` to `c (j h) * mu h`. -/
theorem rescale_restrictStable_operator_image
    {H : Type*} [Group H]
    (P : ProjectiveRepresentation K G V)
    (j : H →* G)
    (mu : H → Kˣ)
    (hstable :
      P.IsStable
        (scalarRestrictionSubmodule P j mu))
    (c : G → Kˣ)
    (h : H) :
    (((P.restrictStable
          (scalarRestrictionSubmodule P j mu)
          hstable).rescale c).operator (j h)) =
      scalarLinearEquiv K
        (scalarRestrictionSubmodule P j mu)
        (c (j h) * mu h) := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change
    (c (j h) : K) • P.operator (j h) (v : V) =
      ((c (j h) * mu h : Kˣ) : K) • (v : V)
  rw [v.property h, Units.val_mul, mul_smul]

/-- Regression criterion for quotient normalization on the selected
summand: the rescaled operator at `j h` is the identity exactly when the
rescaling cochain cancels the selected scalar.

In particular, exact quotient descent of a nontrivial `mu`-summand must not
be attempted before this inertia-level rescaling. -/
theorem rescale_restrictStable_operator_image_eq_one_iff
    {H : Type*} [Group H]
    (P : ProjectiveRepresentation K G V)
    (j : H →* G)
    (mu : H → Kˣ)
    (hstable :
      P.IsStable
        (scalarRestrictionSubmodule P j mu))
    (c : G → Kˣ)
    [Nontrivial (scalarRestrictionSubmodule P j mu)]
    (h : H) :
    (((P.restrictStable
          (scalarRestrictionSubmodule P j mu)
          hstable).rescale c).operator (j h) = 1) ↔
      c (j h) = (mu h)⁻¹ := by
  rw [rescale_restrictStable_operator_image,
    ← scalarLinearEquiv_one K
      (scalarRestrictionSubmodule P j mu),
    (scalarLinearEquiv_injective K
      (scalarRestrictionSubmodule P j mu)).eq_iff]
  exact mul_eq_one_iff_eq_inv

/-- Once the selected scalar eigenspace is stable under the full
projective action, its inherited projective representation has exactly the
original factor set. -/
theorem scalarRestrictionSubmodule_restrictStable_factorSet
    {H : Type*} [Group H]
    (P : ProjectiveRepresentation K G V)
    (j : H →* G)
    (mu : H → Kˣ)
    (hstable :
      P.IsStable
        (scalarRestrictionSubmodule P j mu))
    [Nontrivial V]
    [Nontrivial (scalarRestrictionSubmodule P j mu)] :
    (P.restrictStable
      (scalarRestrictionSubmodule P j mu)
      hstable).factorSet =
        P.factorSet :=
  P.restrictStable_factorSet
    (scalarRestrictionSubmodule P j mu) hstable

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
