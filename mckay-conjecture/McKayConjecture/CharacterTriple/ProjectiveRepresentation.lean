/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSet
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Projective representations

A projective representation is presented by invertible linear lifts `P(g)` and
nonzero scalar factors `α(g,h)` satisfying

`P(g) P(h) = α(g,h) P(gh)`.

The cocycle identity for `α` is *proved* from associativity.  Faithfulness of
the scalar embedding requires the representation space to be nonzero; this is
the only nondegeneracy hypothesis.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple

section ScalarAutomorphisms

variable (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V]

/-- Embed a nonzero scalar as the corresponding invertible linear map. -/
def scalarLinearEquiv : Kˣ →* (V ≃ₗ[K] V) :=
  DistribMulAction.toModuleAut K V

@[simp]
theorem scalarLinearEquiv_apply (a : Kˣ) (x : V) :
    scalarLinearEquiv K V a x = (a : K) • x :=
  rfl

@[simp]
theorem scalarLinearEquiv_one :
    scalarLinearEquiv K V 1 = 1 :=
  map_one _

@[simp]
theorem scalarLinearEquiv_mul (a b : Kˣ) :
    scalarLinearEquiv K V (a * b) =
      scalarLinearEquiv K V a * scalarLinearEquiv K V b :=
  map_mul _ _ _

/-- Scalar automorphisms commute with every linear automorphism. -/
theorem scalarLinearEquiv_comm (a : Kˣ) (f : V ≃ₗ[K] V) :
    scalarLinearEquiv K V a * f = f * scalarLinearEquiv K V a := by
  ext x
  change (a : K) • f x = f ((a : K) • x)
  exact (map_smul f (a : K) x).symm

/-- On a nonzero vector space, distinct units induce distinct scalar
automorphisms. -/
theorem scalarLinearEquiv_injective [Nontrivial V] :
    Function.Injective (scalarLinearEquiv K V) := by
  intro a b hab
  obtain ⟨x : V, hx⟩ := exists_ne (0 : V)
  apply Units.ext
  apply smul_left_injective K hx
  exact DFunLike.congr_fun hab x

end ScalarAutomorphisms

/-- A projective representation by chosen invertible linear lifts.

No cocycle law is included in the data: it follows from `map_mul` and
associativity when `V` is nonzero.
-/
structure ProjectiveRepresentation (K : Type u) (G : Type w) (V : Type v)
    [Field K] [Group G] [AddCommGroup V] [Module K V] where
  /-- The chosen invertible lift of each group element. -/
  operator : G → V ≃ₗ[K] V
  /-- The scalar discrepancy between multiplication of lifts and the lift of a product. -/
  factor : G → G → Kˣ
  /-- Multiplication of lifts is projective, with discrepancy `factor`. -/
  map_mul : ∀ g h : G,
    operator g * operator h =
      scalarLinearEquiv K V (factor g h) * operator (g * h)

namespace ProjectiveRepresentation

variable {K : Type u} {V : Type v} {G : Type w}
  [Field K] [AddCommGroup V] [Module K V] [Group G]

/-- An ordinary linear action, regarded as a projective representation with
constant-one factor. -/
def ofLinearAction (ρ : G →* (V ≃ₗ[K] V)) :
    ProjectiveRepresentation K G V where
  operator := ρ
  factor _ _ := 1
  map_mul g h := by
    simp

@[ext]
theorem ext {P Q : ProjectiveRepresentation K G V}
    (hoperator : P.operator = Q.operator) (hfactor : P.factor = Q.factor) :
    P = Q := by
  cases P
  cases Q
  simp_all

/-- The scalar attached to a projective multiplication law satisfies the
two-cocycle identity. -/
theorem factor_cocycle (P : ProjectiveRepresentation K G V) [Nontrivial V]
    (g h k : G) :
    P.factor (g * h) k * P.factor g h =
      P.factor h k * P.factor g (h * k) := by
  apply scalarLinearEquiv_injective K V
  rw [scalarLinearEquiv_mul, scalarLinearEquiv_mul]
  apply mul_right_cancel
  calc
    (scalarLinearEquiv K V (P.factor (g * h) k) *
          scalarLinearEquiv K V (P.factor g h)) *
        P.operator (g * (h * k)) =
      (scalarLinearEquiv K V (P.factor g h) *
          scalarLinearEquiv K V (P.factor (g * h) k)) *
        P.operator ((g * h) * k) := by
          rw [mul_assoc g h k]
          rw [scalarLinearEquiv_comm]
    _ = (scalarLinearEquiv K V (P.factor g h) * P.operator (g * h)) *
        P.operator k := by
          calc
            (scalarLinearEquiv K V (P.factor g h) *
                scalarLinearEquiv K V (P.factor (g * h) k)) *
                P.operator ((g * h) * k) =
              scalarLinearEquiv K V (P.factor g h) *
                (scalarLinearEquiv K V (P.factor (g * h) k) *
                  P.operator ((g * h) * k)) := mul_assoc _ _ _
            _ = scalarLinearEquiv K V (P.factor g h) *
                (P.operator (g * h) * P.operator k) := by
                  rw [P.map_mul (g * h) k]
            _ = (scalarLinearEquiv K V (P.factor g h) * P.operator (g * h)) *
                P.operator k := (mul_assoc _ _ _).symm
    _ = (P.operator g * P.operator h) * P.operator k := by
          rw [← P.map_mul g h]
    _ = P.operator g * (P.operator h * P.operator k) := mul_assoc _ _ _
    _ = P.operator g *
        (scalarLinearEquiv K V (P.factor h k) * P.operator (h * k)) := by
          rw [P.map_mul h k]
    _ = scalarLinearEquiv K V (P.factor h k) *
        (P.operator g * P.operator (h * k)) := by
          rw [← mul_assoc, ← scalarLinearEquiv_comm, mul_assoc]
    _ = scalarLinearEquiv K V (P.factor h k) *
        (scalarLinearEquiv K V (P.factor g (h * k)) *
          P.operator (g * (h * k))) := by
          rw [P.map_mul g (h * k)]
    _ = (scalarLinearEquiv K V (P.factor h k) *
          scalarLinearEquiv K V (P.factor g (h * k))) *
        P.operator (g * (h * k)) := by rw [mul_assoc]

/-- The factor set determined by a projective representation on a nonzero
space. -/
def factorSet (P : ProjectiveRepresentation K G V) [Nontrivial V] :
    FactorSet G Kˣ where
  toFun := P.factor
  cocycle' := P.factor_cocycle

@[simp]
theorem factorSet_apply (P : ProjectiveRepresentation K G V) [Nontrivial V]
    (g h : G) :
    P.factorSet g h = P.factor g h :=
  rfl

@[simp]
theorem ofLinearAction_factorSet (ρ : G →* (V ≃ₗ[K] V)) [Nontrivial V] :
    (ofLinearAction ρ).factorSet = FactorSet.one := by
  ext g h
  rfl

/-- Rescale the chosen lift of `g` by a nonzero scalar `c g`. -/
def rescale (P : ProjectiveRepresentation K G V) (c : G → Kˣ) :
    ProjectiveRepresentation K G V where
  operator g := scalarLinearEquiv K V (c g) * P.operator g
  factor g h := c g * c h / c (g * h) * P.factor g h
  map_mul g h := by
    calc
      (scalarLinearEquiv K V (c g) * P.operator g) *
          (scalarLinearEquiv K V (c h) * P.operator h) =
        scalarLinearEquiv K V (c g) *
          (P.operator g * scalarLinearEquiv K V (c h)) * P.operator h := by
            simp only [mul_assoc]
      _ = scalarLinearEquiv K V (c g) *
          (scalarLinearEquiv K V (c h) * P.operator g) * P.operator h := by
            rw [← scalarLinearEquiv_comm]
      _ = (scalarLinearEquiv K V (c g) * scalarLinearEquiv K V (c h)) *
          (P.operator g * P.operator h) := by simp only [mul_assoc]
      _ = (scalarLinearEquiv K V (c g) * scalarLinearEquiv K V (c h)) *
          (scalarLinearEquiv K V (P.factor g h) * P.operator (g * h)) := by
            rw [P.map_mul]
      _ = scalarLinearEquiv K V (c g * c h * P.factor g h) *
          P.operator (g * h) := by
            rw [scalarLinearEquiv_mul, scalarLinearEquiv_mul]
            simp only [mul_assoc]
      _ = scalarLinearEquiv K V
          ((c g * c h / c (g * h) * P.factor g h) * c (g * h)) *
          P.operator (g * h) := by
            congr 2
            simp only [div_eq_mul_inv]
            calc
              c g * c h * P.factor g h =
                  (c g * c h * P.factor g h) *
                    ((c (g * h))⁻¹ * c (g * h)) := by simp
              _ = c g * c h * (c (g * h))⁻¹ * P.factor g h * c (g * h) := by
                ac_rfl
      _ = scalarLinearEquiv K V (c g * c h / c (g * h) * P.factor g h) *
          (scalarLinearEquiv K V (c (g * h)) * P.operator (g * h)) := by
            rw [scalarLinearEquiv_mul, mul_assoc]

@[simp]
theorem rescale_operator (P : ProjectiveRepresentation K G V) (c : G → Kˣ) (g : G) :
    (P.rescale c).operator g = scalarLinearEquiv K V (c g) * P.operator g :=
  rfl

@[simp]
theorem rescale_factor (P : ProjectiveRepresentation K G V) (c : G → Kˣ) (g h : G) :
    (P.rescale c).factor g h = c g * c h / c (g * h) * P.factor g h :=
  rfl

/-- Rescaling chosen lifts performs the corresponding gauge transformation on
the factor set. -/
theorem rescale_factorSet (P : ProjectiveRepresentation K G V) [Nontrivial V]
    (c : G → Kˣ) :
    (P.rescale c).factorSet = P.factorSet.gauge c := by
  ext g h
  rfl

/-- Rescaling chosen lifts produces a cohomologous factor set. -/
theorem factorSet_cohomologous_rescale
    (P : ProjectiveRepresentation K G V) [Nontrivial V] (c : G → Kˣ) :
    P.factorSet.Cohomologous (P.rescale c).factorSet :=
  ⟨c, P.rescale_factorSet c⟩

/-- The lift of the identity is the scalar prescribed by `α(1,g)`. -/
theorem operator_one_eq_scalar_left (P : ProjectiveRepresentation K G V) (g : G) :
    P.operator 1 = scalarLinearEquiv K V (P.factor 1 g) := by
  calc
    P.operator 1 =
        (P.operator 1 * P.operator g) * (P.operator g)⁻¹ := by simp
    _ = (scalarLinearEquiv K V (P.factor 1 g) * P.operator g) *
        (P.operator g)⁻¹ := by rw [P.map_mul]; simp
    _ = scalarLinearEquiv K V (P.factor 1 g) := by simp

/-- The lift of the identity is also the scalar prescribed by `α(g,1)`. -/
theorem operator_one_eq_scalar_right (P : ProjectiveRepresentation K G V) (g : G) :
    P.operator 1 = scalarLinearEquiv K V (P.factor g 1) := by
  calc
    P.operator 1 =
        (P.operator g)⁻¹ * (P.operator g * P.operator 1) := by simp
    _ = (P.operator g)⁻¹ *
        (scalarLinearEquiv K V (P.factor g 1) * P.operator g) := by
          rw [P.map_mul]
          simp
    _ = (P.operator g)⁻¹ *
        (P.operator g * scalarLinearEquiv K V (P.factor g 1)) := by
          rw [scalarLinearEquiv_comm]
    _ = scalarLinearEquiv K V (P.factor g 1) := by simp

/-- A projective representation is normalized when its chosen lift of the
identity is the identity automorphism. -/
def IsNormalized (P : ProjectiveRepresentation K G V) : Prop :=
  P.operator 1 = 1

@[simp]
theorem ofLinearAction_isNormalized (ρ : G →* (V ≃ₗ[K] V)) :
    (ofLinearAction ρ).IsNormalized :=
  ρ.map_one

/-- Normalize a projective representation by multiplying every chosen lift by
the inverse of the scalar represented by its identity lift. -/
def normalize (P : ProjectiveRepresentation K G V) :
    ProjectiveRepresentation K G V :=
  P.rescale (fun _ ↦ (P.factor 1 1)⁻¹)

/-- The canonical rescaling `normalize` has identity lift equal to the identity. -/
theorem normalize_isNormalized (P : ProjectiveRepresentation K G V) :
    P.normalize.IsNormalized := by
  change scalarLinearEquiv K V (P.factor 1 1)⁻¹ * P.operator 1 = 1
  rw [P.operator_one_eq_scalar_left 1]
  rw [← scalarLinearEquiv_mul]
  simp

/-- Normalization changes the factor set only by a coboundary. -/
theorem factorSet_cohomologous_normalize
    (P : ProjectiveRepresentation K G V) [Nontrivial V] :
    P.factorSet.Cohomologous P.normalize.factorSet :=
  P.factorSet_cohomologous_rescale _

/-- A normalized projective representation has normalized factor set. -/
theorem factorSet_isNormalized (P : ProjectiveRepresentation K G V) [Nontrivial V]
    (hP : P.IsNormalized) :
    P.factorSet.IsNormalized := by
  constructor
  · intro g
    change P.factor 1 g = 1
    apply scalarLinearEquiv_injective K V
    rw [map_one]
    rw [← P.operator_one_eq_scalar_left g, hP]
  · intro g
    change P.factor g 1 = 1
    apply scalarLinearEquiv_injective K V
    rw [map_one]
    rw [← P.operator_one_eq_scalar_right g, hP]

/-- Normalization of the factor set forces the identity lift to be the identity. -/
theorem isNormalized_of_factorSet_isNormalized
    (P : ProjectiveRepresentation K G V) [Nontrivial V]
    (hα : P.factorSet.IsNormalized) :
    P.IsNormalized := by
  change P.operator 1 = 1
  rw [P.operator_one_eq_scalar_left 1]
  have hone : P.factor 1 1 = 1 := by
    simpa [factorSet] using hα.1 1
  rw [hone, map_one]

/-- Normalizing the chosen lifts is equivalent to normalizing their factor set. -/
theorem isNormalized_iff_factorSet_isNormalized
    (P : ProjectiveRepresentation K G V) [Nontrivial V] :
    P.IsNormalized ↔ P.factorSet.IsNormalized :=
  ⟨P.factorSet_isNormalized, P.isNormalized_of_factorSet_isNormalized⟩

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
