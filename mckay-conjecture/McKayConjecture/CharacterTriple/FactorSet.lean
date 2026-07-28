/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Factor sets

This file defines multiplicative factor sets with trivial coefficient action.
This is the convention used by projective representations in ordinary
character theory.  It also defines changes of section (gauge transformations)
and the resulting cohomology relation.

The curried API in this file is deliberately independent of a global scalar
action instance.  `FactorSet.isMulCocycle₂` connects it to mathlib's
low-degree group-cohomology API.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace CharacterTriple

/-- The trivial multiplicative action of a monoid `G` on a commutative group `A`.

This is a named definition, not a global instance, to avoid competing with
nontrivial coefficient actions elsewhere.
-/
@[instance_reducible]
def trivialMulDistribMulAction (G : Type u) (A : Type v) [Monoid G] [CommGroup A] :
    MulDistribMulAction G A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- A multiplicative factor set for `G` with values in a commutative group `A`.

The coefficient action is trivial, so the cocycle identity is
`α(gh,k) α(g,h) = α(h,k) α(g,hk)`.
-/
structure FactorSet (G : Type u) (A : Type v) [Monoid G] [CommGroup A] where
  /-- The scalar attached to a pair of group elements. -/
  toFun : G → G → A
  /-- The multiplicative two-cocycle identity. -/
  cocycle' : ∀ g h k : G,
    toFun (g * h) k * toFun g h = toFun h k * toFun g (h * k)

namespace FactorSet

variable {G : Type u} {A : Type v} [Monoid G] [CommGroup A]

instance : CoeFun (FactorSet G A) (fun _ ↦ G → G → A) :=
  ⟨FactorSet.toFun⟩

@[ext]
theorem ext {α β : FactorSet G A} (h : ∀ g h, α g h = β g h) : α = β := by
  cases α
  cases β
  congr
  funext g k
  exact h g k

/-- The factor-set cocycle identity, in its character-theory convention. -/
theorem cocycle (α : FactorSet G A) (g h k : G) :
    α (g * h) k * α g h = α h k * α g (h * k) :=
  α.cocycle' g h k

/-- A factor set is normalized when it is one on every pair containing the identity. -/
def IsNormalized (α : FactorSet G A) : Prop :=
  (∀ g, α 1 g = 1) ∧ ∀ g, α g 1 = 1

/-- The constant-one factor set. -/
protected def one : FactorSet G A where
  toFun _ _ := 1
  cocycle' _ _ _ := by simp

@[simp]
theorem one_apply (g h : G) : FactorSet.one g h = (1 : A) :=
  rfl

theorem one_isNormalized : (FactorSet.one : FactorSet G A).IsNormalized := by
  exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Regard a factor set as a multiplicative two-cocycle in mathlib's convention,
using the trivial action on its coefficients. -/
theorem isMulCocycle₂ (α : FactorSet G A) :
    letI := trivialMulDistribMulAction G A
    groupCohomology.IsMulCocycle₂ (fun x : G × G ↦ α x.1 x.2) := by
  letI := trivialMulDistribMulAction G A
  intro g h k
  exact α.cocycle g h k

/-- Every value `α(1,g)` agrees with `α(1,1)`. -/
theorem one_left_eq (α : FactorSet G A) (g : G) :
    α 1 g = α 1 1 := by
  letI := trivialMulDistribMulAction G A
  exact groupCohomology.map_one_fst_of_isMulCocycle₂ α.isMulCocycle₂ g

/-- Every value `α(g,1)` agrees with `α(1,1)`. -/
theorem one_right_eq (α : FactorSet G A) (g : G) :
    α g 1 = α 1 1 := by
  letI := trivialMulDistribMulAction G A
  exact groupCohomology.map_one_snd_of_isMulCocycle₂ α.isMulCocycle₂ g

/-- For a factor set, normalization is equivalent to the single equation
`α(1,1) = 1`. -/
theorem isNormalized_iff_value_one_one (α : FactorSet G A) :
    α.IsNormalized ↔ α 1 1 = 1 := by
  constructor
  · exact fun h ↦ h.1 1
  · intro h
    exact ⟨fun g ↦ α.one_left_eq g ▸ h, fun g ↦ α.one_right_eq g ▸ h⟩

/-- Change a factor set by rescaling each chosen lift by `c g`.

For a projective representation with lifts `P(g)`, replacing `P(g)` by
`c(g)P(g)` changes `α` to
`c(g)c(h)c(gh)⁻¹ α(g,h)`.
-/
def gauge (c : G → A) (α : FactorSet G A) : FactorSet G A where
  toFun g h := c g * c h / c (g * h) * α g h
  cocycle' g h k := by
    rw [mul_assoc g h k]
    simp only [div_eq_mul_inv]
    calc
      c (g * h) * c k * (c (g * (h * k)))⁻¹ * α (g * h) k *
          (c g * c h * (c (g * h))⁻¹ * α g h) =
        c (g * h) * (c (g * h))⁻¹ *
          (c g * c h * c k * (c (g * (h * k)))⁻¹ *
            (α (g * h) k * α g h)) := by ac_rfl
      _ = c g * c h * c k * (c (g * (h * k)))⁻¹ *
          (α (g * h) k * α g h) := by simp
      _ = c g * c h * c k * (c (g * (h * k)))⁻¹ *
          (α h k * α g (h * k)) := by rw [α.cocycle]
      _ = c (h * k) * (c (h * k))⁻¹ *
          (c g * c h * c k * (c (g * (h * k)))⁻¹ *
            (α h k * α g (h * k))) := by simp
      _ = c h * c k * (c (h * k))⁻¹ * α h k *
          (c g * c (h * k) * (c (g * (h * k)))⁻¹ * α g (h * k)) := by ac_rfl

@[simp]
theorem gauge_apply (c : G → A) (α : FactorSet G A) (g h : G) :
    α.gauge c g h = c g * c h / c (g * h) * α g h :=
  rfl

@[simp]
theorem gauge_one (α : FactorSet G A) :
    α.gauge (fun _ ↦ 1) = α := by
  ext g h
  simp

/-- Successive changes of lifts multiply their rescaling functions. -/
theorem gauge_gauge (c d : G → A) (α : FactorSet G A) :
    (α.gauge c).gauge d = α.gauge (fun g ↦ d g * c g) := by
  ext g h
  simp only [gauge_apply, div_eq_mul_inv, mul_inv_rev]
  ac_rfl

/-- Rescaling by pointwise inverses reverses a change of lifts. -/
theorem gauge_inv (c : G → A) (α : FactorSet G A) :
    (α.gauge c).gauge (fun g ↦ (c g)⁻¹) = α := by
  rw [gauge_gauge]
  rw [show (fun g ↦ (c g)⁻¹ * c g) = (fun _ ↦ 1) by
    funext g
    simp]
  exact α.gauge_one

/-- The quotient of a gauge-transformed factor set by the original factor set
is a two-coboundary in mathlib's multiplicative convention. -/
theorem gauge_div_isMulCoboundary₂ (c : G → A) (α : FactorSet G A) :
    letI := trivialMulDistribMulAction G A
    groupCohomology.IsMulCoboundary₂
      (fun x : G × G ↦ α.gauge c x.1 x.2 / α x.1 x.2) := by
  letI := trivialMulDistribMulAction G A
  refine ⟨c, fun g h ↦ ?_⟩
  change c h / c (g * h) * c g =
    (c g * c h / c (g * h) * α g h) / α g h
  simp only [div_eq_mul_inv]
  rw [mul_inv_cancel_right]
  ac_rfl

/-- Two factor sets are cohomologous if one is obtained from the other by a
change of chosen lifts. -/
def Cohomologous (α β : FactorSet G A) : Prop :=
  ∃ c : G → A, β = α.gauge c

theorem cohomologous_refl (α : FactorSet G A) : α.Cohomologous α :=
  ⟨fun _ ↦ 1, α.gauge_one.symm⟩

theorem cohomologous_symm {α β : FactorSet G A} :
    α.Cohomologous β → β.Cohomologous α := by
  rintro ⟨c, rfl⟩
  exact ⟨fun g ↦ (c g)⁻¹, (α.gauge_inv c).symm⟩

theorem cohomologous_trans {α β γ : FactorSet G A} :
    α.Cohomologous β → β.Cohomologous γ → α.Cohomologous γ := by
  rintro ⟨c, rfl⟩ ⟨d, rfl⟩
  exact ⟨fun g ↦ d g * c g, α.gauge_gauge c d⟩

/-- Cohomology of factor sets is an equivalence relation. -/
theorem cohomologous_equivalence : Equivalence (Cohomologous (G := G) (A := A)) :=
  ⟨cohomologous_refl, cohomologous_symm, cohomologous_trans⟩

/-- The setoid whose classes are multiplicative `H²` classes represented by factor sets. -/
def cohomologySetoid : Setoid (FactorSet G A) :=
  ⟨Cohomologous, cohomologous_equivalence⟩

theorem gauge_isNormalized (α : FactorSet G A) (c : G → A)
    (hα : α.IsNormalized) (hc : c 1 = 1) :
    (α.gauge c).IsNormalized := by
  constructor
  · intro g
    simp [hα.1 g, hc]
  · intro g
    simp [hα.2 g, hc]

end FactorSet

/-! Mathlib's explicit low-degree cocycle modules currently put the coefficient
ring and the acting group in the same universe.  The following bridge therefore
lives in `Type`; the proposition-level bridge `FactorSet.isMulCocycle₂` above is
universe-polymorphic. -/

namespace FactorSet

variable {G A : Type} [Group G] [CommGroup A]

/-- A factor set as an element of mathlib's module of multiplicative
two-cocycles (written additively on `Additive A`). -/
def toMathlibCocycle (α : FactorSet G A) :
    letI := trivialMulDistribMulAction G A
    groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction G A) := by
  letI := trivialMulDistribMulAction G A
  exact groupCohomology.cocyclesOfIsMulCocycle₂ α.isMulCocycle₂

@[simp]
theorem toMathlibCocycle_apply (α : FactorSet G A) (g h : G) :
    letI := trivialMulDistribMulAction G A
    (α.toMathlibCocycle : G × G → Additive A) (g, h) = Additive.ofMul (α g h) := by
  rfl

end FactorSet
end CharacterTriple
end McKayConjecture
