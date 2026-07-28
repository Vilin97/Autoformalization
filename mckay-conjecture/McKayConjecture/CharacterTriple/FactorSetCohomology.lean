/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSet

/-!
# Cohomology classes of factor sets

This file sends a multiplicative factor set to mathlib's second group
cohomology group and proves that changing the chosen lifts does not change the
resulting class.

Mathlib's current low-degree API requires the coefficient ring and acting
group to lie in the same universe.  Since multiplicative coefficients are
linearized over `ℤ`, this bridge is stated for `G, A : Type`.  The underlying
cocycle and coboundary propositions in `FactorSet.lean` remain
universe-polymorphic.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

variable {G A : Type} [Group G] [CommGroup A]

/-- The class in `H²(G, A)` represented by a multiplicative factor set, with
`A` carrying the trivial `G`-action. -/
def h2Class (α : FactorSet G A) :
    letI := trivialMulDistribMulAction G A
    groupCohomology.H2 (Rep.ofMulDistribMulAction G A) := by
  letI := trivialMulDistribMulAction G A
  exact groupCohomology.H2π _ α.toMathlibCocycle

/-- The constant-one factor set represents the zero class in `H²`. -/
theorem h2Class_one :
    letI := trivialMulDistribMulAction G A
    (FactorSet.one : FactorSet G A).h2Class = 0 := by
  letI := trivialMulDistribMulAction G A
  unfold h2Class
  have hone :
      (FactorSet.one : FactorSet G A).toMathlibCocycle = 0 := by
    apply Subtype.ext
    funext x
    rcases x with ⟨g, h⟩
    rfl
  rw [hone]
  exact map_zero _

/-- A gauge transformation does not alter the represented `H²` class. -/
theorem h2Class_gauge (α : FactorSet G A) (c : G → A) :
    letI := trivialMulDistribMulAction G A
    (α.gauge c).h2Class = α.h2Class := by
  letI := trivialMulDistribMulAction G A
  apply (groupCohomology.H2π_eq_iff
    (A := Rep.ofMulDistribMulAction G A)
    (α.gauge c).toMathlibCocycle α.toMathlibCocycle).2
  change
    (fun x : G × G ↦
      Additive.ofMul (α.gauge c x.1 x.2 / α x.1 x.2)) ∈
        groupCohomology.coboundaries₂ (Rep.ofMulDistribMulAction G A)
  exact (groupCohomology.coboundariesOfIsMulCoboundary₂
    (α.gauge_div_isMulCoboundary₂ c)).2

/-- Cohomologous factor sets determine equal classes in mathlib's `H²`. -/
theorem h2Class_eq_of_cohomologous {α β : FactorSet G A}
    (h : α.Cohomologous β) :
    letI := trivialMulDistribMulAction G A
    α.h2Class = β.h2Class := by
  letI := trivialMulDistribMulAction G A
  rcases h with ⟨c, rfl⟩
  exact (α.h2Class_gauge c).symm

/-- Equality in mathlib's `H²` is also sufficient for two factor sets to
be related by a gauge transformation.  Thus the explicit character-theory
notion `Cohomologous` agrees exactly with equality of the represented
cohomology classes. -/
theorem cohomologous_of_h2Class_eq {α β : FactorSet G A}
    (h :
      letI := trivialMulDistribMulAction G A
      α.h2Class = β.h2Class) :
    α.Cohomologous β := by
  letI := trivialMulDistribMulAction G A
  have hcoboundary :
      (fun x : G × G ↦
        Additive.ofMul (α x.1 x.2 / β x.1 x.2)) ∈
          groupCohomology.coboundaries₂
            (Rep.ofMulDistribMulAction G A) := by
    exact
      (groupCohomology.H2π_eq_iff
        (A := Rep.ofMulDistribMulAction G A)
        α.toMathlibCocycle β.toMathlibCocycle).1 h
  have hmul :
      groupCohomology.IsMulCoboundary₂
        (fun x : G × G ↦ α x.1 x.2 / β x.1 x.2) := by
    have hraw :=
      groupCohomology.isMulCoboundary₂_of_mem_coboundaries₂
        (fun x : G × G ↦
          α x.1 x.2 / β x.1 x.2)
        hcoboundary
    change
      groupCohomology.IsMulCoboundary₂
        (fun x : G × G ↦ α x.1 x.2 / β x.1 x.2) at hraw
    exact hraw
  obtain ⟨c, hc⟩ := hmul
  apply cohomologous_symm
  refine ⟨c, ?_⟩
  ext g k
  have hcgk := hc g k
  change
    c k / c (g * k) * c g =
      α g k / β g k at hcgk
  change α g k = c g * c k / c (g * k) * β g k
  calc
    α g k = (α g k / β g k) * β g k := by simp
    _ = (c k / c (g * k) * c g) * β g k := by rw [← hcgk]
    _ = c g * c k / c (g * k) * β g k := by
      apply congrArg (fun z : A ↦ z * β g k)
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Explicit gauge cohomology is equivalent to equality of `H²` classes. -/
theorem cohomologous_iff_h2Class_eq {α β : FactorSet G A} :
    α.Cohomologous β ↔
      letI := trivialMulDistribMulAction G A
      α.h2Class = β.h2Class :=
  ⟨h2Class_eq_of_cohomologous, cohomologous_of_h2Class_eq⟩

end FactorSet
end CharacterTriple
end McKayConjecture
