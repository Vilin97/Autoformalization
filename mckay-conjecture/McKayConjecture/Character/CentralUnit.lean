/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalar
import McKayConjecture.CharacterTriple.AssociatedExistence

/-!
# Canonical units attached to central character actions

A central element acts by a nonzero scalar in an irreducible
representation.  This file packages that scalar as an element of `ℂˣ`.
It also records that a cross-multiplied equality of normalized central
character values makes the two resulting units equal.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

open CharacterTriple

variable {G : Type*} [Group G]

/-- The nonzero scalar by which a specified central element acts. -/
def centralUnit
    (χ : IrreducibleCharacter G)
    (z : G) (hz : z ∈ Subgroup.center G) : ℂˣ := by
  let c : ℂ :=
    Classical.choose
      (χ.exists_realization_scalar_of_mem_center z hz)
  have hc :
      χ.realization.ρ z =
        c • (LinearMap.id : Module.End ℂ χ.realization) :=
    Classical.choose_spec
      (χ.exists_realization_scalar_of_mem_center z hz)
  have hc0 : c ≠ 0 := by
    intro hc0
    obtain ⟨v, hv⟩ :=
      exists_ne (0 : χ.realization)
    have hvzero :
        χ.realization.ρ z v = 0 := by
      rw [hc, hc0]
      simp
    apply hv
    exact
      (AssociatedExistence.realizationAction χ z).injective
        (by simpa using hvzero)
  exact Units.mk0 c hc0

/-- The canonical realization action of a central element is its
`centralUnit` scalar. -/
theorem realizationAction_eq_centralUnit
    (χ : IrreducibleCharacter G)
    (z : G) (hz : z ∈ Subgroup.center G) :
    AssociatedExistence.realizationAction χ z =
      scalarLinearEquiv ℂ χ.realization
        (χ.centralUnit z hz) := by
  let c : ℂ :=
    Classical.choose
      (χ.exists_realization_scalar_of_mem_center z hz)
  have hc :
      χ.realization.ρ z =
        c • (LinearMap.id : Module.End ℂ χ.realization) :=
    Classical.choose_spec
      (χ.exists_realization_scalar_of_mem_center z hz)
  ext v
  change χ.realization.ρ z v =
    (χ.centralUnit z hz : ℂ) • v
  have hv := LinearMap.congr_fun hc v
  change χ.realization.ρ z v = c • v at hv
  exact hv.trans (by congr)

/-- The value at a central element is its canonical unit times the
character degree. -/
theorem values_eq_centralUnit_mul_degree
    (χ : IrreducibleCharacter G)
    (z : G) (hz : z ∈ Subgroup.center G) :
  χ.values z =
      (χ.centralUnit z hz : ℂ) * (χ.degree : ℂ) := by
  apply χ.values_eq_scalar_mul_degree
  simpa [centralUnit] using
    (Classical.choose_spec
      (χ.exists_realization_scalar_of_mem_center z hz))

@[simp]
theorem centralUnit_one
    (χ : IrreducibleCharacter G) :
    χ.centralUnit 1 (Subgroup.one_mem _) = 1 := by
  apply scalarLinearEquiv_injective ℂ χ.realization
  rw [← χ.realizationAction_eq_centralUnit 1 (Subgroup.one_mem _)]
  simpa using map_one (AssociatedExistence.realizationAction χ)

/-- Canonical central units multiply with their central elements. -/
theorem centralUnit_mul
    (χ : IrreducibleCharacter G)
    (a b : G)
    (ha : a ∈ Subgroup.center G)
    (hb : b ∈ Subgroup.center G) :
    χ.centralUnit (a * b) (mul_mem ha hb) =
      χ.centralUnit a ha * χ.centralUnit b hb := by
  apply scalarLinearEquiv_injective ℂ χ.realization
  rw [scalarLinearEquiv_mul,
    ← χ.realizationAction_eq_centralUnit a ha,
    ← χ.realizationAction_eq_centralUnit b hb,
    ← χ.realizationAction_eq_centralUnit (a * b) (mul_mem ha hb)]
  exact map_mul (AssociatedExistence.realizationAction χ) a b

/-- Canonical central units commute with taking natural powers. -/
theorem centralUnit_pow
    (χ : IrreducibleCharacter G)
    (z : G)
    (hz : z ∈ Subgroup.center G)
    (n : ℕ) :
    χ.centralUnit (z ^ n) (pow_mem hz n) =
      (χ.centralUnit z hz) ^ n := by
  induction n with
  | zero =>
      simpa using χ.centralUnit_one
  | succ n ih =>
      simpa only [pow_succ] using
        (χ.centralUnit_mul (z ^ n) z
          (pow_mem hz n) hz).trans
          (congrArg (· * χ.centralUnit z hz) ih)

/-- `centralUnit` is independent of how an equal central element is
presented (and of the proof of centrality). -/
theorem centralUnit_congr
    (χ : IrreducibleCharacter G)
    {z w : G}
    (hz : z ∈ Subgroup.center G)
    (hw : w ∈ Subgroup.center G)
    (h : z = w) :
    χ.centralUnit z hz = χ.centralUnit w hw := by
  subst w
  rfl

variable {H : Type*} [Group H]

/-- Equality of normalized central values identifies the two canonical
central units, even when the character degrees differ. -/
theorem centralUnit_eq_of_cross
    (χ : IrreducibleCharacter G)
    (ψ : IrreducibleCharacter H)
    (z : G) (w : H)
    (hz : z ∈ Subgroup.center G)
    (hw : w ∈ Subgroup.center H)
    (hcross :
      χ.values z * (ψ.degree : ℂ) =
        ψ.values w * (χ.degree : ℂ)) :
    χ.centralUnit z hz = ψ.centralUnit w hw := by
  apply Units.ext
  rw [χ.values_eq_centralUnit_mul_degree z hz,
    ψ.values_eq_centralUnit_mul_degree w hw] at hcross
  have hχ : (χ.degree : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr χ.degree_ne_zero
  have hψ : (ψ.degree : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr ψ.degree_ne_zero
  apply mul_left_cancel₀ (mul_ne_zero hχ hψ)
  calc
    (χ.degree : ℂ) * (ψ.degree : ℂ) *
          (χ.centralUnit z hz : ℂ) =
        ((χ.centralUnit z hz : ℂ) *
            (χ.degree : ℂ)) *
          (ψ.degree : ℂ) := by ring
    _ =
        ((ψ.centralUnit w hw : ℂ) *
            (ψ.degree : ℂ)) *
          (χ.degree : ℂ) := hcross
    _ =
        (χ.degree : ℂ) * (ψ.degree : ℂ) *
          (ψ.centralUnit w hw : ℂ) := by ring

/-- Equality of canonical central units implies the corresponding
cross-multiplied equality of normalized character values. -/
theorem cross_of_centralUnit_eq
    (χ : IrreducibleCharacter G)
    (ψ : IrreducibleCharacter H)
    (z : G) (w : H)
    (hz : z ∈ Subgroup.center G)
    (hw : w ∈ Subgroup.center H)
    (hunit :
      χ.centralUnit z hz = ψ.centralUnit w hw) :
    χ.values z * (ψ.degree : ℂ) =
      ψ.values w * (χ.degree : ℂ) := by
  rw [χ.values_eq_centralUnit_mul_degree z hz,
    ψ.values_eq_centralUnit_mul_degree w hw, hunit]
  ring

/-- An extension has the same canonical central scalar as the character
being extended, provided both the source element and its image are central.
-/
theorem IsExtensionAlong.centralUnit_eq
    {f : H →* G}
    {χ : IrreducibleCharacter H}
    {ψ : IrreducibleCharacter G}
    (hψ : IsExtensionAlong f χ ψ)
    (z : H)
    (hz : z ∈ Subgroup.center H)
    (hfz : f z ∈ Subgroup.center G) :
    ψ.centralUnit (f z) hfz = χ.centralUnit z hz := by
  apply ψ.centralUnit_eq_of_cross χ (f z) z hfz hz
  rw [hψ z, hψ.degree_eq]

/-- Equality of normalized central values gives a literal common scalar
for the two canonical realization actions. -/
theorem realizationAction_eq_commonCentralUnit_of_cross
    (χ : IrreducibleCharacter G)
    (ψ : IrreducibleCharacter H)
    (z : G) (w : H)
    (hz : z ∈ Subgroup.center G)
    (hw : w ∈ Subgroup.center H)
    (hcross :
      χ.values z * (ψ.degree : ℂ) =
        ψ.values w * (χ.degree : ℂ)) :
    AssociatedExistence.realizationAction ψ w =
      scalarLinearEquiv ℂ ψ.realization
        (χ.centralUnit z hz) := by
  rw [ψ.realizationAction_eq_centralUnit w hw,
    χ.centralUnit_eq_of_cross ψ z w hz hw hcross]

end IrreducibleCharacter
end McKayConjecture
