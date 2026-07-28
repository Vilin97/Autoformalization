/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanCyclicReduction
import McKayConjecture.Character.ClassFunctionPairing
import McKayConjecture.Character.TwistedInvariantTrace

/-!
# Cyclic Glauberman coefficients as finite-order traces

A Fourier coefficient of the determinant-normalized cyclic trace is the
trace of the cyclic intertwiner on an intertwiner space for the
fixed-point subgroup.  The induced operator has finite order.  This
identification is the algebraic-integrality half of the classical
Galois argument for cyclic Glauberman correspondence.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture

variable {G : Type} [Group G] [Finite G]
variable (K P : Subgroup G) [K.Normal]
variable [IsCyclic P]
variable {p : ℕ} [Fact p.Prime]

/-- Restrict an irreducible realization of `K` to the fixed-point
subgroup of an ambient element. -/
def cyclicFixedPointRepresentation
    (χ : IrreducibleCharacter K) (g : G) :
    Representation ℂ (cyclicFixedPoints K g) χ.realization :=
  χ.realization.ρ.comp
    (cyclicFixedPointsInclusion K g)

/-- The determinant-normalized cyclic intertwiner commutes with the
representation of the fixed-point subgroup. -/
theorem determinantNormalizedCyclicIntertwiner_commutes_fixedPoints
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    ∀ c :
        cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G),
      ((determinantNormalizedCyclicIntertwinerData
          K P hK hP θ).unit :
          Module.End ℂ θ.1.1.realization) ∘ₗ
          cyclicFixedPointRepresentation
            K θ.1.1
            ((cyclicSubgroupGenerator P : P) : G) c =
        cyclicFixedPointRepresentation
            K θ.1.1
            ((cyclicSubgroupGenerator P : P) : G) c ∘ₗ
          ((determinantNormalizedCyclicIntertwinerData
            K P hK hP θ).unit :
            Module.End ℂ θ.1.1.realization) := by
  intro c
  let g : G :=
    ((cyclicSubgroupGenerator P : P) : G)
  let d :=
    determinantNormalizedCyclicIntertwinerData
      K P hK hP θ
  let cK : K :=
    cyclicFixedPointsInclusion K g c
  have hfixed :
      RepresentationTheory.ClassFunction.conjByMulEquiv
          (K := G) (H := K) g cK =
        cK := by
    apply Subtype.ext
    change g * (c : G) * g⁻¹ = (c : G)
    have hcomm :
        (c : G) * g = g * (c : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        c.property.2
    rw [← hcomm]
    group
  have hintertwines := d.intertwines cK
  rw [hfixed] at hintertwines
  have hval := congrArg Units.val hintertwines
  change
    (d.unit : Module.End ℂ θ.1.1.realization) ∘ₗ
        θ.1.1.realization.ρ cK =
      θ.1.1.realization.ρ cK ∘ₗ
        (d.unit : Module.End ℂ θ.1.1.realization)
  simpa only [Units.val_mul,
    Representation.asGroupHom_apply,
    Module.End.mul_eq_comp] using hval

/-- The determinant-normalized cyclic intertwiner has order dividing
the order of the acting cyclic subgroup. -/
theorem determinantNormalizedCyclicIntertwiner_unit_pow_card_eq_one
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    (determinantNormalizedCyclicIntertwinerData
        K P hK hP θ).unit ^ Nat.card P =
      1 := by
  let g : P := cyclicSubgroupGenerator P
  let d :=
    determinantNormalizedCyclicIntertwinerData
      K P hK hP θ
  have hgpowP :
      g ^ Nat.card P = 1 :=
    pow_card_eq_one'
  have hgpowG :
      (g : G) ^ Nat.card P = 1 :=
    congrArg Subtype.val hgpowP
  have hmem :
      (g : G) ^ (Nat.card P : ℤ) ∈ K := by
    rw [zpow_natCast, hgpowG]
    exact K.one_mem
  have hnormalized :=
    d.normalized (Nat.card P : ℤ) hmem
  have hsub :
      (⟨(g : G) ^ (Nat.card P : ℤ), hmem⟩ : K) =
        1 := by
    apply Subtype.ext
    change
      (g : G) ^ (Nat.card P : ℤ) =
        ((1 : K) : G)
    simpa only [zpow_natCast, Subgroup.coe_one] using hgpowG
  rw [hsub, map_one] at hnormalized
  simpa only [d, g, zpow_natCast] using hnormalized

/-- The cyclic intertwiner, as an endomorphism, has finite order. -/
theorem determinantNormalizedCyclicIntertwiner_isOfFinOrder
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    IsOfFinOrder
      ((determinantNormalizedCyclicIntertwinerData
        K P hK hP θ).unit :
        Module.End ℂ θ.1.1.realization) := by
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨Nat.card P, Nat.card_pos, ?_⟩
  have hpow :=
    determinantNormalizedCyclicIntertwiner_unit_pow_card_eq_one
      K P hK hP θ
  exact congrArg Units.val hpow

/-- The finite-order endomorphism whose trace is the Fourier
coefficient indexed by `ψ`. -/
def determinantNormalizedCyclicCoefficientEndomorphism
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G))) :
    Module.End ℂ
      ((Representation.linHom
        ψ.realization.ρ
        (cyclicFixedPointRepresentation
          K θ.1.1
          ((cyclicSubgroupGenerator P : P) : G))).invariants) :=
  by
    letI : Fintype
        (cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G)) :=
      Fintype.ofFinite _
    exact
      Representation.twistedIntertwinerEndomorphism
        ψ.realization.ρ
        (cyclicFixedPointRepresentation
          K θ.1.1
          ((cyclicSubgroupGenerator P : P) : G))
        ((determinantNormalizedCyclicIntertwinerData
          K P hK hP θ).unit :
          Module.End ℂ θ.1.1.realization)
        (determinantNormalizedCyclicIntertwiner_commutes_fixedPoints
          K P hK hP θ)

/-- The coefficient endomorphism has finite order. -/
theorem determinantNormalizedCyclicCoefficientEndomorphism_isOfFinOrder
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G))) :
    IsOfFinOrder
      (determinantNormalizedCyclicCoefficientEndomorphism
        K P hK hP θ ψ) := by
  letI : Fintype
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)) :=
    Fintype.ofFinite _
  unfold determinantNormalizedCyclicCoefficientEndomorphism
  apply
    Representation.twistedIntertwinerEndomorphism_isOfFinOrder
  exact
    determinantNormalizedCyclicIntertwiner_isOfFinOrder
      K P hK hP θ

/-- The coefficient endomorphism has order dividing the order of the
acting cyclic subgroup, not merely some unspecified finite order. -/
theorem determinantNormalizedCyclicCoefficientEndomorphism_pow_card_eq_one
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G))) :
    (determinantNormalizedCyclicCoefficientEndomorphism
        K P hK hP θ ψ) ^ Nat.card P =
      1 := by
  letI : Fintype
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)) :=
    Fintype.ofFinite _
  unfold determinantNormalizedCyclicCoefficientEndomorphism
  apply
    Representation.twistedIntertwinerEndomorphism_pow_eq_one
  have hpow :=
    determinantNormalizedCyclicIntertwiner_unit_pow_card_eq_one
      K P hK hP θ
  exact congrArg Units.val hpow

/-- Every Fourier coefficient of the determinant-normalized cyclic
trace is the trace of its associated finite-order coefficient
endomorphism. -/
theorem normalizedPairing_determinantNormalizedCyclicTrace_eq_trace_coefficientEndomorphism
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G))) :
    ClassFunction.normalizedPairing
        (determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ)
        ψ.toClassFunction =
      LinearMap.trace ℂ
        ((Representation.linHom
          ψ.realization.ρ
          (cyclicFixedPointRepresentation
            K θ.1.1
            ((cyclicSubgroupGenerator P : P) : G))).invariants)
        (determinantNormalizedCyclicCoefficientEndomorphism
          K P hK hP θ ψ) := by
  letI : Fintype
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)) :=
    Fintype.ofFinite _
  have htrace :=
    Representation.twistedCharacterPairing_eq_trace
      ψ.realization.ρ
      (cyclicFixedPointRepresentation
        K θ.1.1
        ((cyclicSubgroupGenerator P : P) : G))
      ((determinantNormalizedCyclicIntertwinerData
        K P hK hP θ).unit :
        Module.End ℂ θ.1.1.realization)
      (determinantNormalizedCyclicIntertwiner_commutes_fixedPoints
        K P hK hP θ)
  rw [ClassFunction.normalizedPairing,
    LinearMap.mk₂_apply]
  simp_rw [IrreducibleCharacter.toClassFunction_apply,
    ← ψ.realization_character]
  change
    (Nat.card
        (cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G)) : ℂ)⁻¹ *
        ∑ c :
          cyclicFixedPoints K
            ((cyclicSubgroupGenerator P : P) : G),
          determinantNormalizedCyclicTrace
              K P hK hP hgenerate θ c *
            ψ.realization.character c⁻¹ =
      _
  unfold determinantNormalizedCyclicCoefficientEndomorphism
  rw [← htrace]
  congr 1
  apply Finset.sum_congr rfl
  intro c _hc
  rw [determinantNormalizedCyclicTrace,
    RepresentationTheory.cyclicTwistedTraceClassFunction_apply]
  rfl

end McKayConjecture
