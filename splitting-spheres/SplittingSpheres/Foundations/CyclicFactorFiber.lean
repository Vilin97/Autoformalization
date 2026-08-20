/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CyclicFiber
public import SplittingSpheres.Foundations.TopologicalCyclicFactor
public import TauCeti.Topology.Homotopy.Monodromy.Functoriality

/-!
# Factor maps on fibers of cyclic covers

For `k ∣ m`, the canonical pointed map from the `m`-fold cyclic cover to the `k`-fold cyclic
cover restricts on the distinguished fiber to reduction modulo `k`.  The proof uses functoriality
of covering-space monodromy and the explicit identification of each fiber with `ZMod`.
-/

@[expose] public section

noncomputable section

namespace SplittingSpheres

universe uX

variable {X : Type uX} [TopologicalSpace X] (x₀ : X)
  [LocallyPathConnectedSpace X] [PathConnectedSpace X]
  [TauCeti.SemilocallySimplyConnectedSpace X]

/-- Restriction of a divisibility factor map to the fiber over the common basepoint. -/
def cyclicCoverFactorFiber
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2))
    {k m : ℕ} (h : k ∣ m) :
    cyclicCoverProj x₀ π m ⁻¹' {x₀} → cyclicCoverProj x₀ π k ⁻¹' {x₀} :=
  TauCeti.IsCoveringMap.fiberMap (cyclicCoverFactor x₀ π h)
    (cyclicCoverProj_comp_factor x₀ π h) x₀

/-- The restricted factor map carries the distinguished point to the distinguished point. -/
@[simp]
theorem cyclicCoverFactorFiber_basepoint
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2))
    {k m : ℕ} (h : k ∣ m) :
    cyclicCoverFactorFiber x₀ π h (cyclicCoverFiberBasepoint x₀ π m) =
      cyclicCoverFiberBasepoint x₀ π k := by
  apply Subtype.ext
  simpa only [cyclicCoverFactorFiber,
    TauCeti.IsCoveringMap.fiberMap_apply_coe] using
    cyclicCoverFactor_basepoint x₀ π h

/-- The restricted factor map intertwines monodromy, specialized to the distinguished lift. -/
theorem cyclicCoverFactorFiber_monodromy
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2))
    {k m : ℕ} (h : k ∣ m) (γ : FundamentalGroup X x₀) :
    cyclicCoverFactorFiber x₀ π h
        ((TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀
          (cyclicCoverSubgroup x₀ π m)).monodromy γ
          (cyclicCoverFiberBasepoint x₀ π m)) =
      (TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀
        (cyclicCoverSubgroup x₀ π k)).monodromy γ
        (cyclicCoverFiberBasepoint x₀ π k) := by
  have hmon := TauCeti.IsCoveringMap.fiberMap_monodromy
    (TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀
      (cyclicCoverSubgroup x₀ π m))
    (TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀
      (cyclicCoverSubgroup x₀ π k))
    (cyclicCoverFactor x₀ π h) (cyclicCoverProj_comp_factor x₀ π h) γ
    (cyclicCoverFiberBasepoint x₀ π m)
  change cyclicCoverFactorFiber x₀ π h
      ((TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀
        (cyclicCoverSubgroup x₀ π m)).monodromy γ
        (cyclicCoverFiberBasepoint x₀ π m)) =
      (TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀
        (cyclicCoverSubgroup x₀ π k)).monodromy γ
        (cyclicCoverFactorFiber x₀ π h
          (cyclicCoverFiberBasepoint x₀ π m)) at hmon
  rw [cyclicCoverFactorFiber_basepoint x₀ π h] at hmon
  exact hmon

/-- On a monodromy translate of the distinguished lift, the factor map is reduction modulo
`k`. -/
theorem cyclicCoverFiberEquiv_factor_monodromy
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2))
    {k m : ℕ} (h : k ∣ m) (γ : FundamentalGroup X x₀) :
    cyclicCoverFiberEquiv x₀ π k
        (cyclicCoverFactorFiber x₀ π h
          ((TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀
            (cyclicCoverSubgroup x₀ π m)).monodromy γ
            (cyclicCoverFiberBasepoint x₀ π m))) =
      ZMod.castHom h (ZMod k)
        (cyclicCoverFiberEquiv x₀ π m
          ((TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀
            (cyclicCoverSubgroup x₀ π m)).monodromy γ
            (cyclicCoverFiberBasepoint x₀ π m))) := by
  rw [cyclicCoverFactorFiber_monodromy x₀ π h γ,
    cyclicCoverFiberEquiv_monodromy, cyclicCoverFiberEquiv_monodromy]
  have hchar := DFunLike.congr_fun
    (cyclicReduction_comp_cyclicCharacter h) (π γ)
  exact (congrArg Multiplicative.toAdd hchar).symm

/-- Under the canonical fiber identifications, every cyclic-cover factor map is exactly the
standard reduction homomorphism `ZMod m → ZMod k`. -/
theorem cyclicCoverFiberEquiv_factor
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2))
    {k m : ℕ} (h : k ∣ m)
    (z : cyclicCoverProj x₀ π m ⁻¹' {x₀}) :
    cyclicCoverFiberEquiv x₀ π k (cyclicCoverFactorFiber x₀ π h z) =
      ZMod.castHom h (ZMod k) (cyclicCoverFiberEquiv x₀ π m z) := by
  obtain ⟨γ, hγ⟩ := cyclicCharacterFundamentalGroup_surjective x₀ π m
    (Multiplicative.ofAdd (cyclicCoverFiberEquiv x₀ π m z))
  have hγ' : (cyclicCharacterFundamentalGroup x₀ π m γ).toAdd =
      cyclicCoverFiberEquiv x₀ π m z := by
    simpa using congrArg Multiplicative.toAdd hγ
  have hz :
      (TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀
        (cyclicCoverSubgroup x₀ π m)).monodromy γ
          (cyclicCoverFiberBasepoint x₀ π m) = z := by
    apply (cyclicCoverFiberEquiv x₀ π m).injective
    rw [cyclicCoverFiberEquiv_monodromy, hγ']
  rw [← hz]
  exact cyclicCoverFiberEquiv_factor_monodromy x₀ π h γ

end SplittingSpheres
