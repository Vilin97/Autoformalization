/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import SplittingSpheres.Foundations.TopologicalCyclicCover

/-!
# Identifying the cyclic-cover fiber with `ZMod m`

The subgroup quotient classified by the cyclic character has a distinguished fiber over the
basepoint.  Orbit--stabilizer identifies this fiber with the quotient of the fundamental group by
the recovered subgroup, and the first isomorphism theorem identifies that quotient with `ZMod m`.
The resulting equivalence is compatible with monodromy: a loop acts by its cyclic character.
-/

@[expose] public section

open scoped Multiplicative

noncomputable section

namespace SplittingSpheres

universe uX

variable {X : Type uX} [TopologicalSpace X] (x₀ : X)

/-- The cyclic character transported to the fundamental group of the base. -/
def cyclicCharacterFundamentalGroup
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) :
    FundamentalGroup X x₀ →* Multiplicative (ZMod m) :=
  (cyclicCharacter m).comp π.toMonoidHom

/-- Its kernel is exactly the subgroup used to define the cyclic cover. -/
theorem cyclicCharacterFundamentalGroup_ker
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) :
    (cyclicCharacterFundamentalGroup x₀ π m).ker = cyclicCoverSubgroup x₀ π m := by
  ext γ
  rfl

/-- The transported cyclic character remains onto. -/
theorem cyclicCharacterFundamentalGroup_surjective
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) :
    Function.Surjective (cyclicCharacterFundamentalGroup x₀ π m) := by
  intro z
  obtain ⟨w, hw⟩ := cyclicCharacter_surjective m z
  obtain ⟨γ, hγ⟩ := π.surjective w
  refine ⟨γ, ?_⟩
  change cyclicCharacter m (π γ) = z
  rwa [hγ]

/-- The quotient of the fundamental group by the cyclic-cover subgroup is the cyclic group. -/
def cyclicFundamentalGroupQuotientEquiv
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) :
    FundamentalGroup X x₀ ⧸ cyclicCoverSubgroup x₀ π m ≃*
      Multiplicative (ZMod m) :=
  (QuotientGroup.quotientMulEquivOfEq
      (cyclicCharacterFundamentalGroup_ker x₀ π m).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (cyclicCharacterFundamentalGroup x₀ π m)
      (cyclicCharacterFundamentalGroup_surjective x₀ π m))

@[simp]
theorem cyclicFundamentalGroupQuotientEquiv_mk
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ)
    (γ : FundamentalGroup X x₀) :
    cyclicFundamentalGroupQuotientEquiv x₀ π m (QuotientGroup.mk γ) =
      cyclicCharacterFundamentalGroup x₀ π m γ := by
  rfl

variable [LocallyPathConnectedSpace X] [PathConnectedSpace X]
  [TauCeti.SemilocallySimplyConnectedSpace X]

/-- Distinguished lift of `x₀` in the raw subgroup-quotient cyclic cover. -/
abbrev cyclicCoverFiberBasepoint
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) :
    TauCeti.UniversalCover.subgroupQuotientProj x₀ (cyclicCoverSubgroup x₀ π m) ⁻¹'
      {x₀} :=
  ⟨TauCeti.UniversalCover.SubgroupQuotient.basepoint x₀ (cyclicCoverSubgroup x₀ π m),
    TauCeti.UniversalCover.subgroupQuotientProj_basepoint x₀
      (cyclicCoverSubgroup x₀ π m)⟩

/-- The recovered subgroup at the distinguished lift is the defining cyclic-cover subgroup. -/
theorem range_mapOfEq_cyclicCoverBasepoint
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) :
    (FundamentalGroup.mapOfEq
      ⟨TauCeti.UniversalCover.subgroupQuotientProj x₀ (cyclicCoverSubgroup x₀ π m),
        TauCeti.UniversalCover.continuous_subgroupQuotientProj x₀
          (cyclicCoverSubgroup x₀ π m)⟩
      (cyclicCoverFiberBasepoint x₀ π m).2).range = cyclicCoverSubgroup x₀ π m := by
  simpa only [cyclicCoverFiberBasepoint] using
    TauCeti.UniversalCover.range_mapOfEq_subgroupQuotientProj x₀
      (cyclicCoverSubgroup x₀ π m)

/-- Canonical identification of the distinguished fiber with `ZMod m`. -/
def cyclicCoverFiberEquiv
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) :
    (TauCeti.UniversalCover.subgroupQuotientProj x₀ (cyclicCoverSubgroup x₀ π m) ⁻¹'
      {x₀}) ≃ ZMod m :=
  (((TauCeti.IsCoveringMap.fiberEquivQuotientRange
        (TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀
          (cyclicCoverSubgroup x₀ π m))
        (cyclicCoverFiberBasepoint x₀ π m)).trans
      (Subgroup.quotientEquivOfEq (range_mapOfEq_cyclicCoverBasepoint x₀ π m))).trans
    (cyclicFundamentalGroupQuotientEquiv x₀ π m).toEquiv).trans
  Multiplicative.toAdd

/-- Under the fiber identification, monodromy by `γ` is the value of the cyclic character on
`γ`. -/
theorem cyclicCoverFiberEquiv_monodromy
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ)
    (γ : FundamentalGroup X x₀) :
    cyclicCoverFiberEquiv x₀ π m
      ((TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀
        (cyclicCoverSubgroup x₀ π m)).monodromy γ
        (cyclicCoverFiberBasepoint x₀ π m)) =
      (cyclicCharacterFundamentalGroup x₀ π m γ).toAdd := by
  let hp := TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀
    (cyclicCoverSubgroup x₀ π m)
  let e := cyclicCoverFiberBasepoint x₀ π m
  have hquot : TauCeti.IsCoveringMap.fiberEquivQuotientRange hp e (hp.monodromy γ e) =
      QuotientGroup.mk γ := by
    exact (TauCeti.IsCoveringMap.fiberEquivQuotientRange hp e).eq_symm_apply.mp
      (TauCeti.IsCoveringMap.fiberEquivQuotientRange_symm_apply_mk hp e γ).symm
  change cyclicCoverFiberEquiv x₀ π m (hp.monodromy γ e) = _
  simp only [cyclicCoverFiberEquiv, Equiv.trans_apply]
  rw [hquot, Subgroup.quotientEquivOfEq_mk]
  exact congrArg Multiplicative.toAdd
    (cyclicFundamentalGroupQuotientEquiv_mk x₀ π m γ)

end SplittingSpheres
