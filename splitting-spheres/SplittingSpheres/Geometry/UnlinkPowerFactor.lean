/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkPowerDeck

/-!
# Factor maps between unlink power pullbacks

If `n = m * q`, raising the power coordinate to the `q`-th power gives a map from the
`n`-th power pullback to the `m`-th power pullback.  This file constructs that map directly,
proves its continuity and functorial laws, and records its equivariance for the displayed
roots-of-unity deck actions.

The construction makes sense for all natural numbers, including zero: no covering-map or
sheet-cardinality conclusion is drawn without a nonzero-degree hypothesis.  Only continuity is
asserted; no smoothness of the factor map with respect to the pulled-back atlases is claimed.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-- Raising the power coordinate to the quotient exponent gives the concrete factor map from
degree `n` to degree `m` when `n = m * q`.  The equality witness is used only to prove the
pullback equation. -/
def standardUnlinkPowerFactorMap {n m q : ℕ} (hnm : n = m * q)
    (z : StandardUnlinkPowerPullback n) : StandardUnlinkPowerPullback m :=
  ⟨(z.1.1, ⟨z.1.2.1 ^ q, pow_ne_zero q z.1.2.2⟩), by
    apply Subtype.ext
    change (standardUnlinkRightNormalMap z.1.1 : ℂ) = (z.1.2.1 ^ q) ^ m
    calc
      (standardUnlinkRightNormalMap z.1.1 : ℂ) = z.1.2.1 ^ n :=
        congrArg Subtype.val z.2
      _ = z.1.2.1 ^ (q * m) :=
        congrArg (fun e : ℕ ↦ z.1.2.1 ^ e)
          (hnm.trans (Nat.mul_comm m q))
      _ = (z.1.2.1 ^ q) ^ m := pow_mul _ _ _⟩

@[simp]
theorem standardUnlinkPowerFactorMap_base {n m q : ℕ} (hnm : n = m * q)
    (z : StandardUnlinkPowerPullback n) :
    (standardUnlinkPowerFactorMap hnm z).1.1 = z.1.1 :=
  rfl

@[simp]
theorem standardUnlinkPowerFactorMap_powerCoordinate {n m q : ℕ}
    (hnm : n = m * q) (z : StandardUnlinkPowerPullback n) :
    ((standardUnlinkPowerFactorMap hnm z).1.2 : ℂ) = z.1.2.1 ^ q :=
  rfl

/-- The factor map lies over the identity of the strict unlink complement. -/
@[simp]
theorem standardUnlinkPowerFactorMap_proj {n m q : ℕ} (hnm : n = m * q)
    (z : StandardUnlinkPowerPullback n) :
    standardUnlinkPowerPullbackProj m (standardUnlinkPowerFactorMap hnm z) =
      standardUnlinkPowerPullbackProj n z :=
  rfl

/-- The concrete factor map is continuous for the subtype topologies on the raw pullbacks. -/
theorem continuous_standardUnlinkPowerFactorMap {n m q : ℕ} (hnm : n = m * q) :
    Continuous (standardUnlinkPowerFactorMap hnm) := by
  unfold standardUnlinkPowerFactorMap
  apply Continuous.subtype_mk
  have hbase : Continuous
      (fun z : StandardUnlinkPowerPullback n ↦ z.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hcoordinate : Continuous
      (fun z : StandardUnlinkPowerPullback n ↦ z.1.2.1) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  exact hbase.prodMk ((hcoordinate.pow q).subtype_mk _)

/-- The factor map sends every projection fiber into the fiber over the same base point. -/
theorem standardUnlinkPowerFactorMap_mapsTo_fiber {n m q : ℕ}
    (hnm : n = m * q) (x : StandardUnlinkComplement) :
    MapsTo (standardUnlinkPowerFactorMap hnm)
      (standardUnlinkPowerPullbackProj n ⁻¹' {x})
      (standardUnlinkPowerPullbackProj m ⁻¹' {x}) := by
  intro z hz
  change standardUnlinkPowerPullbackProj m
      (standardUnlinkPowerFactorMap hnm z) = x
  rw [standardUnlinkPowerFactorMap_proj]
  exact hz

/-! ## Identity and composition -/

/-- Factoring by exponent one is the identity, independently of the proof of `m = m * 1`. -/
@[simp]
theorem standardUnlinkPowerFactorMap_one (m : ℕ) (hmm : m = m * 1)
    (z : StandardUnlinkPowerPullback m) :
    standardUnlinkPowerFactorMap hmm z = z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp

/-- Function-level identity law for the factor maps. -/
theorem standardUnlinkPowerFactorMap_one_fun (m : ℕ) (hmm : m = m * 1) :
    standardUnlinkPowerFactorMap hmm = id := by
  funext z
  exact standardUnlinkPowerFactorMap_one m hmm z

/-- The degree equation used by composition.  The quotient exponent is written as `q * r`
because applying `q` first and then `r` raises a coordinate to `(z ^ q) ^ r`. -/
theorem standardUnlinkPowerFactor_degree_comp {n m k q r : ℕ}
    (hnm : n = m * q) (hmk : m = k * r) :
    n = k * (q * r) := by
  calc
    n = (k * r) * q := by rw [hnm, hmk]
    _ = k * (r * q) := Nat.mul_assoc _ _ _
    _ = k * (q * r) := by rw [Nat.mul_comm r q]

/-- Applying the factor of exponent `q` and then the factor of exponent `r` is the factor of
exponent `q * r`. -/
theorem standardUnlinkPowerFactorMap_comp_apply {n m k q r : ℕ}
    (hnm : n = m * q) (hmk : m = k * r)
    (z : StandardUnlinkPowerPullback n) :
    standardUnlinkPowerFactorMap hmk (standardUnlinkPowerFactorMap hnm z) =
      standardUnlinkPowerFactorMap
        (standardUnlinkPowerFactor_degree_comp hnm hmk) z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (z.1.2.1 ^ q) ^ r = z.1.2.1 ^ (q * r)
    exact (pow_mul _ _ _).symm

/-- Function-level composition law, with the order matching ordinary function composition. -/
theorem standardUnlinkPowerFactorMap_comp {n m k q r : ℕ}
    (hnm : n = m * q) (hmk : m = k * r) :
    standardUnlinkPowerFactorMap hmk ∘ standardUnlinkPowerFactorMap hnm =
      standardUnlinkPowerFactorMap
        (standardUnlinkPowerFactor_degree_comp hnm hmk) := by
  funext z
  exact standardUnlinkPowerFactorMap_comp_apply hnm hmk z

/-! ## Equivariance for the displayed roots-of-unity actions -/

/-- Raising an `n`-th root of unity to the `q`-th power gives an `m`-th root of unity when
`n = m * q`. -/
def standardUnlinkRootsOfUnityFactorHom {n m q : ℕ} (hnm : n = m * q) :
    rootsOfUnity n ℂ →* rootsOfUnity m ℂ where
  toFun u := ⟨u.1 ^ q, by
    apply (mem_rootsOfUnity' m (u.1 ^ q)).mpr
    have hu : (((u.1 : ℂˣ) : ℂ) ^ n) = 1 :=
      (mem_rootsOfUnity' n u.1).mp u.2
    calc
      (((u.1 ^ q : ℂˣ) : ℂ) ^ m) =
          ((((u.1 : ℂˣ) : ℂ) ^ q) ^ m) := by
        rw [Units.val_pow_eq_pow_val]
      _ = ((u.1 : ℂˣ) : ℂ) ^ (q * m) := (pow_mul _ _ _).symm
      _ = ((u.1 : ℂˣ) : ℂ) ^ n :=
        congrArg (fun e : ℕ ↦ ((u.1 : ℂˣ) : ℂ) ^ e)
          ((Nat.mul_comm q m).trans hnm.symm)
      _ = 1 := hu⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, Units.val_pow_eq_pow_val]
    exact mul_pow _ _ _

@[simp]
theorem standardUnlinkRootsOfUnityFactorHom_coe {n m q : ℕ}
    (hnm : n = m * q) (u : rootsOfUnity n ℂ) :
    (standardUnlinkRootsOfUnityFactorHom hnm u : ℂˣ) = u.1 ^ q :=
  rfl

/-- The power factor map is equivariant for the displayed deck actions and the homomorphism
`u ↦ u ^ q` on roots of unity. -/
theorem standardUnlinkPowerFactorMap_deck_equivariant {n m q : ℕ}
    (hnm : n = m * q) (u : rootsOfUnity n ℂ)
    (z : StandardUnlinkPowerPullback n) :
    standardUnlinkPowerFactorMap hnm (u • z) =
      standardUnlinkRootsOfUnityFactorHom hnm u •
        standardUnlinkPowerFactorMap hnm z := by
  rw [standardUnlinkPowerPullback_smul_apply n,
    standardUnlinkPowerPullback_smul_apply m]
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change ((((u.1 : ℂˣ) : ℂ) * z.1.2.1) ^ q) =
      (((((standardUnlinkRootsOfUnityFactorHom hnm u).1 : ℂˣ) : ℂ)) *
        z.1.2.1 ^ q)
    rw [standardUnlinkRootsOfUnityFactorHom_coe]
    rw [mul_pow, Units.val_pow_eq_pow_val]

end SplittingSpheres
