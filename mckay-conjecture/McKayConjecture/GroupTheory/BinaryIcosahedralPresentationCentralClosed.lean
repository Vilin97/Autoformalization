/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralExtensionUniversalityCriterion
import McKayConjecture.GroupTheory.SpecialLinearTwoFivePresentation

/-!
# Central closedness of the balanced binary-icosahedral presentation

For the presentation

`⟨x,y,z | x² = y³ = z⁵ = xyz⟩`,

the exponent-sum matrix of the three relators is

```
[ 2 -3  0]
[ 0  3 -5]
[-1 -1  4].
```

Its determinant is `-1`.  Consequently, in a central extension of the
presented group, arbitrary lifts of `x,y,z` can be corrected by central
kernel elements so that all three relations hold exactly.  The universal
property of `PresentedGroup` then gives a homomorphic section.

The correction below records the inverse integer matrix explicitly.  If
`e₀,e₁,e₂` are the three relation errors, use

```
a = e₀⁷ e₁¹² e₂¹⁵,
b = e₀⁵ e₁⁸  e₂¹⁰,
c = e₀³ e₁⁵  e₂⁶.
```
-/

noncomputable section

open scoped IsMulCommutative

universe u

namespace McKayConjecture
namespace GroupTheory

/-- Central correction factors can be moved past two arbitrary ambient
factors. -/
theorem mul_mul_central_factors
    {G : Type u} [Group G]
    (x y a b : G)
    (ha : a ∈ Subgroup.center G)
    (_hb : b ∈ Subgroup.center G) :
    (x * a) * (y * b) =
      (x * y) * (a * b) := by
  have hay : a * y = y * a :=
    (Subgroup.mem_center_iff.mp ha y).symm
  calc
    (x * a) * (y * b) =
        x * (a * y) * b := by
      simp only [mul_assoc]
    _ = x * (y * a) * b := by rw [hay]
    _ = (x * y) * (a * b) := by
      simp only [mul_assoc]

/-- A central factor separates from a positive power. -/
theorem mul_pow_central_factor
    {G : Type u} [Group G]
    (x z : G)
    (hz : z ∈ Subgroup.center G)
    (n : Nat) :
    (x * z) ^ n = x ^ n * z ^ n :=
  (show Commute x z from
    Subgroup.mem_center_iff.mp hz x).mul_pow n

/-- The group given by the balanced binary-icosahedral presentation is
centrally closed. -/
theorem binaryIcosahedralPresentedGroup_isCentrallyClosed :
    IsCentrallyClosed BinaryIcosahedralPresentedGroup := by
  intro V _ F
  let X : V :=
    Classical.choose
      (F.surjective binaryIcosahedralPresentedX)
  let Y : V :=
    Classical.choose
      (F.surjective binaryIcosahedralPresentedY)
  let Z : V :=
    Classical.choose
      (F.surjective binaryIcosahedralPresentedZ)
  have hX :
      F.projection X = binaryIcosahedralPresentedX :=
    Classical.choose_spec
      (F.surjective binaryIcosahedralPresentedX)
  have hY :
      F.projection Y = binaryIcosahedralPresentedY :=
    Classical.choose_spec
      (F.surjective binaryIcosahedralPresentedY)
  have hZ :
      F.projection Z = binaryIcosahedralPresentedZ :=
    Classical.choose_spec
      (F.surjective binaryIcosahedralPresentedZ)

  let K : Subgroup V := F.projection.ker
  letI : IsMulCommutative K :=
    ⟨⟨fun a b ↦
      Subtype.ext
        (Subgroup.mem_center_iff.mp
          (F.ker_le_center a.2) b.1).symm⟩⟩

  have he₀Ker :
      X ^ 2 * (Y ^ 3)⁻¹ ∈ K := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_pow, map_inv, map_pow,
      hX, hY, binaryIcosahedralPresented_relations.1]
    simp
  have he₁Ker :
      Y ^ 3 * (Z ^ 5)⁻¹ ∈ K := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_pow, map_inv, map_pow,
      hY, hZ, binaryIcosahedralPresented_relations.2.1]
    simp
  have he₂Ker :
      Z ^ 5 * (X * Y * Z)⁻¹ ∈ K := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_pow, map_inv, map_mul,
      map_mul, hX, hY, hZ,
      binaryIcosahedralPresented_relations.2.2]
    simp

  let e₀ : K := ⟨X ^ 2 * (Y ^ 3)⁻¹, he₀Ker⟩
  let e₁ : K := ⟨Y ^ 3 * (Z ^ 5)⁻¹, he₁Ker⟩
  let e₂ : K := ⟨Z ^ 5 * (X * Y * Z)⁻¹, he₂Ker⟩
  let a : K := e₀ ^ 7 * e₁ ^ 12 * e₂ ^ 15
  let b : K := e₀ ^ 5 * e₁ ^ 8 * e₂ ^ 10
  let c : K := e₀ ^ 3 * e₁ ^ 5 * e₂ ^ 6

  have hab : e₀ * a ^ 2 = b ^ 3 := by
    dsimp [a, b]
    simp only [pow_succ, pow_zero]
    ac_rfl
  have hbc : e₁ * b ^ 3 = c ^ 5 := by
    dsimp [b, c]
    simp only [pow_succ, pow_zero]
    ac_rfl
  have hca : e₂ * c ^ 5 = a * b * c := by
    dsimp [a, b, c]
    simp only [pow_succ, pow_zero]
    ac_rfl

  have he₀Center : (e₀ : V) ∈ Subgroup.center V :=
    F.ker_le_center e₀.2
  have he₁Center : (e₁ : V) ∈ Subgroup.center V :=
    F.ker_le_center e₁.2
  have he₂Center : (e₂ : V) ∈ Subgroup.center V :=
    F.ker_le_center e₂.2
  have haCenter : (a : V) ∈ Subgroup.center V :=
    F.ker_le_center a.2
  have hbCenter : (b : V) ∈ Subgroup.center V :=
    F.ker_le_center b.2
  have hcCenter : (c : V) ∈ Subgroup.center V :=
    F.ker_le_center c.2

  have he₀ :
      X ^ 2 = (e₀ : V) * Y ^ 3 := by
    change
      X ^ 2 =
        (X ^ 2 * (Y ^ 3)⁻¹) * Y ^ 3
    group
  have he₁ :
      Y ^ 3 = (e₁ : V) * Z ^ 5 := by
    change
      Y ^ 3 =
        (Y ^ 3 * (Z ^ 5)⁻¹) * Z ^ 5
    group
  have he₂ :
      Z ^ 5 = (e₂ : V) * (X * Y * Z) := by
    change
      Z ^ 5 =
        (Z ^ 5 * (X * Y * Z)⁻¹) *
          (X * Y * Z)
    group

  let X' : V := X * a
  let Y' : V := Y * b
  let Z' : V := Z * c

  have hX' :
      F.projection X' =
        binaryIcosahedralPresentedX := by
    simp [X', hX, MonoidHom.mem_ker.mp a.2]
  have hY' :
      F.projection Y' =
        binaryIcosahedralPresentedY := by
    simp [Y', hY, MonoidHom.mem_ker.mp b.2]
  have hZ' :
      F.projection Z' =
        binaryIcosahedralPresentedZ := by
    simp [Z', hZ, MonoidHom.mem_ker.mp c.2]

  have hrelation₀ : X' ^ 2 = Y' ^ 3 := by
    dsimp [X', Y']
    rw [
      mul_pow_central_factor X (a : V) haCenter,
      mul_pow_central_factor Y (b : V) hbCenter,
      he₀]
    calc
      ((e₀ : V) * Y ^ 3) * (a : V) ^ 2 =
          Y ^ 3 * ((e₀ : V) * (a : V) ^ 2) := by
        rw [(Subgroup.mem_center_iff.mp
          he₀Center (Y ^ 3)).symm]
        simp only [mul_assoc]
      _ = Y ^ 3 * (b : V) ^ 3 := by
        rw [show
          (e₀ : V) * (a : V) ^ 2 =
            (b : V) ^ 3 from
              congrArg Subtype.val hab]
  have hrelation₁ : Y' ^ 3 = Z' ^ 5 := by
    dsimp [Y', Z']
    rw [
      mul_pow_central_factor Y (b : V) hbCenter,
      mul_pow_central_factor Z (c : V) hcCenter,
      he₁]
    calc
      ((e₁ : V) * Z ^ 5) * (b : V) ^ 3 =
          Z ^ 5 * ((e₁ : V) * (b : V) ^ 3) := by
        rw [(Subgroup.mem_center_iff.mp
          he₁Center (Z ^ 5)).symm]
        simp only [mul_assoc]
      _ = Z ^ 5 * (c : V) ^ 5 := by
        rw [show
          (e₁ : V) * (b : V) ^ 3 =
            (c : V) ^ 5 from
              congrArg Subtype.val hbc]
  have hrelation₂ : Z' ^ 5 = X' * Y' * Z' := by
    dsimp [X', Y', Z']
    rw [
      mul_pow_central_factor Z (c : V) hcCenter,
      he₂]
    calc
      ((e₂ : V) * (X * Y * Z)) * (c : V) ^ 5 =
          (X * Y * Z) *
            ((e₂ : V) * (c : V) ^ 5) := by
        rw [(Subgroup.mem_center_iff.mp
          he₂Center (X * Y * Z)).symm]
        simp only [mul_assoc]
      _ = (X * Y * Z) *
            ((a : V) * (b : V) * (c : V)) := by
        rw [show
          (e₂ : V) * (c : V) ^ 5 =
            (a : V) * (b : V) * (c : V) from
              congrArg Subtype.val hca]
      _ = (X * (a : V)) *
            (Y * (b : V)) *
            (Z * (c : V)) := by
        have habCenter :
            (a : V) * (b : V) ∈
              Subgroup.center V :=
          (Subgroup.center V).mul_mem
            haCenter hbCenter
        rw [mul_mul_central_factors X Y
          (a : V) (b : V) haCenter hbCenter]
        rw [mul_mul_central_factors
          (X * Y) Z
          ((a : V) * (b : V)) (c : V)
          habCenter hcCenter]
  let correctedGenerator : Fin 3 → V
    | 0 => X'
    | 1 => Y'
    | 2 => Z'
  have correctedGenerator_kills_relators :
      ∀ r ∈ binaryIcosahedralRelators,
        FreeGroup.lift correctedGenerator r = 1 := by
    intro r hr
    simp only [binaryIcosahedralRelators,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with (rfl | rfl | rfl)
    · simp [binaryIcosahedralRelatorXY,
        binaryIcosahedralGenerator,
        correctedGenerator, hrelation₀]
    · simp [binaryIcosahedralRelatorYZ,
        binaryIcosahedralGenerator,
        correctedGenerator, hrelation₁]
    · simp [binaryIcosahedralRelatorZXYZ,
        binaryIcosahedralGenerator,
        correctedGenerator, hrelation₂]
  let σ : BinaryIcosahedralPresentedGroup →* V :=
    PresentedGroup.toGroup
      correctedGenerator_kills_relators
  refine ⟨σ, ?_⟩
  apply PresentedGroup.ext
  intro i
  fin_cases i
  · simp [σ, correctedGenerator, hX',
      binaryIcosahedralPresentedX]
  · simp [σ, correctedGenerator, hY',
      binaryIcosahedralPresentedY]
  · simp [σ, correctedGenerator, hZ',
      binaryIcosahedralPresentedZ]

end GroupTheory
end McKayConjecture
