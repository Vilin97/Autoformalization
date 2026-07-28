/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.Abel
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverKernel
import McKayConjecture.GroupTheory.PerfectCentralExtensionCenter

/-!
# Corrected lifts for the sixfold `A₆` presentation

Given a central extension onto `A₆`, choose arbitrary lifts `X,Y` of the
two ATLAS generators.  The four relator errors are central.  Multiplying
`X` and `Y` by the inverses of the two lattice errors makes the two
lattice relations hold, and hence defines a homomorphism from the explicit
Schur-cover presentation.
-/

noncomputable section

open scoped commutatorElement

namespace McKayConjecture
namespace GroupTheory

/-- Two ambient factors can be separated from two central correction
factors. -/
theorem alternatingSix_mul_mul_central_factors
    {G : Type*} [Group G]
    (x y a b : G)
    (ha : a ∈ Subgroup.center G) :
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
theorem alternatingSix_mul_pow_central_factor
    {G : Type*} [Group G]
    (x z : G)
    (hz : z ∈ Subgroup.center G)
    (n : ℕ) :
    (x * z) ^ n = x ^ n * z ^ n :=
  (show Commute x z from
    Subgroup.mem_center_iff.mp hz x).mul_pow n

/-- The correction exponents make both lattice rows vanish. -/
theorem alternatingSix_corrected_lattice_relations
    {K : Type*} [CommGroup K]
    (q0 q1 q2 q3 : K) :
    let h1 := q0 ^ 3 * q2 ^ (-2 : ℤ) * q3
    let h2 := q1 ^ 4 * q2 ^ 3 * q3 ^ (-3 : ℤ)
    let x := h1⁻¹
    let y := h2⁻¹
    (q0 * x ^ 2) ^ 3 *
          (q2 * x ^ 5 * y ^ 5) ^ (-2 : ℤ) *
          (q3 * x ^ 5 * y ^ 10) = 1 ∧
      (q1 * y ^ 4) ^ 4 *
          (q2 * x ^ 5 * y ^ 5) ^ 3 *
          (q3 * x ^ 5 * y ^ 10) ^ (-3 : ℤ) = 1 := by
  let aq0 : Additive K := Additive.ofMul q0
  let aq1 : Additive K := Additive.ofMul q1
  let aq2 : Additive K := Additive.ofMul q2
  let aq3 : Additive K := Additive.ofMul q3
  let ah1 :=
    3 • aq0 + (-2 : ℤ) • aq2 + aq3
  let ah2 :=
    4 • aq1 + 3 • aq2 + (-3 : ℤ) • aq3
  let ax := -ah1
  let ay := -ah2
  change
    (3 • (aq0 + 2 • ax) +
          (-2 : ℤ) • (aq2 + 5 • ax + 5 • ay) +
          (aq3 + 5 • ax + 10 • ay) = 0) ∧
      (4 • (aq1 + 4 • ay) +
          3 • (aq2 + 5 • ax + 5 • ay) +
          (-3 : ℤ) •
            (aq3 + 5 • ax + 10 • ay) = 0)
  dsimp [ax, ay, ah1, ah2]
  constructor <;> abel

/-- Every central extension onto `A₆` receives a homomorphism from the
explicit Schur-cover presentation, over `A₆`. -/
theorem alternatingSixSchur_exists_lift
    {V : Type*} [Group V]
    (F : CentralExtension V AlternatingSix) :
    ∃ σ :
        AlternatingSixSchurPresentedGroup →* V,
      F.projection.comp σ =
        alternatingSixSchurProjection := by
  let X : V :=
    Classical.choose
      (F.surjective alternatingSixPresentationA)
  let Y : V :=
    Classical.choose
      (F.surjective alternatingSixPresentationB)
  have hX :
      F.projection X = alternatingSixPresentationA :=
    Classical.choose_spec
      (F.surjective alternatingSixPresentationA)
  have hY :
      F.projection Y = alternatingSixPresentationB :=
    Classical.choose_spec
      (F.surjective alternatingSixPresentationB)

  let K : Subgroup V := F.projection.ker
  letI : CommGroup K :=
    { (inferInstance : Group K) with
      mul_comm := fun left right =>
        Subtype.ext
          (Subgroup.mem_center_iff.mp
            (F.ker_le_center left.2) right.1).symm }

  have hq0Ker : X ^ 2 ∈ K := by
    apply MonoidHom.mem_ker.mpr
    rw [map_pow, hX,
      alternatingSixPresentation_relations.1]
  have hq1Ker : Y ^ 4 ∈ K := by
    apply MonoidHom.mem_ker.mpr
    rw [map_pow, hY,
      alternatingSixPresentation_relations.2.1]
  have hq2Ker : (X * Y) ^ 5 ∈ K := by
    apply MonoidHom.mem_ker.mpr
    rw [map_pow, map_mul, hX, hY,
      alternatingSixPresentation_relations.2.2.1]
  have hq3Ker : (X * Y ^ 2) ^ 5 ∈ K := by
    apply MonoidHom.mem_ker.mpr
    rw [map_pow, map_mul, map_pow, hX, hY,
      alternatingSixPresentation_relations.2.2.2]

  let q0 : K := ⟨X ^ 2, hq0Ker⟩
  let q1 : K := ⟨Y ^ 4, hq1Ker⟩
  let q2 : K := ⟨(X * Y) ^ 5, hq2Ker⟩
  let q3 : K := ⟨(X * Y ^ 2) ^ 5, hq3Ker⟩
  let h1 : K := q0 ^ 3 * q2 ^ (-2 : ℤ) * q3
  let h2 : K := q1 ^ 4 * q2 ^ 3 * q3 ^ (-3 : ℤ)
  let x : K := h1⁻¹
  let y : K := h2⁻¹
  let X' : V := X * x
  let Y' : V := Y * y
  let q0' : K := q0 * x ^ 2
  let q1' : K := q1 * y ^ 4
  let q2' : K := q2 * x ^ 5 * y ^ 5
  let q3' : K := q3 * x ^ 5 * y ^ 10

  have hxCenter : (x : V) ∈ Subgroup.center V :=
    F.ker_le_center x.2
  have hyCenter : (y : V) ∈ Subgroup.center V :=
    F.ker_le_center y.2
  have hxyCenter :
      (x : V) * (y : V) ∈ Subgroup.center V :=
    (Subgroup.center V).mul_mem hxCenter hyCenter
  have hyTwoCenter :
      (y : V) ^ 2 ∈ Subgroup.center V :=
    (Subgroup.center V).pow_mem hyCenter 2
  have hxyTwoCenter :
      (x : V) * (y : V) ^ 2 ∈
        Subgroup.center V :=
    (Subgroup.center V).mul_mem hxCenter hyTwoCenter

  have hX' :
      F.projection X' =
        alternatingSixPresentationA := by
    simp [X', hX, MonoidHom.mem_ker.mp x.2]
  have hY' :
      F.projection Y' =
        alternatingSixPresentationB := by
    simp [Y', hY, MonoidHom.mem_ker.mp y.2]

  have hq0' : X' ^ 2 = (q0' : V) := by
    dsimp [X', q0', q0]
    exact
      alternatingSix_mul_pow_central_factor
        X (x : V) hxCenter 2
  have hq1' : Y' ^ 4 = (q1' : V) := by
    dsimp [Y', q1', q1]
    exact
      alternatingSix_mul_pow_central_factor
        Y (y : V) hyCenter 4
  have hq2' : (X' * Y') ^ 5 = (q2' : V) := by
    dsimp [X', Y', q2', q2]
    rw [alternatingSix_mul_mul_central_factors
      X Y (x : V) (y : V) hxCenter]
    rw [alternatingSix_mul_pow_central_factor
      (X * Y) ((x : V) * (y : V))
      hxyCenter 5]
    have hpower :
        ((x : V) * (y : V)) ^ 5 =
          (x : V) ^ 5 * (y : V) ^ 5 := by
      exact congrArg Subtype.val (mul_pow x y 5)
    rw [hpower]
    simp only [mul_assoc]
  have hq3' :
      (X' * Y' ^ 2) ^ 5 = (q3' : V) := by
    dsimp [X', Y', q3', q3]
    rw [alternatingSix_mul_pow_central_factor
      Y (y : V) hyCenter 2]
    rw [alternatingSix_mul_mul_central_factors
      X (Y ^ 2) (x : V) ((y : V) ^ 2)
      hxCenter]
    rw [alternatingSix_mul_pow_central_factor
      (X * Y ^ 2) ((x : V) * (y : V) ^ 2)
      hxyTwoCenter 5]
    have hpower :
        ((x : V) * (y : V) ^ 2) ^ 5 =
          (x : V) ^ 5 * ((y : V) ^ 2) ^ 5 := by
      exact
        congrArg Subtype.val
          (mul_pow x (y ^ 2) 5)
    rw [hpower]
    have hyPower :
        ((y : V) ^ 2) ^ 5 =
          (y : V) ^ 10 := by
      rw [← pow_mul]
    rw [hyPower]
    simp only [mul_assoc]

  have hlattice :
      q0' ^ 3 * q2' ^ (-2 : ℤ) * q3' = 1 ∧
        q1' ^ 4 * q2' ^ 3 *
          q3' ^ (-3 : ℤ) = 1 := by
    exact
      alternatingSix_corrected_lattice_relations
        q0 q1 q2 q3

  let correctedGenerator : Fin 6 → V
    | 0 => X'
    | 1 => Y'
    | 2 => q0'
    | 3 => q1'
    | 4 => q2'
    | 5 => q3'
  have correctedGenerator_kills_relators :
      ∀ relator ∈ alternatingSixSchurRelators,
        FreeGroup.lift correctedGenerator relator = 1 := by
    intro relator hrelator
    rcases hrelator with hdefinition | hrest
    · rcases hdefinition with ⟨i, rfl⟩ |
        ⟨index, rfl⟩
      · fin_cases i
        · simpa [alternatingSixSchurDefinitionRelator,
            alternatingSixSchurBaseRelator,
            alternatingSixSchurFreeA,
            alternatingSixSchurFreeK,
            alternatingSixSchurGenerator,
            correctedGenerator] using
              mul_inv_eq_one.mpr hq0'
        · simpa [alternatingSixSchurDefinitionRelator,
            alternatingSixSchurBaseRelator,
            alternatingSixSchurFreeB,
            alternatingSixSchurFreeK,
            alternatingSixSchurGenerator,
            correctedGenerator] using
              mul_inv_eq_one.mpr hq1'
        · simpa [alternatingSixSchurDefinitionRelator,
            alternatingSixSchurBaseRelator,
            alternatingSixSchurFreeA,
            alternatingSixSchurFreeB,
            alternatingSixSchurFreeK,
            alternatingSixSchurGenerator,
            correctedGenerator] using
              mul_inv_eq_one.mpr hq2'
        · simpa [alternatingSixSchurDefinitionRelator,
            alternatingSixSchurBaseRelator,
            alternatingSixSchurFreeA,
            alternatingSixSchurFreeB,
            alternatingSixSchurFreeK,
            alternatingSixSchurGenerator,
            correctedGenerator] using
              mul_inv_eq_one.mpr hq3'
      · rcases index with ⟨i, j⟩
        rw [show
          FreeGroup.lift correctedGenerator
              (alternatingSixSchurCentralityRelator
                (i, j)) =
            ⁅correctedGenerator
                ⟨i.val + 2, by omega⟩,
              correctedGenerator j⁆ by
            simp [alternatingSixSchurCentralityRelator,
              alternatingSixSchurFreeK,
              alternatingSixSchurGenerator]]
        fin_cases i
        · apply
            commutatorElement_eq_one_iff_commute.mpr
          exact
            (Subgroup.mem_center_iff.mp
              (F.ker_le_center q0'.2)
              (correctedGenerator j)).symm
        · apply
            commutatorElement_eq_one_iff_commute.mpr
          exact
            (Subgroup.mem_center_iff.mp
              (F.ker_le_center q1'.2)
              (correctedGenerator j)).symm
        · apply
            commutatorElement_eq_one_iff_commute.mpr
          exact
            (Subgroup.mem_center_iff.mp
              (F.ker_le_center q2'.2)
              (correctedGenerator j)).symm
        · apply
            commutatorElement_eq_one_iff_commute.mpr
          exact
            (Subgroup.mem_center_iff.mp
              (F.ker_le_center q3'.2)
              (correctedGenerator j)).symm
    · rcases hrest with rfl | hsecond
      · simpa [alternatingSixSchurLatticeRelatorOne,
          alternatingSixSchurFreeK,
          alternatingSixSchurGenerator,
          correctedGenerator] using
            congrArg Subtype.val hlattice.1
      · have hsecond' :
          relator =
            alternatingSixSchurLatticeRelatorTwo := by
          simpa using hsecond
        subst relator
        simpa [alternatingSixSchurLatticeRelatorTwo,
          alternatingSixSchurFreeK,
          alternatingSixSchurGenerator,
          correctedGenerator] using
            congrArg Subtype.val hlattice.2

  let σ :
      AlternatingSixSchurPresentedGroup →* V :=
    PresentedGroup.toGroup
      correctedGenerator_kills_relators
  refine ⟨σ, ?_⟩
  apply PresentedGroup.ext
  intro i
  fin_cases i
  · simpa [σ, correctedGenerator,
      alternatingSixSchurProjection,
      alternatingSixSchurProjectionGenerator,
      hX']
  · simpa [σ, correctedGenerator,
      alternatingSixSchurProjection,
      alternatingSixSchurProjectionGenerator,
      hY']
  · simpa [σ, correctedGenerator,
      alternatingSixSchurProjection,
      alternatingSixSchurProjectionGenerator,
      MonoidHom.mem_ker.mp q0'.2]
  · simpa [σ, correctedGenerator,
      alternatingSixSchurProjection,
      alternatingSixSchurProjectionGenerator,
      MonoidHom.mem_ker.mp q1'.2]
  · simpa [σ, correctedGenerator,
      alternatingSixSchurProjection,
      alternatingSixSchurProjectionGenerator,
      MonoidHom.mem_ker.mp q2'.2]
  · simpa [σ, correctedGenerator,
      alternatingSixSchurProjection,
      alternatingSixSchurProjectionGenerator,
      MonoidHom.mem_ker.mp q3'.2]

end GroupTheory
end McKayConjecture
