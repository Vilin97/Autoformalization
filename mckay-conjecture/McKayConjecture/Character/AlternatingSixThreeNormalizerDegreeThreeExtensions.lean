/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import McKayConjecture.Character.AlternatingSixThreeNormalizerDegreeThreeHeisenberg
import McKayConjecture.Character.CyclicExtensionAlong
import McKayConjecture.Character.Gallagher
import McKayConjecture.Character.InnerAutomorphism
import McKayConjecture.Character.AlternatingSixThreeNormalizerLinearRows

/-!
# The sixteen degree-three rows of the three-normalizer

The two nonlinear Heisenberg characters are invariant under the cyclic
factor.  The cyclic-extension theorem supplies one extension of each,
and twisting by the eight quotient-linear characters supplies all
sixteen degree-three rows.
-/

noncomputable section

open CategoryTheory Matrix
open scoped BigOperators

namespace McKayConjecture
namespace AlternatingSixThreeNormalizer

open GroupTheory

/-- Closed character formula for a Schrödinger row: it vanishes off the
center and is three times its central character on the center. -/
theorem degreeThreeHeisenbergCharacter_values_formula
    (central : Fin 2)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    (degreeThreeHeisenbergCharacter central).values p =
      if p.x = 0 ∧ p.y = 0 then
        3 * threePhase
          (degreeThreeCentralParameter central * p.z)
      else
        0 := by
  rw [degreeThreeHeisenbergCharacter_values]
  rw [Matrix.trace]
  by_cases hx : p.x = 0
  · by_cases hy : p.y = 0
    · simp [degreeThreeHeisenbergMatrix, hx, hy,
        Finset.sum_const, ZMod.card]
    · have hky :
          degreeThreeCentralParameter central * p.y ≠ 0 :=
        mul_ne_zero
          (degreeThreeCentralParameter_ne_zero central) hy
      have hsum :
          (∑ i : ZMod 3,
              threePhase
                (i *
                  (degreeThreeCentralParameter central * p.y))) =
            0 := by
        rw [AddChar.sum_mulShift
          (degreeThreeCentralParameter central * p.y)
          (ZMod.isPrimitive_stdAddChar 3)]
        simp [hky]
      rw [if_neg (not_and_or.mpr (Or.inr hy))]
      change
        (∑ i : ZMod 3,
          if i = i + p.x then
            threePhase
              (degreeThreeCentralParameter central *
                (p.z + p.y * i))
          else 0) = 0
      simp only [hx, add_zero, if_true]
      calc
        (∑ i : ZMod 3,
            threePhase
              (degreeThreeCentralParameter central *
                (p.z + p.y * i))) =
            threePhase
                (degreeThreeCentralParameter central * p.z) *
              (∑ i : ZMod 3,
                threePhase
                  (i *
                    (degreeThreeCentralParameter central * p.y))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [← threePhase_add]
              congr 1
              ring
        _ = 0 := by rw [hsum, mul_zero]
  · rw [if_neg (not_and_or.mpr (Or.inl hx))]
    apply Finset.sum_eq_zero
    intro i _
    change
      (if i = i + p.x then
        threePhase
          (degreeThreeCentralParameter central *
            (p.z + p.y * i))
      else 0) = 0
    rw [if_neg]
    intro hi
    apply hx
    have h := congrArg (fun z => -i + z) hi
    simpa [add_assoc] using h.symm

/-- Every element of the cyclic factor fixes the center pointwise. -/
theorem alternatingSixThreeHeisenbergCoordinateAction_central
    (c : AlternatingSixThreeCyclicEight)
    (z : ZMod 3) :
    alternatingSixThreeHeisenbergCoordinateAction c ⟨z, 0, 0⟩ =
      ⟨z, 0, 0⟩ := by
  apply alternatingSixThreeCyclicEight_cases (c := c)
  all_goals
    rw [alternatingSixThreeHeisenbergCoordinateAction_apply]
    simp [alternatingSixThreeHeisenbergCoordinateActionFormula]

/-- The coordinate action preserves the test for membership in the
center. -/
theorem alternatingSixThreeHeisenbergCoordinateAction_isCentral_iff
    (c : AlternatingSixThreeCyclicEight)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    (alternatingSixThreeHeisenbergCoordinateAction c p).x = 0 ∧
        (alternatingSixThreeHeisenbergCoordinateAction c p).y = 0 ↔
      p.x = 0 ∧ p.y = 0 := by
  constructor
  · intro h
    have hcoordinate :
        alternatingSixThreeHeisenbergCoordinateAction c p =
          ⟨(alternatingSixThreeHeisenbergCoordinateAction c p).z,
            0, 0⟩ := by
      ext
      · rfl
      · exact h.1
      · exact h.2
    have hinverse :=
      congrArg
        (fun q =>
          alternatingSixThreeHeisenbergCoordinateAction c⁻¹ q)
        hcoordinate
    have hleft :
        alternatingSixThreeHeisenbergCoordinateAction c⁻¹
            (alternatingSixThreeHeisenbergCoordinateAction c p) =
          p := by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        MulAut.one_apply]
    rw [hleft,
      alternatingSixThreeHeisenbergCoordinateAction_central] at hinverse
    exact ⟨congrArg (·.x) hinverse, congrArg (·.y) hinverse⟩
  · rintro ⟨hx, hy⟩
    have hp : p = ⟨p.z, 0, 0⟩ := by
      ext <;> simp [hx, hy]
    rw [hp, alternatingSixThreeHeisenbergCoordinateAction_central]
    simp

/-- The displayed character formula is fixed by the entire `C₈`
coordinate action. -/
theorem degreeThreeHeisenbergCharacter_invariant
    (central : Fin 2)
    (c : AlternatingSixThreeCyclicEight)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    (degreeThreeHeisenbergCharacter central).values
        (alternatingSixThreeHeisenbergCoordinateAction c p) =
      (degreeThreeHeisenbergCharacter central).values p := by
  by_cases hp : p.x = 0 ∧ p.y = 0
  · have heq : p = ⟨p.z, 0, 0⟩ := by
      ext <;> simp [hp.1, hp.2]
    rw [heq, alternatingSixThreeHeisenbergCoordinateAction_central]
  · rw [degreeThreeHeisenbergCharacter_values_formula,
      degreeThreeHeisenbergCharacter_values_formula,
      if_neg hp, if_neg]
    intro haction
    exact hp
      ((alternatingSixThreeHeisenbergCoordinateAction_isCentral_iff
        c p).mp haction)

/-- The semidirect-product extension used to invoke the invariant cyclic
extension theorem. -/
abbrev degreeThreeGroupExtension :=
  SemidirectProduct.toGroupExtension
    alternatingSixThreeHeisenbergCoordinateAction

local instance degreeThreeHeisenbergRangeNormal :
    (SemidirectProduct.inl :
      AlternatingSixThreeHeisenbergCoordinates →*
        AlternatingSixThreeNormalizerCoordinates).range.Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

/-- Conjugation of the canonical Heisenberg copy has the expected
coordinate formula. -/
theorem degreeThree_conjugate_inl
    (g : AlternatingSixThreeNormalizerCoordinates)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    g * SemidirectProduct.inl p * g⁻¹ =
      SemidirectProduct.inl
        (g.left *
          alternatingSixThreeHeisenbergCoordinateAction g.right p *
            g.left⁻¹) := by
  apply SemidirectProduct.ext
  · simp [SemidirectProduct.mul_left, mul_assoc]
  · simp

/-- Conjugation in the full semidirect product preserves each of the two
Heisenberg characters. -/
theorem degreeThreeHeisenbergCharacter_conjAct_invariant
    (central : Fin 2)
    (g : AlternatingSixThreeNormalizerCoordinates)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    (degreeThreeHeisenbergCharacter central).values
        (degreeThreeGroupExtension.conjAct g p) =
      (degreeThreeHeisenbergCharacter central).values p := by
  have hcoordinate :
      degreeThreeGroupExtension.conjAct g p =
        g.left *
          alternatingSixThreeHeisenbergCoordinateAction g.right p *
            g.left⁻¹ := by
    apply degreeThreeGroupExtension.inl_injective
    rw [GroupExtension.inl_conjAct_comm degreeThreeGroupExtension]
    exact degreeThree_conjugate_inl g p
  rw [hcoordinate]
  calc
    (degreeThreeHeisenbergCharacter central).values
          (g.left *
            alternatingSixThreeHeisenbergCoordinateAction g.right p *
              g.left⁻¹) =
        (degreeThreeHeisenbergCharacter central).values
          (alternatingSixThreeHeisenbergCoordinateAction g.right p) := by
      apply IrreducibleCharacter.values_eq_of_isConj
      exact isConj_iff.mpr ⟨g.left⁻¹, by group⟩
    _ =
        (degreeThreeHeisenbergCharacter central).values p :=
      degreeThreeHeisenbergCharacter_invariant central g.right p

/-- The quotient by the Heisenberg factor is cyclic. -/
theorem degreeThreeHeisenbergRange_quotient_isCyclic :
    IsCyclic
      (AlternatingSixThreeNormalizerCoordinates ⧸
        (SemidirectProduct.inl :
          AlternatingSixThreeHeisenbergCoordinates →*
            AlternatingSixThreeNormalizerCoordinates).range) := by
  change
    IsCyclic
      (AlternatingSixThreeNormalizerCoordinates ⧸
        degreeThreeGroupExtension.inl.range)
  rw [
    (degreeThreeGroupExtension.quotientRangeInlEquivRight).isCyclic
  ]
  infer_instance

/-- Choose one extension of each nonlinear Heisenberg row to the full
normalizer. -/
def degreeThreeBaseCharacter (central : Fin 2) :
    IrreducibleCharacter AlternatingSixThreeNormalizerCoordinates :=
  Classical.choose
    (IrreducibleCharacter.exists_extensionAlong_of_injective_cyclic_range
      (SemidirectProduct.inl :
        AlternatingSixThreeHeisenbergCoordinates →*
          AlternatingSixThreeNormalizerCoordinates)
      SemidirectProduct.inl_injective
      (by
        rw [SemidirectProduct.range_inl_eq_ker_rightHom]
        infer_instance)
      degreeThreeHeisenbergRange_quotient_isCyclic
      degreeThreeGroupExtension.conjAct
      (fun g p =>
        GroupExtension.inl_conjAct_comm degreeThreeGroupExtension)
      (degreeThreeHeisenbergCharacter central)
      (degreeThreeHeisenbergCharacter_conjAct_invariant central))

/-- The chosen character really extends the specified Heisenberg row. -/
theorem degreeThreeBaseCharacter_isExtension
    (central : Fin 2) :
    IrreducibleCharacter.IsExtensionAlong
      (SemidirectProduct.inl :
        AlternatingSixThreeHeisenbergCoordinates →*
          AlternatingSixThreeNormalizerCoordinates)
      (degreeThreeHeisenbergCharacter central)
      (degreeThreeBaseCharacter central) :=
  Classical.choose_spec
    (IrreducibleCharacter.exists_extensionAlong_of_injective_cyclic_range
      (SemidirectProduct.inl :
        AlternatingSixThreeHeisenbergCoordinates →*
          AlternatingSixThreeNormalizerCoordinates)
      SemidirectProduct.inl_injective
      (by
        rw [SemidirectProduct.range_inl_eq_ker_rightHom]
        infer_instance)
      degreeThreeHeisenbergRange_quotient_isCyclic
      degreeThreeGroupExtension.conjAct
      (fun g p =>
        GroupExtension.inl_conjAct_comm degreeThreeGroupExtension)
      (degreeThreeHeisenbergCharacter central)
      (degreeThreeHeisenbergCharacter_conjAct_invariant central))

@[simp]
theorem degreeThreeBaseCharacter_degree (central : Fin 2) :
    (degreeThreeBaseCharacter central).degree = 3 := by
  rw [(degreeThreeBaseCharacter_isExtension central).degree_eq]
  exact degreeThreeHeisenbergCharacter_degree central

/-- The quotient-linear character on the coordinate model. -/
def coordinateQuotientLinearHom (j : Fin 8) :
    AlternatingSixThreeNormalizerCoordinates →* ℂˣ :=
  (CyclicEight.linearHom j).comp SemidirectProduct.rightHom

@[simp]
theorem coordinateQuotientLinearHom_inl
    (j : Fin 8)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    coordinateQuotientLinearHom j (SemidirectProduct.inl p) = 1 := by
  simp [coordinateQuotientLinearHom]

/-- The sixteen degree-three characters, obtained by the eight quotient
twists of each of the two base extensions. -/
def degreeThreeCharacter (central : Fin 2) (twist : Fin 8) :
    IrreducibleCharacter AlternatingSixThreeNormalizerCoordinates :=
  IrreducibleCharacter.twist
    (coordinateQuotientLinearHom twist)
    (degreeThreeBaseCharacter central)

@[simp]
theorem degreeThreeCharacter_degree
    (central : Fin 2) (twist : Fin 8) :
    (degreeThreeCharacter central twist).degree = 3 := by
  rw [degreeThreeCharacter, IrreducibleCharacter.twist_degree,
    degreeThreeBaseCharacter_degree]

/-- Every displayed degree-three row restricts to its prescribed
Schrödinger character. -/
theorem degreeThreeCharacter_isExtension
    (central : Fin 2) (twist : Fin 8) :
    IrreducibleCharacter.IsExtensionAlong
      (SemidirectProduct.inl :
        AlternatingSixThreeHeisenbergCoordinates →*
          AlternatingSixThreeNormalizerCoordinates)
      (degreeThreeHeisenbergCharacter central)
      (degreeThreeCharacter central twist) :=
  (degreeThreeBaseCharacter_isExtension central).twist_of_eq_one
    (coordinateQuotientLinearHom twist)
    (coordinateQuotientLinearHom_inl twist)

/-- The canonical Heisenberg subgroup inside the coordinate normalizer. -/
abbrev coordinateHeisenbergSubgroup :
    Subgroup AlternatingSixThreeNormalizerCoordinates :=
  (SemidirectProduct.inl :
    AlternatingSixThreeHeisenbergCoordinates →*
      AlternatingSixThreeNormalizerCoordinates).range

/-- The coordinate Heisenberg group is canonically equivalent to its
range in the semidirect product. -/
def coordinateHeisenbergEquivRange :
    AlternatingSixThreeHeisenbergCoordinates ≃*
      coordinateHeisenbergSubgroup :=
  MonoidHom.ofInjective SemidirectProduct.inl_injective

/-- A Schrödinger row transported to the canonical subgroup. -/
def degreeThreeHeisenbergRangeCharacter (central : Fin 2) :
    IrreducibleCharacter coordinateHeisenbergSubgroup :=
  (degreeThreeHeisenbergCharacter central).comap
    coordinateHeisenbergEquivRange.symm

/-- The chosen base row is an extension from the canonical subgroup. -/
theorem degreeThreeBaseCharacter_isRangeExtension
    (central : Fin 2) :
    IrreducibleCharacter.IsExtensionAlong
      coordinateHeisenbergSubgroup.subtype
      (degreeThreeHeisenbergRangeCharacter central)
      (degreeThreeBaseCharacter central) := by
  intro h
  change
    (degreeThreeBaseCharacter central).values
        (h : AlternatingSixThreeNormalizerCoordinates) =
      (degreeThreeHeisenbergRangeCharacter central).values h
  rw [← MonoidHom.apply_ofInjective_symm
    SemidirectProduct.inl_injective h]
  rw [degreeThreeBaseCharacter_isExtension central]
  rfl

/-- The quotient-linear rows, packaged as characters trivial on the
canonical Heisenberg subgroup. -/
def coordinateQuotientLinearHomTrivial (j : Fin 8) :
    IrreducibleCharacter.LinearCharactersTrivialOn
      coordinateHeisenbergSubgroup :=
  ⟨coordinateQuotientLinearHom j, by
    intro h
    obtain ⟨p, hp⟩ := h.property
    rw [← hp]
    exact coordinateQuotientLinearHom_inl j p⟩

theorem coordinateQuotientLinearHomTrivial_injective :
    Function.Injective coordinateQuotientLinearHomTrivial := by
  intro i j hij
  apply CyclicEight.linearHom_injective
  apply MonoidHom.ext
  intro c
  have h :=
    DFunLike.congr_fun
      (congrArg Subtype.val hij)
      (SemidirectProduct.inr c :
        AlternatingSixThreeNormalizerCoordinates)
  change
    coordinateQuotientLinearHom i
        (SemidirectProduct.inr c) =
      coordinateQuotientLinearHom j
        (SemidirectProduct.inr c) at h
  simpa [coordinateQuotientLinearHom] using h

/-- For a fixed central character, the eight quotient twists are
pairwise distinct. -/
theorem degreeThreeCharacter_twist_injective
    (central : Fin 2) :
    Function.Injective (degreeThreeCharacter central) := by
  intro i j hij
  apply coordinateQuotientLinearHomTrivial_injective
  apply
    (IrreducibleCharacter.twist_injective_on_linearCharactersTrivialOn
      (degreeThreeBaseCharacter_isRangeExtension central))
  exact hij

@[simp]
theorem degreeThreeCharacter_values_centralGenerator
    (central : Fin 2) (twist : Fin 8) :
    (degreeThreeCharacter central twist).values
        (SemidirectProduct.inl
          alternatingSixThreeHeisenbergCoordinateZ) =
      3 * threePhase (degreeThreeCentralParameter central) := by
  rw [degreeThreeCharacter_isExtension central twist]
  rw [degreeThreeHeisenbergCharacter_values_formula]
  simp [alternatingSixThreeHeisenbergCoordinateZ]

theorem degreeThreeCentralParameter_injective :
    Function.Injective degreeThreeCentralParameter := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim ((by decide : (1 : ZMod 3) ≠ 2) hij)
  · exact False.elim ((by decide : (2 : ZMod 3) ≠ 1) hij)
  · rfl

/-- All sixteen degree-three rows are pairwise distinct. -/
theorem degreeThreeCharacter_injective :
    Function.Injective
      (fun r : Fin 2 × Fin 8 =>
        degreeThreeCharacter r.1 r.2) := by
  rintro ⟨central, twist⟩ ⟨central', twist'⟩ hrows
  have hvalue :=
    congrArg
      (fun χ :
        IrreducibleCharacter
          AlternatingSixThreeNormalizerCoordinates =>
        χ.values
          (SemidirectProduct.inl
            alternatingSixThreeHeisenbergCoordinateZ))
      hrows
  rw [degreeThreeCharacter_values_centralGenerator,
    degreeThreeCharacter_values_centralGenerator] at hvalue
  have hphase :
      threePhase (degreeThreeCentralParameter central) =
        threePhase (degreeThreeCentralParameter central') := by
    exact mul_left_cancel₀ (by norm_num : (3 : ℂ) ≠ 0) hvalue
  have hcentral : central = central' :=
    degreeThreeCentralParameter_injective
      (ZMod.injective_stdAddChar hphase)
  subst central'
  have htwist : twist = twist' :=
    degreeThreeCharacter_twist_injective central hrows
  subst twist'
  rfl

end AlternatingSixThreeNormalizer
end McKayConjecture
