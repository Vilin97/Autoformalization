/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import McKayConjecture.GroupTheory.AlternatingSixSylowStructure
import McKayConjecture.GroupTheory.AlternatingSixPresentation
import McKayConjecture.GroupTheory.DihedralFourAutomorphisms

/-!
# The Sylow-two normalizer in `A₆`

The elements

* `r = a b a b⁻¹`, of order four, and
* `s = a`, of order two,

give a concrete copy of the dihedral group `D₈` inside `A₆`.  Its order is
the full two-part of `|A₆|`, so it is a Sylow subgroup.  This file computes
its normalizer, centralizer, and induced automorphism group, and then
transports the cardinality statements to every Sylow `2`-subgroup of `A₆`.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixNormalizerFactPrimeTwo :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The order-four rotation in the concrete dihedral Sylow subgroup. -/
def alternatingSixSylowTwoRotation : AlternatingSix :=
  alternatingSixPresentationA *
    alternatingSixPresentationB *
      alternatingSixPresentationA *
        alternatingSixPresentationB⁻¹

/-- The reflection in the concrete dihedral Sylow subgroup. -/
def alternatingSixSylowTwoReflection : AlternatingSix :=
  alternatingSixPresentationA

/-- The standard dihedral group of order eight maps to `A₆` by the chosen
rotation and reflection. -/
def dihedralFourToAlternatingSix :
    DihedralGroup 4 →* AlternatingSix where
  toFun
    | DihedralGroup.r i =>
        alternatingSixSylowTwoRotation ^ i.val
    | DihedralGroup.sr i =>
        alternatingSixSylowTwoReflection *
          alternatingSixSylowTwoRotation ^ i.val
  map_one' := by
    rfl
  map_mul' x y := by
    rcases x with i | i <;>
      rcases y with j | j <;>
        fin_cases i <;>
          fin_cases j <;>
            decide

/-- The concrete dihedral representation is faithful. -/
theorem dihedralFourToAlternatingSix_injective :
    Function.Injective dihedralFourToAlternatingSix := by
  intro x y hxy
  rcases x with i | i <;>
    rcases y with j | j <;>
      fin_cases i <;>
        fin_cases j
  all_goals
    first
    | rfl
    | exfalso
      revert hxy
      decide

/-- The explicit dihedral subgroup of `A₆`. -/
def alternatingSixDihedralSylowTwoSubgroup :
    Subgroup AlternatingSix :=
  dihedralFourToAlternatingSix.range

/-- The explicit dihedral subgroup has order eight. -/
@[simp]
theorem natCard_alternatingSixDihedralSylowTwoSubgroup :
    Nat.card alternatingSixDihedralSylowTwoSubgroup = 8 := by
  change Nat.card dihedralFourToAlternatingSix.range = 8
  calc
    Nat.card dihedralFourToAlternatingSix.range =
        Nat.card (DihedralGroup 4) :=
      (Nat.card_congr
        (MonoidHom.ofInjective
          dihedralFourToAlternatingSix_injective).toEquiv).symm
    _ = 8 := by
      rw [DihedralGroup.nat_card]

/-- The explicit dihedral subgroup, regarded as a Sylow `2`-subgroup. -/
def alternatingSixDihedralSylowTwo :
    Sylow 2 AlternatingSix :=
  Sylow.ofCard alternatingSixDihedralSylowTwoSubgroup (by
    rw [natCard_alternatingSixDihedralSylowTwoSubgroup,
      natCard_alternatingSix]
    have h :=
      DFunLike.congr_fun
        factorization_natCard_alternatingSix 2
    rw [natCard_alternatingSix] at h
    norm_num [Finsupp.add_apply, Finsupp.single_apply] at h
    rw [h]
    norm_num)

@[simp]
theorem alternatingSixDihedralSylowTwo_coe :
    (alternatingSixDihedralSylowTwo :
      Subgroup AlternatingSix) =
        alternatingSixDihedralSylowTwoSubgroup :=
  rfl

/-! ## The centralizer of the chosen rotation -/

/-- The chosen rotation has cycle type `(4)(2)`. -/
@[simp]
theorem alternatingSixSylowTwoRotation_cycleType :
    ((alternatingSixSylowTwoRotation :
      AlternatingSix) :
        Equiv.Perm (Fin 6)).cycleType =
      {4, 2} := by
  decide

/-- Its full symmetric-group centralizer has order eight. -/
@[simp]
theorem natCard_perm_centralizer_alternatingSixSylowTwoRotation :
    Nat.card
        (Subgroup.centralizer
          ({((alternatingSixSylowTwoRotation :
              AlternatingSix) :
              Equiv.Perm (Fin 6))} :
            Set (Equiv.Perm (Fin 6)))) =
      8 := by
  rw [Equiv.Perm.nat_card_centralizer,
    alternatingSixSylowTwoRotation_cycleType]
  norm_num

/-- The sign map restricted to the full permutation centralizer. -/
def alternatingSixSylowTwoRotationCentralizerSign :
    Subgroup.centralizer
        ({((alternatingSixSylowTwoRotation :
            AlternatingSix) :
            Equiv.Perm (Fin 6))} :
          Set (Equiv.Perm (Fin 6))) →*
      ℤˣ :=
  Equiv.Perm.sign.comp
    (Subgroup.centralizer
      ({((alternatingSixSylowTwoRotation :
          AlternatingSix) :
          Equiv.Perm (Fin 6))} :
        Set (Equiv.Perm (Fin 6)))).subtype

/-- Centralizing the chosen rotation inside `A₆` is equivalent to lying in
the sign kernel of its full permutation centralizer. -/
def alternatingSixSylowTwoRotationCentralizerEquivSignKer :
    Subgroup.centralizer
        ({alternatingSixSylowTwoRotation} :
          Set AlternatingSix) ≃*
      alternatingSixSylowTwoRotationCentralizerSign.ker where
  toFun x :=
    ⟨⟨(x : AlternatingSix),
        by
          have hx := x.property
          rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
          exact congrArg Subtype.val hx⟩,
      by
        rw [MonoidHom.mem_ker]
        change
          Equiv.Perm.sign
              ((x : AlternatingSix) :
                Equiv.Perm (Fin 6)) =
            1
        rw [← Equiv.Perm.mem_alternatingGroup]
        exact (x : AlternatingSix).property⟩
  invFun x :=
    ⟨⟨(x.1 : Equiv.Perm (Fin 6)),
        by
          rw [Equiv.Perm.mem_alternatingGroup]
          have hx := MonoidHom.mem_ker.mp x.property
          exact hx⟩,
      by
        have hx := x.1.property
        rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
        exact Subtype.ext hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The transposition of the last two points centralizes the chosen
rotation and has odd sign. -/
def alternatingSixSylowTwoRotationOddCentralizer :
    Subgroup.centralizer
      ({((alternatingSixSylowTwoRotation :
          AlternatingSix) :
          Equiv.Perm (Fin 6))} :
        Set (Equiv.Perm (Fin 6))) :=
  ⟨Equiv.swap (4 : Fin 6) 5, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    decide⟩

@[simp]
theorem alternatingSixSylowTwoRotationCentralizerSign_odd :
    alternatingSixSylowTwoRotationCentralizerSign
        alternatingSixSylowTwoRotationOddCentralizer =
      -1 := by
  simp [alternatingSixSylowTwoRotationCentralizerSign,
    alternatingSixSylowTwoRotationOddCentralizer]

/-- Both signs occur in the full permutation centralizer. -/
theorem alternatingSixSylowTwoRotationCentralizerSign_surjective :
    Function.Surjective
      alternatingSixSylowTwoRotationCentralizerSign := by
  intro signValue
  rcases Int.units_eq_one_or signValue with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact
      ⟨alternatingSixSylowTwoRotationOddCentralizer,
        alternatingSixSylowTwoRotationCentralizerSign_odd⟩

/-- The centralizer of the chosen rotation inside `A₆` has order four. -/
@[simp]
theorem natCard_alternatingSix_centralizer_sylowTwoRotation :
    Nat.card
        (Subgroup.centralizer
          ({alternatingSixSylowTwoRotation} :
            Set AlternatingSix)) =
      4 := by
  let f :=
    alternatingSixSylowTwoRotationCentralizerSign
  have hrange : f.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      alternatingSixSylowTwoRotationCentralizerSign_surjective
  have hproduct :
      Nat.card f.ker * Nat.card f.range =
        Nat.card
          (Subgroup.centralizer
            ({((alternatingSixSylowTwoRotation :
                AlternatingSix) :
                Equiv.Perm (Fin 6))} :
              Set (Equiv.Perm (Fin 6)))) := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card f.ker * f.ker.index := by
        rw [Subgroup.index_ker]
      _ =
          Nat.card
            (Subgroup.centralizer
              ({((alternatingSixSylowTwoRotation :
                  AlternatingSix) :
                  Equiv.Perm (Fin 6))} :
                Set (Equiv.Perm (Fin 6)))) :=
        f.ker.card_mul_index
  have hUnits : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  rw [hrange, Subgroup.card_top,
    hUnits,
    natCard_perm_centralizer_alternatingSixSylowTwoRotation]
      at hproduct
  calc
    Nat.card
        (Subgroup.centralizer
          ({alternatingSixSylowTwoRotation} :
            Set AlternatingSix)) =
        Nat.card f.ker :=
      Nat.card_congr
        alternatingSixSylowTwoRotationCentralizerEquivSignKer.toEquiv
    _ = 4 := by
      change Nat.card f.ker * 2 = 8 at hproduct
      omega

/-- The center of the explicit Sylow `2`-subgroup has order two. -/
@[simp]
theorem natCard_center_alternatingSixDihedralSylowTwo :
    Nat.card (Subgroup.center alternatingSixDihedralSylowTwo) =
      2 := by
  change
    Nat.card
        (Subgroup.center dihedralFourToAlternatingSix.range) =
      2
  calc
    Nat.card
        (Subgroup.center dihedralFourToAlternatingSix.range) =
        Nat.card (Subgroup.center (DihedralGroup 4)) :=
      (Nat.card_congr
        (Subgroup.centerCongr
          (MonoidHom.ofInjective
            dihedralFourToAlternatingSix_injective)).toEquiv).symm
    _ = 2 := natCard_center_dihedralGroup_four

/-- The explicit Sylow `2`-subgroup is canonically the chosen copy of
`D₈`. -/
def dihedralFourEquivAlternatingSixDihedralSylowTwo :
    DihedralGroup 4 ≃*
      alternatingSixDihedralSylowTwo := by
  change
    DihedralGroup 4 ≃*
      dihedralFourToAlternatingSix.range
  exact
    MonoidHom.ofInjective
      dihedralFourToAlternatingSix_injective

/-- The automorphism group of the explicit Sylow subgroup has order
eight. -/
@[simp]
theorem natCard_mulAut_alternatingSixDihedralSylowTwo :
    Nat.card (MulAut alternatingSixDihedralSylowTwo) = 8 := by
  rw [Nat.card_congr
      (MulAut.congr
        dihedralFourEquivAlternatingSixDihedralSylowTwo.symm).toEquiv,
    natCard_mulAut_dihedralGroup_four]

/-- The chosen rotation belongs to the explicit Sylow subgroup. -/
theorem alternatingSixSylowTwoRotation_mem_dihedralSylowTwo :
    alternatingSixSylowTwoRotation ∈
      (alternatingSixDihedralSylowTwo :
        Subgroup AlternatingSix) := by
  change
    alternatingSixSylowTwoRotation ∈
      dihedralFourToAlternatingSix.range
  refine
    ⟨DihedralGroup.r (1 : ZMod 4), ?_⟩
  change
    alternatingSixSylowTwoRotation ^
        (1 : ZMod 4).val =
      alternatingSixSylowTwoRotation
  rw [show (1 : ZMod 4).val = 1 by
    exact ZMod.val_cast_of_lt (by norm_num)]
  simp

/-- Centralizing the full explicit Sylow subgroup implies centralizing its
chosen rotation. -/
theorem centralizer_alternatingSixDihedralSylowTwo_le_rotation :
    Subgroup.centralizer
        (alternatingSixDihedralSylowTwo :
          Set AlternatingSix) ≤
      Subgroup.centralizer
        ({alternatingSixSylowTwoRotation} :
          Set AlternatingSix) :=
  Subgroup.centralizer_le
    (Set.singleton_subset_iff.mpr
      alternatingSixSylowTwoRotation_mem_dihedralSylowTwo)

/-- The centralizer of the explicit Sylow subgroup has order dividing
four. -/
theorem natCard_centralizer_alternatingSixDihedralSylowTwo_dvd_four :
    Nat.card
        (Subgroup.centralizer
          (alternatingSixDihedralSylowTwo :
            Set AlternatingSix)) ∣
      4 := by
  rw [← natCard_alternatingSix_centralizer_sylowTwoRotation]
  exact
    Subgroup.card_dvd_of_le
      centralizer_alternatingSixDihedralSylowTwo_le_rotation

/-- The kernel of the normalizer action for the explicit Sylow subgroup
has order dividing four. -/
theorem natCard_alternatingSixDihedralSylowTwo_normalizerMonoidHom_ker_dvd_four :
    Nat.card
        (alternatingSixDihedralSylowTwo :
          Subgroup AlternatingSix).normalizerMonoidHom.ker ∣
      4 := by
  let P :=
    (alternatingSixDihedralSylowTwo :
      Subgroup AlternatingSix)
  let N :=
    Subgroup.normalizer (P : Set AlternatingSix)
  let f := P.normalizerMonoidHom
  have hcard :
      Nat.card f.ker =
        Nat.card
          (Subgroup.centralizer
            (P : Set AlternatingSix)) := by
    rw [Subgroup.normalizerMonoidHom_ker]
    exact
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (Subgroup.centralizer_le_normalizer
            (P : Set AlternatingSix))).toEquiv
  change Nat.card f.ker ∣ 4
  rw [hcard]
  exact
    natCard_centralizer_alternatingSixDihedralSylowTwo_dvd_four

/-- The range of the normalizer action for the explicit Sylow subgroup
has order dividing eight. -/
theorem natCard_alternatingSixDihedralSylowTwo_normalizerMonoidHom_range_dvd_eight :
    Nat.card
        (alternatingSixDihedralSylowTwo :
          Subgroup AlternatingSix).normalizerMonoidHom.range ∣
      8 := by
  rw [← natCard_mulAut_alternatingSixDihedralSylowTwo]
  exact
    (alternatingSixDihedralSylowTwo :
      Subgroup AlternatingSix).normalizerMonoidHom.range.card_subgroup_dvd_card

/-- The order of the explicit Sylow normalizer divides thirty-two. -/
theorem natCard_normalizer_alternatingSixDihedralSylowTwo_dvd_thirtyTwo :
    Nat.card
        (Subgroup.normalizer
          (alternatingSixDihedralSylowTwo :
            Set AlternatingSix)) ∣
      32 := by
  let P :=
    (alternatingSixDihedralSylowTwo :
      Subgroup AlternatingSix)
  let f := P.normalizerMonoidHom
  have hcard :
      Nat.card
          (Subgroup.normalizer
            (P : Set AlternatingSix)) =
        Nat.card f.ker * Nat.card f.range := by
    calc
      Nat.card
          (Subgroup.normalizer
            (P : Set AlternatingSix)) =
          Nat.card f.ker * f.ker.index :=
        f.ker.card_mul_index.symm
      _ = Nat.card f.ker * Nat.card f.range := by
        rw [Subgroup.index_ker]
  change
    Nat.card
        (Subgroup.normalizer
          (P : Set AlternatingSix)) ∣
      32
  rw [hcard]
  exact
    Nat.mul_dvd_mul
      natCard_alternatingSixDihedralSylowTwo_normalizerMonoidHom_ker_dvd_four
      natCard_alternatingSixDihedralSylowTwo_normalizerMonoidHom_range_dvd_eight

/-- The explicit dihedral Sylow subgroup is self-normalizing. -/
@[simp]
theorem natCard_normalizer_alternatingSixDihedralSylowTwo :
    Nat.card
        (Subgroup.normalizer
          (alternatingSixDihedralSylowTwo :
            Set AlternatingSix)) =
      8 := by
  let P :=
    (alternatingSixDihedralSylowTwo :
      Subgroup AlternatingSix)
  let N :=
    Subgroup.normalizer (P : Set AlternatingSix)
  have hnormalizerDvdThirtyTwo :
      Nat.card N ∣ 32 :=
    natCard_normalizer_alternatingSixDihedralSylowTwo_dvd_thirtyTwo
  have hnormalizerDvdThreeSixty :
      Nat.card N ∣ 360 := by
    rw [← natCard_alternatingSix]
    exact N.card_subgroup_dvd_card
  have hnormalizerDvdEight :
      Nat.card N ∣ 8 := by
    have :=
      Nat.dvd_gcd
        hnormalizerDvdThirtyTwo
        hnormalizerDvdThreeSixty
    norm_num at this ⊢
    exact this
  have heightLe :
      8 ≤ Nat.card N := by
    rw [← natCard_alternatingSixDihedralSylowTwoSubgroup]
    exact
      Subgroup.card_le_of_le
        (P.le_normalizer)
  change Nat.card N = 8
  exact
    Nat.le_antisymm
      (Nat.le_of_dvd (by norm_num)
        hnormalizerDvdEight)
      heightLe

/-- The normalizer of the explicit Sylow subgroup is the subgroup itself. -/
theorem normalizer_alternatingSixDihedralSylowTwo_eq :
    Subgroup.normalizer
        (alternatingSixDihedralSylowTwo :
          Set AlternatingSix) =
      (alternatingSixDihedralSylowTwo :
        Subgroup AlternatingSix) := by
  symm
  apply
    Subgroup.eq_of_le_of_card_ge
      (alternatingSixDihedralSylowTwo :
        Subgroup AlternatingSix).le_normalizer
  have hnormalizer :
      Nat.card
          (Subgroup.normalizer
            (alternatingSixDihedralSylowTwo :
              Set AlternatingSix)) =
        8 :=
    natCard_normalizer_alternatingSixDihedralSylowTwo
  have hsylow :
      Nat.card alternatingSixDihedralSylowTwo = 8 :=
    natCard_sylowTwo_alternatingSix
      alternatingSixDihedralSylowTwo
  exact le_of_eq (hnormalizer.trans hsylow.symm)

/-- Inside a self-normalizing subgroup, its ambient centralizer becomes
its intrinsic center. -/
theorem centralizer_subgroupOf_alternatingSixDihedralSylowTwo_eq_center :
    (Subgroup.centralizer
        (alternatingSixDihedralSylowTwo :
          Set AlternatingSix)).subgroupOf
      (alternatingSixDihedralSylowTwo :
        Subgroup AlternatingSix) =
      Subgroup.center alternatingSixDihedralSylowTwo := by
  ext x
  rw [Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro hx y
    apply Subtype.ext
    exact hx (y : AlternatingSix) y.property
  · intro hx y hy
    exact congrArg Subtype.val (hx ⟨y, hy⟩)

/-- The centralizer of the explicit Sylow subgroup has order two. -/
@[simp]
theorem natCard_centralizer_alternatingSixDihedralSylowTwo :
    Nat.card
        (Subgroup.centralizer
          (alternatingSixDihedralSylowTwo :
            Set AlternatingSix)) =
      2 := by
  let P :=
    (alternatingSixDihedralSylowTwo :
      Subgroup AlternatingSix)
  let C :=
    Subgroup.centralizer (P : Set AlternatingSix)
  have hCP : C ≤ P := by
    change
      Subgroup.centralizer
          (alternatingSixDihedralSylowTwo :
            Set AlternatingSix) ≤
        (alternatingSixDihedralSylowTwo :
          Subgroup AlternatingSix)
    rw [← normalizer_alternatingSixDihedralSylowTwo_eq]
    exact
      Subgroup.centralizer_le_normalizer
        (alternatingSixDihedralSylowTwo :
          Set AlternatingSix)
  calc
    Nat.card C =
        Nat.card (C.subgroupOf P) :=
      (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hCP).toEquiv).symm
    _ =
        Nat.card
          (Subgroup.center
            alternatingSixDihedralSylowTwo) := by
      change
        Nat.card
            ((Subgroup.centralizer
              (alternatingSixDihedralSylowTwo :
                Set AlternatingSix)).subgroupOf
                  (alternatingSixDihedralSylowTwo :
                    Subgroup AlternatingSix)) =
          Nat.card
            (Subgroup.center
              alternatingSixDihedralSylowTwo)
      rw [
        centralizer_subgroupOf_alternatingSixDihedralSylowTwo_eq_center]
    _ = 2 :=
      natCard_center_alternatingSixDihedralSylowTwo

/-- The induced automorphism group of the explicit Sylow subgroup has
order four. -/
@[simp]
theorem natCard_alternatingSixDihedralSylowTwo_normalizerMonoidHom_range :
    Nat.card
        (alternatingSixDihedralSylowTwo :
          Subgroup AlternatingSix).normalizerMonoidHom.range =
      4 := by
  let P :=
    (alternatingSixDihedralSylowTwo :
      Subgroup AlternatingSix)
  let f := P.normalizerMonoidHom
  have hker :
      Nat.card f.ker = 2 := by
    rw [Subgroup.normalizerMonoidHom_ker]
    calc
      Nat.card
          ((Subgroup.centralizer
            (P : Set AlternatingSix)).subgroupOf
              (Subgroup.normalizer
                (P : Set AlternatingSix))) =
          Nat.card
            (Subgroup.centralizer
              (P : Set AlternatingSix)) :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe
            (Subgroup.centralizer_le_normalizer
              (P : Set AlternatingSix))).toEquiv
      _ = 2 :=
        natCard_centralizer_alternatingSixDihedralSylowTwo
  have hcard :
      Nat.card f.ker * Nat.card f.range =
        Nat.card
          (Subgroup.normalizer
            (P : Set AlternatingSix)) := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card f.ker * f.ker.index := by
        rw [Subgroup.index_ker]
      _ =
          Nat.card
            (Subgroup.normalizer
              (P : Set AlternatingSix)) :=
        f.ker.card_mul_index
  change Nat.card f.range = 4
  have hnormalizer :
      Nat.card
          (Subgroup.normalizer
            (P : Set AlternatingSix)) =
        8 := by
    change
      Nat.card
          (Subgroup.normalizer
            (alternatingSixDihedralSylowTwo :
              Set AlternatingSix)) =
        8
    exact
      natCard_normalizer_alternatingSixDihedralSylowTwo
  rw [hker, hnormalizer] at hcard
  omega

/-! ## All Sylow `2`-subgroups of `A₆` -/

/-- There are forty-five Sylow `2`-subgroups in `A₆`. -/
@[simp]
theorem natCard_sylowTwoSubgroups_alternatingSix :
    Nat.card (Sylow 2 AlternatingSix) = 45 := by
  let N :=
    Subgroup.normalizer
      (alternatingSixDihedralSylowTwo :
        Set AlternatingSix)
  rw [Sylow.card_eq_index_normalizer
    alternatingSixDihedralSylowTwo]
  have hcard := N.card_mul_index
  change Nat.card N * N.index =
      Nat.card AlternatingSix at hcard
  have hnormalizer : Nat.card N = 8 :=
    natCard_normalizer_alternatingSixDihedralSylowTwo
  rw [hnormalizer, natCard_alternatingSix] at hcard
  have hcancel :
      8 * N.index = 8 * 45 := by
    norm_num at hcard ⊢
    exact hcard
  exact Nat.mul_left_cancel (by norm_num) hcancel

/-- Every Sylow `2`-normalizer in `A₆` has order eight. -/
@[simp]
theorem natCard_normalizer_sylowTwo_alternatingSix
    (P : Sylow 2 AlternatingSix) :
    Nat.card
        (Subgroup.normalizer
          ((P : Subgroup AlternatingSix) :
            Set AlternatingSix)) =
      8 := by
  let N :=
    Subgroup.normalizer
      ((P : Subgroup AlternatingSix) :
        Set AlternatingSix)
  have hindex :
      N.index = 45 := by
    have h :=
      Sylow.card_eq_index_normalizer P
    change
      Nat.card (Sylow 2 AlternatingSix) =
        N.index at h
    exact
      h.symm.trans
        natCard_sylowTwoSubgroups_alternatingSix
  have hcard := N.card_mul_index
  change Nat.card N * N.index =
      Nat.card AlternatingSix at hcard
  rw [hindex, natCard_alternatingSix] at hcard
  have hcancel :
      Nat.card N * 45 = 8 * 45 := by
    norm_num at hcard ⊢
    exact hcard
  exact Nat.mul_right_cancel (by norm_num) hcancel

/-- Every Sylow `2`-subgroup of `A₆` is self-normalizing. -/
theorem normalizer_sylowTwo_alternatingSix_eq
    (P : Sylow 2 AlternatingSix) :
    Subgroup.normalizer
        ((P : Subgroup AlternatingSix) :
          Set AlternatingSix) =
      (P : Subgroup AlternatingSix) := by
  symm
  apply
    Subgroup.eq_of_le_of_card_ge
      (P : Subgroup AlternatingSix).le_normalizer
  rw [natCard_normalizer_sylowTwo_alternatingSix,
    natCard_sylowTwo_alternatingSix]

/-- Every Sylow `2`-subgroup of `A₆` is dihedral of order eight. -/
def alternatingSixSylowTwoEquivDihedralFour
    (P : Sylow 2 AlternatingSix) :
    P ≃* DihedralGroup 4 :=
  (Sylow.equiv P alternatingSixDihedralSylowTwo).trans
    dihedralFourEquivAlternatingSixDihedralSylowTwo.symm

/-- The center of every Sylow `2`-subgroup of `A₆` has order two. -/
@[simp]
theorem natCard_center_sylowTwo_alternatingSix
    (P : Sylow 2 AlternatingSix) :
    Nat.card (Subgroup.center P) = 2 := by
  rw [Nat.card_congr
      (Subgroup.centerCongr
        (alternatingSixSylowTwoEquivDihedralFour P)).toEquiv,
    natCard_center_dihedralGroup_four]

/-- The automorphism group of every Sylow `2`-subgroup of `A₆` has order
eight. -/
@[simp]
theorem natCard_mulAut_sylowTwo_alternatingSix
    (P : Sylow 2 AlternatingSix) :
    Nat.card (MulAut P) = 8 := by
  rw [Nat.card_congr
      (MulAut.congr
        (alternatingSixSylowTwoEquivDihedralFour P)).toEquiv,
    natCard_mulAut_dihedralGroup_four]

/-- The ambient centralizer, viewed inside a self-normalizing Sylow
subgroup, is its intrinsic center. -/
theorem centralizer_subgroupOf_sylowTwo_alternatingSix_eq_center
    (P : Sylow 2 AlternatingSix) :
    (Subgroup.centralizer
        ((P : Subgroup AlternatingSix) :
          Set AlternatingSix)).subgroupOf
      (P : Subgroup AlternatingSix) =
      Subgroup.center P := by
  ext x
  rw [Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro hx y
    apply Subtype.ext
    exact hx (y : AlternatingSix) y.property
  · intro hx y hy
    exact congrArg Subtype.val (hx ⟨y, hy⟩)

/-- The centralizer in `A₆` of every Sylow `2`-subgroup has order two. -/
@[simp]
theorem natCard_centralizer_sylowTwo_alternatingSix
    (P : Sylow 2 AlternatingSix) :
    Nat.card
        (Subgroup.centralizer
          ((P : Subgroup AlternatingSix) :
            Set AlternatingSix)) =
      2 := by
  let Psub :=
    (P : Subgroup AlternatingSix)
  let C :=
    Subgroup.centralizer
      (Psub : Set AlternatingSix)
  have hCP : C ≤ Psub := by
    change
      Subgroup.centralizer
          ((P : Subgroup AlternatingSix) :
            Set AlternatingSix) ≤
        (P : Subgroup AlternatingSix)
    exact
      (Subgroup.centralizer_le_normalizer
          ((P : Subgroup AlternatingSix) :
            Set AlternatingSix)).trans_eq
        (normalizer_sylowTwo_alternatingSix_eq P)
  calc
    Nat.card C =
        Nat.card (C.subgroupOf Psub) :=
      (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hCP).toEquiv).symm
    _ = Nat.card (Subgroup.center P) := by
      change
        Nat.card
            ((Subgroup.centralizer
              ((P : Subgroup AlternatingSix) :
                Set AlternatingSix)).subgroupOf
                  (P : Subgroup AlternatingSix)) =
          Nat.card (Subgroup.center P)
      rw [
        centralizer_subgroupOf_sylowTwo_alternatingSix_eq_center]
    _ = 2 :=
      natCard_center_sylowTwo_alternatingSix P

/-- Conjugation by the Sylow normalizer induces a group of four
automorphisms. -/
@[simp]
theorem natCard_sylowTwo_normalizerMonoidHom_range
    (P : Sylow 2 AlternatingSix) :
    Nat.card
        (P : Subgroup AlternatingSix).normalizerMonoidHom.range =
      4 := by
  let Psub :=
    (P : Subgroup AlternatingSix)
  let f := Psub.normalizerMonoidHom
  have hker :
      Nat.card f.ker = 2 := by
    rw [Subgroup.normalizerMonoidHom_ker]
    calc
      Nat.card
          ((Subgroup.centralizer
            (Psub : Set AlternatingSix)).subgroupOf
              (Subgroup.normalizer
                (Psub : Set AlternatingSix))) =
          Nat.card
            (Subgroup.centralizer
              (Psub : Set AlternatingSix)) :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe
            (Subgroup.centralizer_le_normalizer
              (Psub : Set AlternatingSix))).toEquiv
      _ = 2 := by
        change
          Nat.card
              (Subgroup.centralizer
                ((P : Subgroup AlternatingSix) :
                  Set AlternatingSix)) =
            2
        exact
          natCard_centralizer_sylowTwo_alternatingSix P
  have hcard :
      Nat.card f.ker * Nat.card f.range =
        Nat.card
          (Subgroup.normalizer
            (Psub : Set AlternatingSix)) := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card f.ker * f.ker.index := by
        rw [Subgroup.index_ker]
      _ =
          Nat.card
            (Subgroup.normalizer
              (Psub : Set AlternatingSix)) :=
        f.ker.card_mul_index
  have hnormalizer :
      Nat.card
          (Subgroup.normalizer
            (Psub : Set AlternatingSix)) =
        8 := by
    change
      Nat.card
          (Subgroup.normalizer
            ((P : Subgroup AlternatingSix) :
              Set AlternatingSix)) =
        8
    exact
      natCard_normalizer_sylowTwo_alternatingSix P
  change Nat.card f.range = 4
  rw [hker, hnormalizer] at hcard
  omega

/-- The Sylow centralizer has relative index four in the normalizer. -/
theorem relIndex_centralizer_sylowTwo_normalizer_alternatingSix
    (P : Sylow 2 AlternatingSix) :
    (Subgroup.centralizer
        ((P : Subgroup AlternatingSix) :
          Set AlternatingSix)).relIndex
      (Subgroup.normalizer
        ((P : Subgroup AlternatingSix) :
          Set AlternatingSix)) =
      4 := by
  change
    ((Subgroup.centralizer
      ((P : Subgroup AlternatingSix) :
        Set AlternatingSix)).subgroupOf
          (Subgroup.normalizer
            ((P : Subgroup AlternatingSix) :
              Set AlternatingSix))).index =
      4
  rw [← Subgroup.normalizerMonoidHom_ker,
    Subgroup.index_ker]
  exact natCard_sylowTwo_normalizerMonoidHom_range P

end GroupTheory
end McKayConjecture
