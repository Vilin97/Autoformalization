/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.Analysis.Complex.Polynomial.Basic
import McKayConjecture.CharacterTriple.FactorSetCentralExtension
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionNormalizer
import McKayConjecture.CharacterTriple.FactorSetCohomology
import McKayConjecture.CharacterTriple.FiniteFactorNormalization

/-!
# Factor sets on groups of squarefree order

The Schur multiplier of a finite group of squarefree order is mathematically
trivial.  This file develops the part of that theorem supported directly by
the pinned library:

* an explicit splitting of every normalized factor set on a finite cyclic
  group with values in the units of an algebraically closed field;
* squarefree-order groups are `Z`-groups;
* hence their standard metacyclic decomposition has two cyclic factors of
  coprime order, and the restriction of a factor set to either factor is an
  explicit coboundary.

The remaining global step is the restriction/corestriction (Sylow-detection)
argument for second cohomology.  The pinned group-cohomology library has
restriction and Shapiro maps, but no cohomological corestriction or theorem
that restriction followed by corestriction is multiplication by the subgroup
index.  Consequently the final global vanishing theorem is not asserted here.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

universe u v

variable {G : Type u} {A : Type v}
variable [Group G] [CommGroup A]

namespace CentralExtensionGroup

/-- A multiplicative section of the central-extension projection gives an
explicit gauge which trivializes the factor set. -/
theorem gauge_coefficient_section_eq_one
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (s : G →* CentralExtensionGroup alpha halpha)
    (hs :
      (projection alpha halpha).comp s =
        MonoidHom.id G) :
    alpha.gauge (fun g ↦ coefficient alpha halpha (s g)) =
      FactorSet.one := by
  ext g h
  have hbase (x : G) :
      base alpha halpha (s x) = x := by
    have hx := DFunLike.congr_fun hs x
    exact hx
  have hcoefficient :=
    congrArg (coefficient alpha halpha) (map_mul s g h)
  simp only [coefficient_mul, hbase] at hcoefficient
  rw [gauge_apply, one_apply, hcoefficient]
  simp only [div_eq_mul_inv, mul_inv_rev]
  simp [mul_assoc, mul_comm, mul_left_comm]

end CentralExtensionGroup

/-- A gauge trivialization exhibits the original factor set itself as a
multiplicative two-coboundary. -/
theorem isMulCoboundary₂_of_gauge_eq_one
    (alpha : FactorSet G A)
    (c : G → A)
    (h : alpha.gauge c = FactorSet.one) :
    letI := trivialMulDistribMulAction G A
    groupCohomology.IsMulCoboundary₂
      (fun x : G × G ↦ alpha x.1 x.2) := by
  letI := trivialMulDistribMulAction G A
  refine ⟨fun g ↦ (c g)⁻¹, ?_⟩
  intro g k
  have hvalue :=
    congrArg
      (fun beta : FactorSet G A ↦ beta g k) h
  simp only [gauge_apply, one_apply] at hvalue
  change
    (c k)⁻¹ / (c (g * k))⁻¹ * (c g)⁻¹ =
      alpha g k
  rw [div_eq_mul_inv, inv_inv]
  calc
    (c k)⁻¹ * c (g * k) * (c g)⁻¹ =
        (c g * c k / c (g * k))⁻¹ := by
          simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
          ac_rfl
    _ = alpha g k := by
          exact mul_eq_one_iff_inv_eq.mp hvalue

section Cyclic

variable {K : Type v} [Field K] [IsAlgClosed K]
variable [Finite G] [IsCyclic G]

/-- Every normalized factor set on a finite cyclic group, with values in
the units of an algebraically closed field, admits a multiplicative section
of its central extension. -/
theorem exists_centralExtensionGroup_section_of_isCyclic
    (alpha : FactorSet G Kˣ)
    (halpha : alpha.IsNormalized) :
    ∃ s : G →* CentralExtensionGroup alpha halpha,
      (CentralExtensionGroup.projection alpha halpha).comp s =
        MonoidHom.id G := by
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := G)
  let E := CentralExtensionGroup alpha halpha
  let x : E :=
    CentralExtensionGroup.mk alpha halpha z 1
  let n := orderOf z
  have hn : 0 < n :=
    orderOf_pos z
  let a : Kˣ :=
    CentralExtensionGroup.coefficient alpha halpha (x ^ n)
  let b : Kˣ :=
    unitNthRoot a⁻¹ n hn
  let y : E :=
    CentralExtensionGroup.coefficientEmbedding alpha halpha b * x
  have hxpow :
      x ^ n =
        CentralExtensionGroup.coefficientEmbedding
          alpha halpha a := by
    apply CentralExtensionGroup.ext alpha halpha
    · change
        (CentralExtensionGroup.projection alpha halpha) (x ^ n) =
          (CentralExtensionGroup.projection alpha halpha)
            (CentralExtensionGroup.coefficientEmbedding
              alpha halpha a)
      rw [map_pow]
      change z ^ n = 1
      simpa only [n] using pow_orderOf_eq_one z
    · rfl
  have hcentral :
      CentralExtensionGroup.coefficientEmbedding
          alpha halpha b ∈
        Subgroup.center E :=
    CentralExtensionGroup.coefficientEmbedding_range_le_center
      alpha halpha ⟨b, rfl⟩
  have hcommute :
      Commute
        (CentralExtensionGroup.coefficientEmbedding
          alpha halpha b) x :=
    ((Subgroup.mem_center_iff.mp hcentral) x).symm
  have hypow : y ^ n = 1 := by
    calc
      y ^ n =
          (CentralExtensionGroup.coefficientEmbedding
              alpha halpha b) ^ n * x ^ n :=
        hcommute.mul_pow n
      _ =
          CentralExtensionGroup.coefficientEmbedding
              alpha halpha (b ^ n) *
            CentralExtensionGroup.coefficientEmbedding
              alpha halpha a := by
        rw [map_pow, hxpow]
      _ =
          CentralExtensionGroup.coefficientEmbedding
            alpha halpha (a⁻¹ * a) := by
        rw [unitNthRoot_pow]
        exact
          (map_mul
            (CentralExtensionGroup.coefficientEmbedding
              alpha halpha) a⁻¹ a).symm
      _ = 1 := by
        rw [inv_mul_cancel]
        exact
          map_one
            (CentralExtensionGroup.coefficientEmbedding
              alpha halpha)
  have hyorder :
      orderOf y ∣ orderOf z :=
    orderOf_dvd_iff_pow_eq_one.mpr hypow
  let s : G →* E :=
    monoidHomOfForallMemZpowers hz hyorder
  refine ⟨s, ?_⟩
  apply
    (MonoidHom.eq_iff_eq_on_generator hz _ _).mpr
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, s,
    monoidHomOfForallMemZpowers_apply_gen]
  change
    CentralExtensionGroup.base alpha halpha y = z
  change (1 : G) * z = z
  exact one_mul z

/-- Every normalized factor set on a finite cyclic group with values in
`Kˣ` is a multiplicative two-coboundary. -/
theorem isMulCoboundary₂_of_isCyclic
    (alpha : FactorSet G Kˣ)
    (halpha : alpha.IsNormalized) :
    letI := trivialMulDistribMulAction G Kˣ
    groupCohomology.IsMulCoboundary₂
      (fun x : G × G ↦ alpha x.1 x.2) := by
  obtain ⟨s, hs⟩ :=
    alpha.exists_centralExtensionGroup_section_of_isCyclic
      halpha
  exact
    alpha.isMulCoboundary₂_of_gauge_eq_one
      (fun g ↦
        CentralExtensionGroup.coefficient alpha halpha (s g))
      (CentralExtensionGroup.gauge_coefficient_section_eq_one
        alpha halpha s hs)

end Cyclic

section CyclicH2

variable {G₀ K₀ : Type}
variable [Group G₀] [Field K₀] [IsAlgClosed K₀]
variable [Finite G₀] [IsCyclic G₀]

/-- Equivalently, every normalized factor set on a finite cyclic group has
zero second-cohomology class. -/
theorem h2Class_eq_zero_of_isCyclic
    (alpha : FactorSet G₀ K₀ˣ)
    (halpha : alpha.IsNormalized) :
    letI := trivialMulDistribMulAction G₀ K₀ˣ
    alpha.h2Class = 0 := by
  letI := trivialMulDistribMulAction G₀ K₀ˣ
  apply
    (groupCohomology.H2π_eq_zero_iff
      (A := Rep.ofMulDistribMulAction G₀ K₀ˣ)
      alpha.toMathlibCocycle).mpr
  exact
    (groupCohomology.coboundariesOfIsMulCoboundary₂
      (alpha.isMulCoboundary₂_of_isCyclic halpha)).2

end CyclicH2

section SquarefreeStructure

variable [Finite G]

omit [Finite G] in
/-- A finite group of squarefree order has cyclic Sylow subgroups. -/
theorem isZGroup_of_squarefree_card
    (hG : Squarefree (Nat.card G)) :
    IsZGroup G :=
  IsZGroup.of_squarefree hG

/-- The pinned classification of `Z`-groups gives a squarefree-order group
as a semidirect product of two cyclic subgroups of coprime order. -/
theorem exists_cyclic_coprime_semidirect_decomposition
    (hG : Squarefree (Nat.card G)) :
    ∃ (N H : Subgroup G) (phi : H →* MulAut N)
        (_e : G ≃* N ⋊[phi] H),
      IsCyclic H ∧
        IsCyclic N ∧
        Nat.Coprime (Nat.card N) (Nat.card H) := by
  letI : IsZGroup G :=
    IsZGroup.of_squarefree hG
  exact
    isZGroup_iff_exists_mulEquiv.mp inferInstance

/-- A finite commutative group of squarefree order is cyclic.  This is the
abelian specialization of the `Z`-group theorem in the pinned library. -/
theorem isCyclic_of_squarefree_card_of_isMulCommutative
    (hG : Squarefree (Nat.card G))
    (hcommutative : IsMulCommutative G) :
    IsCyclic G := by
  letI : CommGroup G :=
    { (inferInstance : Group G) with
      mul_comm := isMulCommutative_iff.mp hcommutative }
  letI : IsZGroup G :=
    IsZGroup.of_squarefree hG
  letI : Group.IsNilpotent G :=
    inferInstance
  infer_instance

/-- In the commutative squarefree-order case, the cyclic splitting theorem
does give the full vanishing statement. -/
theorem isMulCoboundary₂_of_squarefree_card_of_isMulCommutative
    (alpha : FactorSet G ℂˣ)
    (halpha : alpha.IsNormalized)
    (hG : Squarefree (Nat.card G))
    (hcommutative : IsMulCommutative G) :
    letI := trivialMulDistribMulAction G ℂˣ
    groupCohomology.IsMulCoboundary₂
      (fun x : G × G ↦ alpha x.1 x.2) := by
  letI : IsCyclic G :=
    isCyclic_of_squarefree_card_of_isMulCommutative
      hG hcommutative
  exact alpha.isMulCoboundary₂_of_isCyclic halpha

/-- The precise structural conclusion currently available for a complex
factor set on a squarefree-order group: after writing the group as a
coprime cyclic-by-cyclic semidirect product, both cyclic restrictions split.
-/
def HasCyclicCoprimeCoboundaryRestrictions
    (alpha : FactorSet G ℂˣ) : Prop :=
  ∃ (N H : Subgroup G) (phi : H →* MulAut N)
      (_e : G ≃* N ⋊[phi] H),
    IsCyclic H ∧
      IsCyclic N ∧
      Nat.Coprime (Nat.card N) (Nat.card H) ∧
      (letI := trivialMulDistribMulAction N ℂˣ
       groupCohomology.IsMulCoboundary₂
         (fun x : N × N ↦
           (alpha.comap N.subtype) x.1 x.2)) ∧
      (letI := trivialMulDistribMulAction H ℂˣ
       groupCohomology.IsMulCoboundary₂
         (fun x : H × H ↦
           (alpha.comap H.subtype) x.1 x.2))

/-- On each cyclic factor in the standard squarefree-order decomposition,
the restriction of a normalized complex factor set is a coboundary. -/
theorem exists_cyclic_coprime_decomposition_with_coboundary_restrictions
    (alpha : FactorSet G ℂˣ)
    (halpha : alpha.IsNormalized)
    (hG : Squarefree (Nat.card G)) :
    ∃ (N H : Subgroup G) (phi : H →* MulAut N)
        (_e : G ≃* N ⋊[phi] H),
      IsCyclic H ∧
        IsCyclic N ∧
        Nat.Coprime (Nat.card N) (Nat.card H) ∧
        (letI := trivialMulDistribMulAction N ℂˣ
         groupCohomology.IsMulCoboundary₂
           (fun x : N × N ↦
             (alpha.comap N.subtype) x.1 x.2)) ∧
        (letI := trivialMulDistribMulAction H ℂˣ
         groupCohomology.IsMulCoboundary₂
           (fun x : H × H ↦
             (alpha.comap H.subtype) x.1 x.2)) := by
  obtain ⟨N, H, phi, e, hH, hN, hcoprime⟩ :=
    exists_cyclic_coprime_semidirect_decomposition hG
  letI : IsCyclic H := hH
  letI : IsCyclic N := hN
  have hnormalN :
      (alpha.comap N.subtype).IsNormalized :=
    alpha.comap_isNormalized N.subtype halpha
  have hnormalH :
      (alpha.comap H.subtype).IsNormalized :=
    alpha.comap_isNormalized H.subtype halpha
  exact
    ⟨N, H, phi, e, hH, hN, hcoprime,
      (alpha.comap N.subtype).isMulCoboundary₂_of_isCyclic
        hnormalN,
      (alpha.comap H.subtype).isMulCoboundary₂_of_isCyclic
        hnormalH⟩

/-- Packaged form of
`exists_cyclic_coprime_decomposition_with_coboundary_restrictions`. -/
theorem hasCyclicCoprimeCoboundaryRestrictions_of_squarefree_card
    (alpha : FactorSet G ℂˣ)
    (halpha : alpha.IsNormalized)
    (hG : Squarefree (Nat.card G)) :
    alpha.HasCyclicCoprimeCoboundaryRestrictions :=
  alpha.exists_cyclic_coprime_decomposition_with_coboundary_restrictions
    halpha hG

end SquarefreeStructure

section SquarefreeH2

variable {G₀ : Type} [Group G₀] [Finite G₀]

/-- In the commutative squarefree-order case, the represented second
cohomology class vanishes. -/
theorem h2Class_eq_zero_of_squarefree_card_of_isMulCommutative
    (alpha : FactorSet G₀ ℂˣ)
    (halpha : alpha.IsNormalized)
    (hG : Squarefree (Nat.card G₀))
    (hcommutative : IsMulCommutative G₀) :
    letI := trivialMulDistribMulAction G₀ ℂˣ
    alpha.h2Class = 0 := by
  letI : IsCyclic G₀ :=
    isCyclic_of_squarefree_card_of_isMulCommutative
      hG hcommutative
  exact alpha.h2Class_eq_zero_of_isCyclic halpha

end SquarefreeH2

end FactorSet
end CharacterTriple
end McKayConjecture
