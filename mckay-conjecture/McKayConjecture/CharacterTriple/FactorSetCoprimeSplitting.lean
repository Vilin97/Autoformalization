/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SchurZassenhaus
import McKayConjecture.CharacterTriple.FactorSetCentralExtension

/-!
# Splitting factor sets with coprime coefficient and base orders

Schur--Zassenhaus splits the central extension associated to a normalized
factor set whenever the finite coefficient group and base group have coprime
orders.  Reading the coefficient coordinate of a complementary section gives
an explicit normalized cochain whose gauge makes the factor set trivial.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

universe u v

variable {G : Type u} {A : Type v}
variable [Group G] [CommGroup A] [Finite G] [Finite A]

namespace CentralExtensionGroup

variable (alpha : FactorSet G A) (halpha : alpha.IsNormalized)

abbrev coefficientKernel :
    Subgroup (CentralExtensionGroup alpha halpha) :=
  (projection alpha halpha).ker

theorem coefficientKernel_card :
    Nat.card (coefficientKernel alpha halpha) =
      Nat.card A := by
  rw [show
    coefficientKernel alpha halpha =
      (coefficientEmbedding alpha halpha).range from
    projection_ker_eq_coefficientEmbedding_range alpha halpha]
  exact
    Nat.card_congr
      ((MonoidHom.ofInjective
        (coefficientEmbedding_injective alpha halpha)).symm)

theorem coefficientKernel_index :
    (coefficientKernel alpha halpha).index =
      Nat.card G := by
  rw [Subgroup.index_ker]
  exact
    Nat.card_congr
      ((MulEquiv.subgroupCongr
        ((projection alpha halpha).range_eq_top.mpr
          (projection_surjective alpha halpha))).trans
        Subgroup.topEquiv)

theorem exists_coefficientKernel_complement
    (hcoprime :
      Nat.Coprime (Nat.card A) (Nat.card G)) :
    ∃ H :
        Subgroup (CentralExtensionGroup alpha halpha),
      (coefficientKernel alpha halpha).IsComplement' H := by
  apply Subgroup.exists_right_complement'_of_coprime
  rw [coefficientKernel_card, coefficientKernel_index]
  exact hcoprime

def complementProjection
    (H : Subgroup (CentralExtensionGroup alpha halpha)) :
    H →* G :=
  (projection alpha halpha).comp H.subtype

theorem complementProjection_injective
    (H : Subgroup (CentralExtensionGroup alpha halpha))
    (hH :
      (coefficientKernel alpha halpha).IsComplement' H) :
    Function.Injective
      (complementProjection alpha halpha H) := by
  intro x y hxy
  change
    projection alpha halpha
        (x : CentralExtensionGroup alpha halpha) =
      projection alpha halpha
        (y : CentralExtensionGroup alpha halpha) at hxy
  have hker :
      ((x : CentralExtensionGroup alpha halpha) *
          (y : CentralExtensionGroup alpha halpha)⁻¹) ∈
        coefficientKernel alpha halpha := by
    change
      projection alpha halpha
          ((x : CentralExtensionGroup alpha halpha) *
            (y : CentralExtensionGroup alpha halpha)⁻¹) =
        1
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hcomp :
      ((x : CentralExtensionGroup alpha halpha) *
          (y : CentralExtensionGroup alpha halpha)⁻¹) ∈ H :=
    H.mul_mem x.property (H.inv_mem y.property)
  have hone :
      (x : CentralExtensionGroup alpha halpha) *
          (y : CentralExtensionGroup alpha halpha)⁻¹ =
        1 :=
    Subgroup.disjoint_def.mp hH.disjoint
      hker hcomp
  apply Subtype.ext
  exact (mul_inv_eq_one.mp hone)

theorem complementProjection_surjective
    (H : Subgroup (CentralExtensionGroup alpha halpha))
    (hH :
      (coefficientKernel alpha halpha).IsComplement' H) :
    Function.Surjective
      (complementProjection alpha halpha H) := by
  intro g
  obtain ⟨x, hx⟩ :=
    projection_surjective alpha halpha g
  obtain ⟨⟨n, h⟩, hnh⟩ := hH.2 x
  refine ⟨h, ?_⟩
  change projection alpha halpha (h : CentralExtensionGroup alpha halpha) = g
  have hn :
      projection alpha halpha
          (n : CentralExtensionGroup alpha halpha) = 1 :=
    n.property
  have hproj :=
    congrArg (projection alpha halpha) hnh
  change
    projection alpha halpha
        ((n : CentralExtensionGroup alpha halpha) *
          (h : CentralExtensionGroup alpha halpha)) =
      projection alpha halpha x at hproj
  rw [map_mul, hn, one_mul] at hproj
  exact hproj.trans hx

def complementProjectionEquiv
    (H : Subgroup (CentralExtensionGroup alpha halpha))
    (hH :
      (coefficientKernel alpha halpha).IsComplement' H) :
    H ≃* G :=
  MulEquiv.ofBijective
    (complementProjection alpha halpha H)
    ⟨complementProjection_injective alpha halpha H hH,
      complementProjection_surjective alpha halpha H hH⟩

def complementSection
    (H : Subgroup (CentralExtensionGroup alpha halpha))
    (hH :
      (coefficientKernel alpha halpha).IsComplement' H) :
    G →*
      CentralExtensionGroup alpha halpha :=
  H.subtype.comp
    (complementProjectionEquiv alpha halpha H hH).symm.toMonoidHom

@[simp]
theorem projection_complementSection
    (H : Subgroup (CentralExtensionGroup alpha halpha))
    (hH :
      (coefficientKernel alpha halpha).IsComplement' H)
    (g : G) :
    projection alpha halpha
        (complementSection alpha halpha H hH g) =
      g :=
  (complementProjectionEquiv alpha halpha H hH).apply_symm_apply g

def complementCochain
    (H : Subgroup (CentralExtensionGroup alpha halpha))
    (hH :
      (coefficientKernel alpha halpha).IsComplement' H)
    (g : G) : A :=
  coefficient alpha halpha
    (complementSection alpha halpha H hH g)

@[simp]
theorem complementCochain_one
    (H : Subgroup (CentralExtensionGroup alpha halpha))
    (hH :
      (coefficientKernel alpha halpha).IsComplement' H) :
    complementCochain alpha halpha H hH 1 = 1 := by
  simp [complementCochain]

theorem factor_mul_complementCochain
    (H : Subgroup (CentralExtensionGroup alpha halpha))
    (hH :
      (coefficientKernel alpha halpha).IsComplement' H)
    (g k : G) :
    alpha g k *
        complementCochain alpha halpha H hH g *
        complementCochain alpha halpha H hH k =
      complementCochain alpha halpha H hH (g * k) := by
  change
    alpha g k *
        coefficient alpha halpha
          (complementSection alpha halpha H hH g) *
        coefficient alpha halpha
          (complementSection alpha halpha H hH k) =
      coefficient alpha halpha
        (complementSection alpha halpha H hH (g * k))
  have hs :
      complementSection alpha halpha H hH g *
          complementSection alpha halpha H hH k =
        complementSection alpha halpha H hH (g * k) := by
    exact (map_mul (complementSection alpha halpha H hH) g k).symm
  have hc := congrArg (coefficient alpha halpha) hs
  simp only [coefficient_mul] at hc
  rw [show
      base alpha halpha
          (complementSection alpha halpha H hH g) = g from
        projection_complementSection alpha halpha H hH g,
    show
      base alpha halpha
          (complementSection alpha halpha H hH k) = k from
        projection_complementSection alpha halpha H hH k] at hc
  exact hc

theorem gauge_complementCochain_eq_one
    (H : Subgroup (CentralExtensionGroup alpha halpha))
    (hH :
      (coefficientKernel alpha halpha).IsComplement' H) :
    alpha.gauge
        (complementCochain alpha halpha H hH) =
      FactorSet.one := by
  ext g k
  rw [gauge_apply, one_apply]
  rw [div_eq_mul_inv]
  have h := factor_mul_complementCochain
    alpha halpha H hH g k
  calc
    complementCochain alpha halpha H hH g *
          complementCochain alpha halpha H hH k *
          (complementCochain alpha halpha H hH (g * k))⁻¹ *
          alpha g k =
        (alpha g k *
          complementCochain alpha halpha H hH g *
          complementCochain alpha halpha H hH k) *
          (complementCochain alpha halpha H hH (g * k))⁻¹ := by
            ac_rfl
    _ = 1 := by rw [h, mul_inv_cancel]

end CentralExtensionGroup

theorem exists_gauge_eq_one_of_coprime
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (hcoprime :
      Nat.Coprime (Nat.card A) (Nat.card G)) :
    ∃ c : G → A,
      alpha.gauge c = FactorSet.one := by
  obtain ⟨H, hH⟩ :=
    CentralExtensionGroup.exists_coefficientKernel_complement
      alpha halpha hcoprime
  exact
    ⟨CentralExtensionGroup.complementCochain
        alpha halpha H hH,
      CentralExtensionGroup.gauge_complementCochain_eq_one
        alpha halpha H hH⟩

/-- Under the same coprimality hypothesis, the trivializing cochain may be
chosen to take the value one at the identity. -/
theorem exists_normalized_gauge_eq_one_of_coprime
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (hcoprime :
      Nat.Coprime (Nat.card A) (Nat.card G)) :
    ∃ c : G → A,
      c 1 = 1 ∧
        alpha.gauge c = FactorSet.one := by
  obtain ⟨H, hH⟩ :=
    CentralExtensionGroup.exists_coefficientKernel_complement
      alpha halpha hcoprime
  exact
    ⟨CentralExtensionGroup.complementCochain
        alpha halpha H hH,
      CentralExtensionGroup.complementCochain_one
        alpha halpha H hH,
      CentralExtensionGroup.gauge_complementCochain_eq_one
        alpha halpha H hH⟩

end FactorSet
end CharacterTriple
end McKayConjecture
