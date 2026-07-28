/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralExtensionSylowNormalizer

/-!
# Normalizer actions across a central extension

Suppose a central extension identifies a lifted Sylow subgroup with the
target Sylow subgroup.  Projection then intertwines the two conjugation
actions of their normalizers.  Since the normalizer projection is
surjective, the two induced subgroups of the corresponding automorphism
groups are canonically isomorphic.

This is the action-level refinement of the normalizer-order comparison in
`CentralExtensionSylowNormalizer`.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory
namespace CentralExtension

variable {U : Type u} {Q : Type v}
variable [Group U] [Group Q] [Finite U]
variable {p : ℕ} [Fact p.Prime]

/-- Projection restricted from the unique Sylow lift to the target Sylow
subgroup. -/
def sylowLiftProjection
    (E : CentralExtension U Q) (S : Sylow p Q) :
    E.sylowLift S →* S where
  toFun x :=
    ⟨E.projection (x : U), by
      rw [← E.sylowLift_map S]
      exact
        ⟨(x : U), x.property, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact E.projection.map_one
  map_mul' x y := by
    apply Subtype.ext
    exact E.projection.map_mul x y

@[simp]
theorem sylowLiftProjection_apply_coe
    (E : CentralExtension U Q) (S : Sylow p Q)
    (x : E.sylowLift S) :
    ((E.sylowLiftProjection S x : S) : Q) =
      E.projection (x : U) :=
  rfl

/-- The restricted projection onto the target Sylow subgroup is
surjective. -/
theorem sylowLiftProjection_surjective
    (E : CentralExtension U Q) (S : Sylow p Q) :
    Function.Surjective (E.sylowLiftProjection S) := by
  intro y
  have hy :
      (y : Q) ∈
        (E.sylowLift S : Subgroup U).map E.projection := by
    rw [E.sylowLift_map S]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxy

/-- If the Sylow projection is injective, it is a canonical isomorphism
between the lifted and target Sylow subgroups. -/
def sylowLiftEquivOfInjective
    (E : CentralExtension U Q) (S : Sylow p Q)
    (hinjective :
      Function.Injective (E.sylowLiftProjection S)) :
    E.sylowLift S ≃* S :=
  MulEquiv.ofBijective
    (E.sylowLiftProjection S)
    ⟨hinjective, E.sylowLiftProjection_surjective S⟩

@[simp]
theorem sylowLiftEquivOfInjective_apply_coe
    (E : CentralExtension U Q) (S : Sylow p Q)
    (hinjective :
      Function.Injective (E.sylowLiftProjection S))
    (x : E.sylowLift S) :
    ((E.sylowLiftEquivOfInjective S hinjective x : S) : Q) =
      E.projection (x : U) :=
  rfl

/-- Projection intertwines conjugation by the two Sylow normalizers. -/
theorem sylowLiftEquivOfInjective_normalizer_action
    (E : CentralExtension U Q) (S : Sylow p Q)
    (hinjective :
      Function.Injective (E.sylowLiftProjection S))
    (x :
      Subgroup.normalizer (E.sylowLift S : Set U))
    (y : E.sylowLift S) :
    E.sylowLiftEquivOfInjective S hinjective
        ((E.sylowLift S : Subgroup U).normalizerMonoidHom x y) =
      (S : Subgroup Q).normalizerMonoidHom
        (E.sylowNormalizerProjection S x)
        (E.sylowLiftEquivOfInjective S hinjective y) := by
  apply Subtype.ext
  change
    E.projection ((x : U) * (y : U) * (x : U)⁻¹) =
      E.projection (x : U) *
        E.projection (y : U) *
          (E.projection (x : U))⁻¹
  simp

/-- Projection restricted from the centralizer of the Sylow lift to the
centralizer of the target Sylow subgroup. -/
def sylowCentralizerProjection
    (E : CentralExtension U Q) (S : Sylow p Q)
    (hinjective :
      Function.Injective (E.sylowLiftProjection S)) :
    Subgroup.centralizer (E.sylowLift S : Set U) →*
      Subgroup.centralizer (S : Set Q) where
  toFun x :=
    ⟨E.projection (x : U), by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨z, hz⟩ :=
        (E.sylowLiftEquivOfInjective S hinjective).surjective
          ⟨y, hy⟩
      have hx :=
        x.property (z : U) z.property
      have hxMap :=
        congrArg E.projection hx
      have hzCoe :
          E.projection (z : U) = y :=
        congrArg Subtype.val hz
      rw [← hzCoe]
      simpa only [map_mul] using hxMap⟩
  map_one' := by
    apply Subtype.ext
    exact E.projection.map_one
  map_mul' x y := by
    apply Subtype.ext
    exact E.projection.map_mul x y

@[simp]
theorem sylowCentralizerProjection_apply_coe
    (E : CentralExtension U Q) (S : Sylow p Q)
    (hinjective :
      Function.Injective (E.sylowLiftProjection S))
    (x : Subgroup.centralizer (E.sylowLift S : Set U)) :
    ((E.sylowCentralizerProjection S hinjective x :
        Subgroup.centralizer (S : Set Q)) : Q) =
      E.projection (x : U) :=
  rfl

/-- The restricted projection between Sylow centralizers is surjective. -/
theorem sylowCentralizerProjection_surjective
    (E : CentralExtension U Q) (S : Sylow p Q)
    (hinjective :
      Function.Injective (E.sylowLiftProjection S)) :
    Function.Surjective
      (E.sylowCentralizerProjection S hinjective) := by
  intro y
  let yNormalizer :
      Subgroup.normalizer (S : Set Q) :=
    ⟨(y : Q),
      Subgroup.centralizer_le_normalizer
        (S : Set Q) y.property⟩
  obtain ⟨x, hx⟩ :=
    E.sylowNormalizerProjection_surjective S yNormalizer
  have hxCentralizer :
      (x : U) ∈
        Subgroup.centralizer
          (E.sylowLift S : Set U) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    let zLift : E.sylowLift S :=
      ⟨z, hz⟩
    have hyFix :
        (S : Subgroup Q).normalizerMonoidHom yNormalizer
            (E.sylowLiftEquivOfInjective S hinjective zLift) =
          E.sylowLiftEquivOfInjective S hinjective zLift := by
      apply Subtype.ext
      change
        (y : Q) *
              E.projection z *
                (y : Q)⁻¹ =
          E.projection z
      have hyCommute :
          E.projection z * (y : Q) =
            (y : Q) * E.projection z :=
        y.property
          (E.projection z)
          (E.sylowLiftEquivOfInjective S hinjective zLift).property
      rw [← hyCommute]
      simp [mul_assoc]
    have hxFix :
        (E.sylowLift S : Subgroup U).normalizerMonoidHom x zLift =
          zLift := by
      apply
        (E.sylowLiftEquivOfInjective S hinjective).injective
      rw [E.sylowLiftEquivOfInjective_normalizer_action
        S hinjective x zLift]
      have hxNormalizer :
          E.sylowNormalizerProjection S x =
            yNormalizer :=
        hx
      rw [hxNormalizer]
      exact hyFix
    have hxFixCoe :=
      congrArg Subtype.val hxFix
    change (x : U) * z * (x : U)⁻¹ = z at hxFixCoe
    calc
      z * (x : U) =
          ((x : U) * z * (x : U)⁻¹) * (x : U) := by
        rw [hxFixCoe]
      _ = (x : U) * z := by
        simp [mul_assoc]
  refine ⟨⟨(x : U), hxCentralizer⟩, ?_⟩
  apply Subtype.ext
  change E.projection (x : U) = (y : Q)
  exact
    congrArg
      (fun w : Subgroup.normalizer (S : Set Q) ↦ (w : Q))
      hx

/-- The kernel of the restricted centralizer projection is central. -/
theorem sylowCentralizerProjection_ker_le_center
    (E : CentralExtension U Q) (S : Sylow p Q)
    (hinjective :
      Function.Injective (E.sylowLiftProjection S)) :
    (E.sylowCentralizerProjection S hinjective).ker ≤
      Subgroup.center
        (Subgroup.centralizer
          (E.sylowLift S : Set U)) := by
  intro x hx
  have hxKer :
      (x : U) ∈ E.projection.ker := by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  have hxCenter :
      (x : U) ∈ Subgroup.center U :=
    E.ker_le_center hxKer
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact
    Subgroup.mem_center_iff.mp hxCenter (y : U)

/-- Corresponding Sylow centralizers form a central extension whenever
the Sylow projection is injective. -/
def sylowCentralizerCentralExtension
    (E : CentralExtension U Q) (S : Sylow p Q)
    (hinjective :
      Function.Injective (E.sylowLiftProjection S)) :
    CentralExtension
      (Subgroup.centralizer (E.sylowLift S : Set U))
      (Subgroup.centralizer (S : Set Q)) where
  projection :=
    E.sylowCentralizerProjection S hinjective
  surjective :=
    E.sylowCentralizerProjection_surjective S hinjective
  ker_le_center :=
    E.sylowCentralizerProjection_ker_le_center S hinjective

/-- Homomorphism form of the action-intertwining identity. -/
theorem congr_sylowLiftEquiv_comp_normalizerMonoidHom
    (E : CentralExtension U Q) (S : Sylow p Q)
    (hinjective :
      Function.Injective (E.sylowLiftProjection S)) :
    (MulAut.congr
        (E.sylowLiftEquivOfInjective S hinjective)).toMonoidHom.comp
        (E.sylowLift S : Subgroup U).normalizerMonoidHom =
      (S : Subgroup Q).normalizerMonoidHom.comp
        (E.sylowNormalizerProjection S) := by
  apply MonoidHom.ext
  intro x
  apply DFunLike.ext
  intro y
  obtain ⟨z, rfl⟩ :=
    (E.sylowLiftEquivOfInjective S hinjective).surjective y
  simpa [MulAut.congr] using
    E.sylowLiftEquivOfInjective_normalizer_action
      S hinjective x z

/-- The normalizer-action range upstairs maps exactly to the
normalizer-action range downstairs. -/
theorem map_normalizerMonoidHom_range
    (E : CentralExtension U Q) (S : Sylow p Q)
    (hinjective :
      Function.Injective (E.sylowLiftProjection S)) :
    ((E.sylowLift S : Subgroup U).normalizerMonoidHom.range).map
        (MulAut.congr
          (E.sylowLiftEquivOfInjective S hinjective)).toMonoidHom =
      (S : Subgroup Q).normalizerMonoidHom.range := by
  let c :=
    (MulAut.congr
      (E.sylowLiftEquivOfInjective S hinjective)).toMonoidHom
  let sourceAction :=
    (E.sylowLift S : Subgroup U).normalizerMonoidHom
  let targetAction :=
    (S : Subgroup Q).normalizerMonoidHom
  let projection :=
    E.sylowNormalizerProjection S
  calc
    sourceAction.range.map c =
        (c.comp sourceAction).range :=
      (MonoidHom.range_comp c sourceAction).symm
    _ = (targetAction.comp projection).range := by
      rw [E.congr_sylowLiftEquiv_comp_normalizerMonoidHom
        S hinjective]
    _ = projection.range.map targetAction :=
      MonoidHom.range_comp targetAction projection
    _ = targetAction.range := by
      rw [E.sylowNormalizerProjection_range S,
        ← MonoidHom.range_eq_map]

/-- The induced automorphism groups of the two Sylow subgroups are
canonically isomorphic. -/
def normalizerMonoidHomRangeEquiv
    (E : CentralExtension U Q) (S : Sylow p Q)
    (hinjective :
      Function.Injective (E.sylowLiftProjection S)) :
    (E.sylowLift S : Subgroup U).normalizerMonoidHom.range ≃*
      (S : Subgroup Q).normalizerMonoidHom.range :=
  ((MulAut.congr
      (E.sylowLiftEquivOfInjective S hinjective)).subgroupMap
        (E.sylowLift S : Subgroup U).normalizerMonoidHom.range).trans
    (MulEquiv.subgroupCongr
      (E.map_normalizerMonoidHom_range S hinjective))

/-- In particular, the two induced automorphism groups have the same
cardinality. -/
theorem natCard_normalizerMonoidHom_range_eq
    (E : CentralExtension U Q) (S : Sylow p Q)
    (hinjective :
      Function.Injective (E.sylowLiftProjection S)) :
    Nat.card
        (E.sylowLift S : Subgroup U).normalizerMonoidHom.range =
      Nat.card (S : Subgroup Q).normalizerMonoidHom.range :=
  Nat.card_congr
    (E.normalizerMonoidHomRangeEquiv S hinjective).toEquiv

end CentralExtension
end GroupTheory
end McKayConjecture
