/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorCentralIndexSharpened
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45FactorExtensionNormalizer
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45OuterQuotients
import McKayConjecture.InductiveMcKay.NormalSubgroupFactorNormalizerFibre
import McKayConjecture.Proof.CoprimeOrder

/-!
# Quotient-factor normalizer induction in Proposition 4.5

For a concrete Proposition-4.5 inertia pair, this file applies central-index
induction to the finite factor extension of the *outer quotient* of the left
inertia triple.

The naive estimate by the order of the outer quotient is not enough:
`CS` need not contain `Z(X)`.  The sharper associated-factor estimate proves
descent anyway.  If the inertia subgroup is proper, its central index is
already below that of `X`; if it is all of `X`, the noncentral normal copy
of `CS` gives strict descent inside the inertia group.

Both outer quotients are `q'`-groups.  Thus their chosen Sylow subgroups are
trivial, and the concrete right outer quotient is exactly the normalizer of
the chosen Sylow subgroup on the left.  The generic factor-extension
normalizer theorem then identifies the right pulled-back quotient-factor
extension with the normalizer of the Sylow lift.  Central-index induction
therefore constructs the full inverse-coefficient character on that right
quotient-factor extension.

What it does not prove is that this quotient-factor character lifts across
the right normal character with the required centralizer trace identity.
Those two genuinely representation-theoretic conclusions are named
separately at the end of the file.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation
open CharacterTriple.FactorSet
open ComplementReduction
open GroupTheory
open NormalSubgroupAssociatedFactorFibre
open NormalSubgroupFactorNormalizerFibre

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-! ## Strict central-index descent -/

/-- The canonical finite factor extension of the left inertia *quotient*. -/
abbrev ProductAmbientGlaubermanLeftQuotientFactorExtensionGroup
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  ExtensionGroup
    (productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta)

omit [Fact q.Prime] in
/-- Every ambient-central element belongs to the left inertia subgroup. -/
theorem center_le_productAmbientGlaubermanLeftInertia
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    Subgroup.center X ≤
      IrreducibleCharacter.inertia
        (product S C) theta.1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  intro z hz
  exact
    IrreducibleCharacter.mem_inertia_of_mem_center
      (product S C) theta.1 z hz

omit [Fact q.Prime] in
/-- If the left inertia subgroup is all of `X`, noncentrality of `C`
becomes noncentrality of the canonical normal copy of `CS` in the inertia
triple. -/
theorem productAmbientGlaubermanLeftNormalCopy_not_le_center_of_inertia_eq_top
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (hCnoncentral :
      ¬C ≤ Subgroup.center X) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    (hInertia :
      IrreducibleCharacter.inertia
          (product S C) theta.1 =
        ⊤) →
    ¬(productAmbientGlaubermanLeftInertiaTriple
        S C hgenerate theta).normalSubgroup ≤
      Subgroup.center
        (ProductAmbientGlaubermanLeftInertiaGroup
          S C hgenerate theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  intro hInertia
  intro hnormal
  apply hCnoncentral
  intro c hc
  have hcProduct :
      c ∈ product S C :=
    (show C ≤ product S C from le_sup_left) hc
  have hcInertia :
      c ∈ IrreducibleCharacter.inertia
        (product S C) theta.1 :=
    IrreducibleCharacter.subgroup_le_inertia
      (product S C) theta.1 hcProduct
  let cInertia :
      IrreducibleCharacter.inertia
        (product S C) theta.1 :=
    ⟨c, hcInertia⟩
  have hcCopy :
      cInertia ∈
        CliffordEquivalence.inertiaNormalCopy
          (product S C) theta.1 :=
    hcProduct
  have hcCenter := hnormal hcCopy
  rw [Subgroup.mem_center_iff] at hcCenter ⊢
  intro x
  have hxInertia :
      x ∈ IrreducibleCharacter.inertia
        (product S C) theta.1 := by
    rw [hInertia]
    exact trivial
  exact
    congrArg Subtype.val
      (hcCenter
        (⟨x, hxInertia⟩ :
          IrreducibleCharacter.inertia
            (product S C) theta.1))

/-- The canonical quotient-factor extension of every concrete left inertia
triple has central index strictly below the ambient group `X`. -/
theorem productAmbientGlaubermanLeftQuotientFactorExtension_centralIndex_lt
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (hCnoncentral :
      ¬C ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    centralIndex
        (ProductAmbientGlaubermanLeftQuotientFactorExtensionGroup
          S C hgenerate theta) <
      centralIndex X := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let T :=
    productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta
  let R := AssociatedGeneralExistence.associated T
  let F := R.finiteFactorNormalization
  let I :=
    IrreducibleCharacter.inertia
      (product S C) theta.1
  by_cases hInertia : I = ⊤
  · let e : I ≃* X :=
      MulEquiv.ofBijective I.subtype
        ⟨I.subtype_injective, by
          intro x
          exact
            ⟨⟨x, by rw [hInertia]; exact trivial⟩,
              rfl⟩⟩
    calc
      centralIndex
          (ProductAmbientGlaubermanLeftQuotientFactorExtensionGroup
            S C hgenerate theta) <
          centralIndex I :=
        F.finiteFactorCentralExtension_centralIndex_lt R
          (productAmbientGlaubermanLeftNormalCopy_not_le_center_of_inertia_eq_top
            S C hgenerate theta hCnoncentral hInertia)
      _ = centralIndex X :=
        centralIndex_congr e
  · calc
      centralIndex
          (ProductAmbientGlaubermanLeftQuotientFactorExtensionGroup
            S C hgenerate theta) ≤
          centralIndex I :=
        F.finiteFactorCentralExtension_centralIndex_le R
      _ < centralIndex X :=
        centralIndex_lt_of_center_le_of_lt_top
          I
          (center_le_productAmbientGlaubermanLeftInertia
            S C hgenerate theta)
          (lt_top_iff_ne_top.mpr hInertia)

/-! ## The concrete right outer quotient as a Sylow normalizer -/

/-- A fixed Sylow subgroup of the left inertia outer quotient.  The
`q'`-group theorem below shows that it is necessarily trivial. -/
abbrev productAmbientGlaubermanLeftOuterQuotientSylow
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    Sylow q
      (productAmbientGlaubermanLeftOuterQuotient
        S C hgenerate theta) :=
  default

/-- The chosen Sylow subgroup of the left outer quotient is trivial. -/
theorem productAmbientGlaubermanLeftOuterQuotientSylow_eq_bot
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    (productAmbientGlaubermanLeftOuterQuotientSylow
        S C hgenerate theta :
      Subgroup
        (productAmbientGlaubermanLeftOuterQuotient
          S C hgenerate theta)) =
      ⊥ := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  apply McKayConjecture.Sylow.eq_bot_of_not_dvd_card
  exact
    (GroupTheory.isPPrimeGroup_iff_not_dvd Fact.out).mp
      (productAmbientGlaubermanLeftOuterQuotient_isPPrimeGroup
        S C hgenerate theta)

/-- Consequently the normalizer of the chosen left-quotient Sylow subgroup
is the whole left outer quotient. -/
theorem productAmbientGlaubermanLeftOuterQuotientSylow_normalizer_eq_top
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    Subgroup.normalizer
        (productAmbientGlaubermanLeftOuterQuotientSylow
          S C hgenerate theta :
          Set
            (productAmbientGlaubermanLeftOuterQuotient
              S C hgenerate theta)) =
      ⊤ := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let Q :=
    productAmbientGlaubermanLeftOuterQuotientSylow
      S C hgenerate theta
  have hQ :
      (Q :
        Subgroup
          (productAmbientGlaubermanLeftOuterQuotient
            S C hgenerate theta)) =
        ⊥ :=
    productAmbientGlaubermanLeftOuterQuotientSylow_eq_bot
      S C hgenerate theta
  haveI :
      (Q :
        Subgroup
          (productAmbientGlaubermanLeftOuterQuotient
            S C hgenerate theta)).Normal := by
    rw [hQ]
    infer_instance
  exact Subgroup.normalizer_eq_top_iff.mpr inferInstance

/-- The concrete right outer quotient is exactly the normalizer of the
chosen Sylow subgroup in the left outer quotient.  Its underlying value is
the already-constructed matched-inertia quotient equivalence. -/
def productAmbientGlaubermanRightOuterEquivLeftOuterSylowNormalizer
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanRightOuterQuotient
          S C hcentral hgenerate g theta ≃*
      Subgroup.normalizer
        (productAmbientGlaubermanLeftOuterQuotientSylow
          S C hgenerate theta :
          Set
            (productAmbientGlaubermanLeftOuterQuotient
              S C hgenerate theta)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let e :=
    productAmbientGlaubermanOuterQuotientEquiv
      S C hcentral hgenerate g theta
  let hnormalizer :=
    productAmbientGlaubermanLeftOuterQuotientSylow_normalizer_eq_top
      S C hgenerate theta
  exact
    e.trans
      (((MulEquiv.subgroupCongr hnormalizer).trans
        Subgroup.topEquiv).symm)

@[simp]
theorem productAmbientGlaubermanRightOuterEquivLeftOuterSylowNormalizer_apply_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ∀ b :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta,
    ((productAmbientGlaubermanRightOuterEquivLeftOuterSylowNormalizer
        S C hcentral hgenerate g theta b :
      Subgroup.normalizer
        (productAmbientGlaubermanLeftOuterQuotientSylow
          S C hgenerate theta :
          Set
            (productAmbientGlaubermanLeftOuterQuotient
              S C hgenerate theta))) :
      productAmbientGlaubermanLeftOuterQuotient
        S C hgenerate theta) =
      productAmbientGlaubermanOuterQuotientEquiv
        S C hcentral hgenerate g theta b := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  intro b
  rfl

/-! ## Exact quotient-factor extension identification -/

/-- The canonical left quotient factor pulled back to the concrete right
outer quotient through its exact Sylow-normalizer identification. -/
abbrev ProductAmbientGlaubermanRightQuotientFactorSet
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let T :=
    productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta
  CentralExtensionGroup.sylowNormalizerFactorSet
    (CanonicalFactorSet T)
    (productAmbientGlaubermanLeftOuterQuotientSylow
      S C hgenerate theta)
    (productAmbientGlaubermanRightOuterEquivLeftOuterSylowNormalizer
      S C hcentral hgenerate g theta)

/-- The preceding Sylow-normalizer pullback is literally pullback along the
concrete matched-inertia outer-quotient equivalence. -/
theorem productAmbientGlaubermanRightQuotientFactorSet_eq_comap
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ProductAmbientGlaubermanRightQuotientFactorSet
        S C hcentral hgenerate g theta =
      (CanonicalFactorSet
        (productAmbientGlaubermanLeftInertiaTriple
          S C hgenerate theta)).comap
        (productAmbientGlaubermanOuterQuotientEquiv
          S C hcentral hgenerate g theta).toMonoidHom := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  apply FactorSet.ext
  intro b c
  rfl

/-- The concrete right quotient factor is normalized. -/
abbrev ProductAmbientGlaubermanRightQuotientFactorSetIsNormalized
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    (ProductAmbientGlaubermanRightQuotientFactorSet
      S C hcentral hgenerate g theta).IsNormalized :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let T :=
    productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta
  CentralExtensionGroup.sylowNormalizerFactorSet_isNormalized
    (CanonicalFactorSet T)
    (CanonicalFactorSetIsNormalized T)
    (productAmbientGlaubermanLeftOuterQuotientSylow
      S C hgenerate theta)
    (productAmbientGlaubermanRightOuterEquivLeftOuterSylowNormalizer
      S C hcentral hgenerate g theta)

/-- The concrete finite quotient-factor extension on the right outer
quotient. -/
abbrev ProductAmbientGlaubermanRightQuotientFactorExtensionGroup
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  CentralExtensionGroup
      (ProductAmbientGlaubermanRightQuotientFactorSet
        S C hcentral hgenerate g theta)
      (ProductAmbientGlaubermanRightQuotientFactorSetIsNormalized
        S C hcentral hgenerate g theta)

/-- The exact normalizer in the left quotient-factor extension to which
central-index induction applies. -/
abbrev ProductAmbientGlaubermanLeftQuotientFactorSylowLiftNormalizer
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let T :=
    productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta
  SylowNormalizer
    (LiftedSylow T
      (productAmbientGlaubermanLeftOuterQuotientSylow
        S C hgenerate theta))

/-! ## The character furnished by central-index induction -/

/-- The normal character in the concrete left quotient triple has
prime-to-`q` degree. -/
theorem productAmbientGlaubermanLeftInertiaTriple_character_isPPrimeDegree
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    (productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta).character.IsPPrimeDegree q := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  change
    ¬q ∣
      (CliffordEquivalence.inertiaCopyCharacter
        (product S C) theta.1).degree
  simpa only [CliffordEquivalence.inertiaCopyCharacter,
    IrreducibleCharacter.comap_degree,
    IrreducibleCharacter.IsPPrimeDegree] using theta.2

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
