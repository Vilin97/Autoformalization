/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InertiaCharacteristicCopy
import McKayConjecture.InductiveMcKay.InvariantCharacterInertiaNormalProduct
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizerSourceTransport
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45FactorExtensionNormalizer

/-!
# The canonical kernel inside the source-character inertia group

Fix a prime-to-`q` character `theta` of `CS`.  The ambient group relevant
to its ordinary inertia-fibre count is

`Γ_theta = I_X(theta)`,

not the generally larger inertia group of the canonical `q'`-kernel
constituent below `theta`.

This file copies the characteristic `q'`-kernel of `CS` into `Γ_theta`.
Together with the restricted Sylow subgroup it recovers the normal copy
of `CS`.  Frattini's argument then gives the exact product hypothesis
needed when the abstract Okuyama--Wajima count is specialized to this
character inertia group.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CliffordEquivalence
open CliffordCorrespondence
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The characteristic `q'`-kernel of `CS`, copied into the inertia group
of the chosen character of `CS`. -/
abbrev productAmbientGlaubermanLeftInertiaPPrimeKernel
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    Subgroup
      (ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  inertiaSubgroupCopy
    (product S C) theta.1
    (productPPrimeKernel S C hcentral)

/-- Copying the internal Sylow subgroup of `CS` into the character inertia
group gives the already named restricted ambient Sylow subgroup. -/
theorem productAmbientGlaubermanLeftInertia_productSylowCopy_eq
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    inertiaSubgroupCopy
        (product S C) theta.1
        (productSylow S C : Subgroup (product S C)) =
      (productAmbientGlaubermanLeftInertiaSylow
        S C hgenerate theta :
        Subgroup
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let D := product S C
  let P : Subgroup D :=
    (productSylow S C : Subgroup D)
  let T := IrreducibleCharacter.inertia D theta.1
  let Pcopy : Subgroup T :=
    inertiaSubgroupCopy D theta.1 P
  let e : P ≃* Pcopy :=
    inertiaSubgroupCopyEquiv D theta.1 P
  apply le_antisymm
  · intro x hx
    let xcopy : Pcopy := ⟨x, hx⟩
    let y : P := e.symm xcopy
    have heq : e y = xcopy :=
      e.apply_symm_apply xcopy
    have hcoe :
        inertiaInclusion D theta.1 y = x := by
      rw [← inertiaSubgroupCopyEquiv_apply_coe
        D theta.1 P y]
      exact congrArg Subtype.val heq
    change ((x : T) : X) ∈ S
    rw [← hcoe]
    exact y.property
  · intro x hx
    let yD : D :=
      ⟨((x : T) : X),
        (show (S : Subgroup X) ≤ D from le_sup_right) hx⟩
    let y : P :=
      ⟨yD, hx⟩
    have heq : (e y : T) = x := by
      apply Subtype.ext
      rfl
    rw [← heq]
    exact (e y).property

/-- The copied `q'`-kernel together with the restricted Sylow subgroup is
exactly the canonical normal copy of `CS` inside `I_X(theta)`. -/
theorem
    productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_eq_normalCopy
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    productAmbientGlaubermanLeftInertiaPPrimeKernel
          S C hcentral hgenerate theta ⊔
        (productAmbientGlaubermanLeftInertiaSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) =
      inertiaNormalCopy (product S C) theta.1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  rw [←
    productAmbientGlaubermanLeftInertia_productSylowCopy_eq
      S C hgenerate theta]
  exact
    inertiaSubgroupCopy_sup_eq_normalCopy
      (product S C) theta.1
      (K := productPPrimeKernel S C hcentral)
      (L := (productSylow S C :
        Subgroup (product S C)))
      (productPPrimeKernel_sup_productSylow_eq_top
        S C hcentral)

/-- The copied canonical kernel still has order prime to `q`. -/
theorem productAmbientGlaubermanLeftInertiaPPrimeKernel_isPPrimeGroup
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IsPPrimeGroup q
      (productAmbientGlaubermanLeftInertiaPPrimeKernel
        S C hcentral hgenerate theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    inertiaSubgroupCopy_isPPrimeGroup
      (product S C) theta.1
      (productPPrimeKernel S C hcentral)
      (productPPrimeKernel_isPPrimeGroup
        S C hcentral)

/-- The copied kernel--Sylow normal product is normal in the exact source
character inertia group. -/
theorem
    productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_normal
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    (productAmbientGlaubermanLeftInertiaPPrimeKernel
          S C hcentral hgenerate theta ⊔
        (productAmbientGlaubermanLeftInertiaSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta))).Normal := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  rw [
    productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_eq_normalCopy
      S C hcentral hgenerate theta]
  infer_instance

/-- Frattini generation in the exact source-character inertia group:
the characteristic `q'`-kernel and the normalizer of the restricted Sylow
subgroup generate `I_X(theta)`. -/
theorem
    productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_normalizer_eq_top
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    productAmbientGlaubermanLeftInertiaPPrimeKernel
          S C hcentral hgenerate theta ⊔
        Subgroup.normalizer
          ((productAmbientGlaubermanLeftInertiaSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) :
            Set
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) =
      ⊤ := by
  let D := product S C
  letI : D.Normal :=
    product_normal S C hgenerate
  let thetaInvariant :
      PInvariantPPrimeIrreducibleCharacter
        D (S : Subgroup X) q :=
    ⟨theta,
      sylow_le_productAmbientLeftInertia
        S C hgenerate theta⟩
  have hDS : D ⊔ (S : Subgroup X) = D :=
    sup_eq_left.mpr le_sup_right
  have hDSNormal :
      (D ⊔ (S : Subgroup X)).Normal := by
    rw [hDS]
    infer_instance
  have hfrattini :=
    invariantCharacterInertia_sup_normalizer_eq_top
      D S thetaInvariant hDSNormal
  change
    productAmbientGlaubermanLeftInertiaPPrimeKernel
          S C hcentral hgenerate theta ⊔
        Subgroup.normalizer
          ((productAmbientGlaubermanLeftInertiaSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) :
            Set
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) =
      ⊤
  have hnormalCopy :
      inertiaNormalCopy D theta.1 =
        productAmbientGlaubermanLeftInertiaPPrimeKernel
              S C hcentral hgenerate theta ⊔
            (productAmbientGlaubermanLeftInertiaSylow
              S C hgenerate theta :
              Subgroup
                (ProductAmbientGlaubermanLeftInertiaGroup
                  S C hgenerate theta)) :=
    (productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_eq_normalCopy
      S C hcentral hgenerate theta).symm
  rw [hnormalCopy] at hfrattini
  apply top_unique
  rw [← hfrattini]
  exact
    sup_le
      (sup_le le_sup_left
        (Subgroup.le_normalizer.trans le_sup_right))
      le_sup_right

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
