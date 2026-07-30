/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GoodElementTorsor

/-!
# Extension ratios for good elements

Fix an extension `η` of an invariant character `θ` from `N` to `N⟨q⟩`.
Conjugating `η` by an element over `C_{A/N}(q)` gives another extension.
Gallagher's extension torsor supplies a unique quotient-linear character
carrying `η` to that conjugate.

These ratio characters multiply under the centralizer action.  Evaluation
on the canonical generator of the cyclic quotient therefore gives a linear
character of the good-element centralizer.  It is trivial precisely when
`η` is fixed, and hence precisely when `q` is `θ`-good.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace IrreducibleCharacter

variable {A : Type u} [Group A]
variable (N : Subgroup A) [N.Normal]

theorem goodElementConjugateInternalExtension
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q)
    (d : goodElementCentralizer N q) :
    IsExtensionAlong
      (cyclicOverNormalSubgroup N q).subtype
      (cyclicOverInternalCharacter N θ q)
      (goodElementAction N q d • η.1) :=
  (isExtensionAlong_cyclicOverInclusion_iff
    N θ q (goodElementAction N q d • η.1)).mp
      (goodElementAction_isExtensionAlong
        N θ hinvariant q η d)

def goodElementExtensionRatioCharacter
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q)
    (d : goodElementCentralizer N q) :
  (cyclicOverQuotientElement N q ⧸
      cyclicOverNormalSubgroup N q) →* ℂˣ :=
  (gallagherExtensionEquiv
    ((isExtensionAlong_cyclicOverInclusion_iff
      N θ q η.1).mp η.2)).symm
      ⟨goodElementAction N q d • η.1,
        goodElementConjugateInternalExtension
          N θ hinvariant q η d⟩

theorem goodElementExtensionRatioCharacter_spec
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q)
    (d : goodElementCentralizer N q) :
    goodElementAction N q d • η.1 =
      twist
        (inflateLinearCharacter
          (cyclicOverNormalSubgroup N q)
          (goodElementExtensionRatioCharacter
            N θ hinvariant q η d))
        η.1 :=
by
  let hη :=
    (isExtensionAlong_cyclicOverInclusion_iff
      N θ q η.1).mp η.2
  let ηd :
      Extensions (cyclicOverNormalSubgroup N q)
        (cyclicOverInternalCharacter N θ q) :=
    ⟨goodElementAction N q d • η.1,
      goodElementConjugateInternalExtension
        N θ hinvariant q η d⟩
  have h :=
    (gallagherExtensionEquiv hη).apply_symm_apply ηd
  simpa only [goodElementExtensionRatioCharacter,
    gallagherExtensionEquiv_apply] using
      (congrArg Subtype.val h).symm

theorem eq_goodElementExtensionRatioCharacter
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q)
    (d : goodElementCentralizer N q)
    (beta :
      (cyclicOverQuotientElement N q ⧸
        cyclicOverNormalSubgroup N q) →* ℂˣ)
    (hbeta :
      goodElementAction N q d • η.1 =
        twist
          (inflateLinearCharacter
            (cyclicOverNormalSubgroup N q) beta)
          η.1) :
    beta =
      goodElementExtensionRatioCharacter
        N θ hinvariant q η d :=
by
  let hη :=
    (isExtensionAlong_cyclicOverInclusion_iff
      N θ q η.1).mp η.2
  apply quotientTwistExtension_injective hη
  apply Subtype.ext
  exact hbeta.symm.trans
    (goodElementExtensionRatioCharacter_spec
      N θ hinvariant q η d)

theorem goodElementExtensionRatioCharacter_eq_one_iff
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q)
    (d : goodElementCentralizer N q) :
    goodElementExtensionRatioCharacter
        N θ hinvariant q η d = 1 ↔
      goodElementAction N q d • η.1 = η.1 := by
  constructor
  · intro hratio
    rw [goodElementExtensionRatioCharacter_spec
      N θ hinvariant q η d, hratio]
    simp [inflateLinearCharacter]
  · intro hfixed
    symm
    apply eq_goodElementExtensionRatioCharacter
      N θ hinvariant q η d 1
    rw [hfixed]
    simp [inflateLinearCharacter]

/-- The canonical chosen lift of `q` inside `N⟨q⟩`. -/
def cyclicOverQuotientGenerator (q : A ⧸ N) :
    cyclicOverQuotientElement N q :=
  ⟨Quotient.out q, by
    change
      QuotientGroup.mk' N (Quotient.out q) ∈
        Subgroup.zpowers q
    rw [show
      QuotientGroup.mk' N (Quotient.out q) = q by
        exact Quotient.out_eq' q]
    exact Subgroup.mem_zpowers q⟩

/-- The class of the canonical lift in the internal quotient
`N⟨q⟩ / N`. -/
def cyclicOverInternalQuotientGenerator (q : A ⧸ N) :
    cyclicOverQuotientElement N q ⧸
      cyclicOverNormalSubgroup N q :=
  QuotientGroup.mk' (cyclicOverNormalSubgroup N q)
    (cyclicOverQuotientGenerator N q)

@[simp]
theorem cyclicOverQuotientGenerator_ambientQuotient
    (q : A ⧸ N) :
    QuotientGroup.mk' N
        ((cyclicOverQuotientGenerator N q :
          cyclicOverQuotientElement N q) : A) =
      q :=
  Quotient.out_eq' q

/-- The canonical quotient class generates `N⟨q⟩ / N`. -/
theorem mem_zpowers_cyclicOverInternalQuotientGenerator
    (q : A ⧸ N)
    (x :
      cyclicOverQuotientElement N q ⧸
        cyclicOverNormalSubgroup N q) :
    x ∈ Subgroup.zpowers
      (cyclicOverInternalQuotientGenerator N q) := by
  let H := cyclicOverNormalSubgroup N q
  obtain ⟨u, rfl⟩ :=
    QuotientGroup.mk'_surjective H x
  obtain ⟨z, hz⟩ :=
    Subgroup.mem_zpowers_iff.mp u.2
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨z, ?_⟩
  rw [cyclicOverInternalQuotientGenerator,
    ← map_zpow]
  apply (QuotientGroup.eq_iff_div_mem (N := H)).mpr
  change
    (((cyclicOverQuotientGenerator N q) ^ z /
      u : cyclicOverQuotientElement N q) :
        cyclicOverQuotientElement N q) ∈ H
  change
    (((cyclicOverQuotientGenerator N q) ^ z /
      u : cyclicOverQuotientElement N q) : A) ∈ N
  apply (QuotientGroup.eq_iff_div_mem (N := N)).mp
  calc
    QuotientGroup.mk' N
        ((((cyclicOverQuotientGenerator N q) ^ z :
          cyclicOverQuotientElement N q)) : A) =
        (QuotientGroup.mk' N
          ((cyclicOverQuotientGenerator N q :
            cyclicOverQuotientElement N q) : A)) ^ z := by
          simp
    _ = q ^ z := by
      rw [cyclicOverQuotientGenerator_ambientQuotient]
    _ = QuotientGroup.mk' N (u : A) := hz

/-- A quotient-linear character is determined by its value on the canonical
generator of `N⟨q⟩ / N`. -/
theorem quotientLinearCharacter_ext_generator
    (q : A ⧸ N)
    {beta gamma :
      (cyclicOverQuotientElement N q ⧸
        cyclicOverNormalSubgroup N q) →* ℂˣ}
    (h :
      beta (cyclicOverInternalQuotientGenerator N q) =
        gamma (cyclicOverInternalQuotientGenerator N q)) :
    beta = gamma := by
  apply MonoidHom.ext
  intro x
  obtain ⟨z, hz⟩ :=
    Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_cyclicOverInternalQuotientGenerator
        N q x)
  rw [← hz, map_zpow, map_zpow, h]

/-- Evaluation of the extension-ratio character on the canonical quotient
generator. -/
def goodElementExtensionRatioValue
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q)
    (d : goodElementCentralizer N q) :
    ℂˣ :=
  goodElementExtensionRatioCharacter
      N θ hinvariant q η d
    (cyclicOverInternalQuotientGenerator N q)

/-- The ratio value is the scalar by which the conjugated extension differs
from the chosen extension on the canonical lift of `q`. -/
theorem goodElementAction_value_cyclicOverQuotientGenerator
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q)
    (d : goodElementCentralizer N q) :
    (goodElementAction N q d • η.1).values
        (cyclicOverQuotientGenerator N q) =
      (goodElementExtensionRatioValue
          N θ hinvariant q η d : ℂ) *
        η.1.values (cyclicOverQuotientGenerator N q) := by
  have h := congrArg
    (fun χ : IrreducibleCharacter
        (cyclicOverQuotientElement N q) =>
      χ.values (cyclicOverQuotientGenerator N q))
    (goodElementExtensionRatioCharacter_spec
      N θ hinvariant q η d)
  simpa only [twist_values, inflateLinearCharacter_apply,
    goodElementExtensionRatioValue,
    cyclicOverInternalQuotientGenerator] using h

@[simp]
theorem goodElementExtensionRatioCharacter_one
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q) :
    goodElementExtensionRatioCharacter
        N θ hinvariant q η 1 = 1 :=
  (goodElementExtensionRatioCharacter_eq_one_iff
    N θ hinvariant q η 1).mpr (by
      rw [show goodElementAction N q
          (1 : goodElementCentralizer N q) = 1 by
        exact map_one (goodElementAction N q)]
      exact one_smul _ _)

theorem goodElementExtensionRatioCharacter_mul
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q)
    (d e : goodElementCentralizer N q) :
    goodElementExtensionRatioCharacter
        N θ hinvariant q η (d * e) =
      goodElementExtensionRatioCharacter
          N θ hinvariant q η d *
        goodElementExtensionRatioCharacter
          N θ hinvariant q η e := by
  let H := cyclicOverNormalSubgroup N q
  let betaD :=
    goodElementExtensionRatioCharacter
      N θ hinvariant q η d
  let betaE :=
    goodElementExtensionRatioCharacter
      N θ hinvariant q η e
  symm
  apply eq_goodElementExtensionRatioCharacter
    N θ hinvariant q η (d * e) (betaD * betaE)
  calc
    goodElementAction N q (d * e) • η.1 =
        goodElementAction N q d •
          (goodElementAction N q e • η.1) := by
      rw [map_mul, mul_smul]
    _ = goodElementAction N q d •
          twist (inflateLinearCharacter H betaE) η.1 := by
      rw [goodElementExtensionRatioCharacter_spec
        N θ hinvariant q η e]
    _ = twist (inflateLinearCharacter H betaE)
          (goodElementAction N q d • η.1) := by
      exact goodElementAction_smul_twist
        N q d (inflateLinearCharacter H betaE)
          (inflateLinearCharacter_subgroup H betaE) η.1
    _ = twist (inflateLinearCharacter H betaE)
          (twist (inflateLinearCharacter H betaD) η.1) := by
      rw [goodElementExtensionRatioCharacter_spec
        N θ hinvariant q η d]
    _ = twist
          (inflateLinearCharacter H (betaD * betaE)) η.1 := by
      rw [← twist_mul]
      congr 1
      apply MonoidHom.ext
      intro x
      simp [inflateLinearCharacter, mul_comm]

/-- The quotient-linear Gallagher ratios form a character-valued
homomorphism on the good-element centralizer. -/
def goodElementExtensionRatioCharacterHom
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q) :
    goodElementCentralizer N q →*
      ((cyclicOverQuotientElement N q ⧸
        cyclicOverNormalSubgroup N q) →* ℂˣ) where
  toFun d :=
    goodElementExtensionRatioCharacter
      N θ hinvariant q η d
  map_one' :=
    goodElementExtensionRatioCharacter_one
      N θ hinvariant q η
  map_mul' d e :=
    goodElementExtensionRatioCharacter_mul
      N θ hinvariant q η d e

/-- Evaluation on the canonical quotient generator packages the Gallagher
ratios as a linear character of the good-element centralizer. -/
def goodElementExtensionRatio
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q) :
    goodElementCentralizer N q →* ℂˣ where
  toFun d :=
    goodElementExtensionRatioValue
      N θ hinvariant q η d
  map_one' := by
    change
      goodElementExtensionRatioCharacter
          N θ hinvariant q η 1
          (cyclicOverInternalQuotientGenerator N q) =
        1
    rw [goodElementExtensionRatioCharacter_one]
    rfl
  map_mul' d e := by
    change
      goodElementExtensionRatioCharacter
          N θ hinvariant q η (d * e)
          (cyclicOverInternalQuotientGenerator N q) =
        goodElementExtensionRatioCharacter
            N θ hinvariant q η d
            (cyclicOverInternalQuotientGenerator N q) *
          goodElementExtensionRatioCharacter
            N θ hinvariant q η e
            (cyclicOverInternalQuotientGenerator N q)
    rw [goodElementExtensionRatioCharacter_mul]
    rfl

@[simp]
theorem goodElementExtensionRatio_apply
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q)
    (d : goodElementCentralizer N q) :
    goodElementExtensionRatio N θ hinvariant q η d =
      goodElementExtensionRatioValue
        N θ hinvariant q η d :=
  rfl

/-- The scalar-valued extension ratio is trivial exactly when the chosen
extension is fixed by every quotient-centralizer element. -/
theorem goodElementExtensionRatio_eq_one_iff
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q) :
    goodElementExtensionRatio N θ hinvariant q η = 1 ↔
      ∀ d : goodElementCentralizer N q,
        goodElementAction N q d • η.1 = η.1 := by
  constructor
  · intro hratio d
    have hd := congrArg
      (fun f : goodElementCentralizer N q →* ℂˣ => f d)
      hratio
    have hdValue :
        goodElementExtensionRatioCharacter
            N θ hinvariant q η d
            (cyclicOverInternalQuotientGenerator N q) =
          (1 :
            (cyclicOverQuotientElement N q ⧸
              cyclicOverNormalSubgroup N q) →* ℂˣ)
            (cyclicOverInternalQuotientGenerator N q) := by
      simpa only [goodElementExtensionRatio_apply,
        goodElementExtensionRatioValue,
        MonoidHom.one_apply] using hd
    have hdCharacter :
        goodElementExtensionRatioCharacter
            N θ hinvariant q η d = 1 :=
      quotientLinearCharacter_ext_generator N q hdValue
    exact
      (goodElementExtensionRatioCharacter_eq_one_iff
        N θ hinvariant q η d).mp hdCharacter
  · intro hfixed
    apply MonoidHom.ext
    intro d
    have hdCharacter :
        goodElementExtensionRatioCharacter
            N θ hinvariant q η d = 1 :=
      (goodElementExtensionRatioCharacter_eq_one_iff
        N θ hinvariant q η d).mpr (hfixed d)
    change
      goodElementExtensionRatioCharacter
          N θ hinvariant q η d
          (cyclicOverInternalQuotientGenerator N q) =
        1
    rw [hdCharacter]
    rfl

/-- The extension-ratio character is trivial exactly for good quotient
elements. -/
theorem goodElementExtensionRatio_eq_one_iff_isGood
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q) :
    goodElementExtensionRatio N θ hinvariant q η = 1 ↔
      IsGoodQuotientElement N θ q :=
  (goodElementExtensionRatio_eq_one_iff
      N θ hinvariant q η).trans
    (isGoodQuotientElement_iff_one_extension
      N θ q η).symm

end IrreducibleCharacter
end McKayConjecture
