/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaPerParameter

/-!
# Gallagher coordinates for the Okuyama--Wajima normal products

This file extracts the two independent invariant linear parameters needed by
the explicit-character form of the ordinary Okuyama--Wajima count.

Extension alone does not make a Gallagher parameter invariant under the
larger ambient group.  The exact automatic statement therefore assumes that
the explicit source character is ambient-invariant and that the explicit
target character is invariant under the Sylow normalizer.  Since the
determinant-normalized base extensions already have the same invariance,
Gallagher freeness proves invariance of each ratio parameter separately.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open CliffordCorrespondence
open GroupTheory

variable {A : Type} [Group A] [Finite A]

namespace IrreducibleCharacter

/-- Two ambient-invariant extensions of the same character differ by an
ambient-invariant linear character.

The subgroup on which the two characters agree is written in the ambient
group `A`, while the extensions live on a larger normal subgroup `L`.  This
form is tailored to normal-product applications and avoids identifying the
source and target quotient parameters. -/
theorem exists_invariantLinearTwist_of_invariantExtensions
    (N L : Subgroup A) [N.Normal]
    (hL : L.Normal)
    (hNL : N ≤ L)
    (chi : IrreducibleCharacter N)
    (psi₀ psi₁ : IrreducibleCharacter L)
    (hpsi₀ :
      IsExtensionAlong
        (Subgroup.inclusion hNL) chi psi₀)
    (hpsi₁ :
      IsExtensionAlong
        (Subgroup.inclusion hNL) chi psi₁)
    (hpsi₀Invariant :
      ∀ (a : A) (x : L),
        psi₀.values
            (conjugateNormalElement L hL a x) =
          psi₀.values x)
    (hpsi₁Invariant :
      ∀ (a : A) (x : L),
        psi₁.values
            (conjugateNormalElement L hL a x) =
          psi₁.values x) :
    ∃ lam : L →* ℂˣ,
      (∀ n : N,
        lam (Subgroup.inclusion hNL n) = 1) ∧
      psi₁ = IrreducibleCharacter.twist lam psi₀ ∧
      ∀ (a : A) (x : L),
        lam (conjugateNormalElement L hL a x) =
          lam x := by
  let N' : Subgroup L := N.subgroupOf L
  let eN : N' ≃* N :=
    Subgroup.subgroupOfEquivOfLe hNL
  let chi' : IrreducibleCharacter N' :=
    chi.comap eN
  have hpsi₀' :
      IsExtensionAlong N'.subtype chi' psi₀ := by
    intro n
    exact hpsi₀ (eN n)
  have hpsi₁' :
      IsExtensionAlong N'.subtype chi' psi₁ := by
    intro n
    exact hpsi₁ (eN n)
  obtain ⟨lam, hlamN', hpsi₁Twist⟩ :=
    hpsi₀'.exists_eq_twist hpsi₁'
  have hlamInvariant :
      ∀ (a : A) (x : L),
        lam (conjugateNormalElement L hL a x) =
          lam x := by
    intro a x
    let lamConj : L →* ℂˣ :=
      lam.comp
        (MulAut.conjNormal (H := L) a).toMonoidHom
    let lamTrivial : LinearCharactersTrivialOn N' :=
      ⟨lam, hlamN'⟩
    have hlamConjN : ∀ n : N',
        lamConj (n : L) = 1 := by
      intro n
      let n' : N' :=
        ⟨MulAut.conjNormal (H := L) a (n : L), by
          exact
            (inferInstance : N.Normal).conj_mem
              (n : A) n.property a⟩
      exact hlamN' n'
    let lamConjTrivial : LinearCharactersTrivialOn N' :=
      ⟨lamConj, hlamConjN⟩
    have htwist :
        IrreducibleCharacter.twist lamConj psi₀ =
          IrreducibleCharacter.twist lam psi₀ := by
      apply IrreducibleCharacter.ext
      funext y
      have h₀ := hpsi₀Invariant a y
      have h₁ := hpsi₁Invariant a y
      rw [hpsi₁Twist,
        IrreducibleCharacter.twist_values,
        IrreducibleCharacter.twist_values] at h₁
      rw [h₀] at h₁
      have hconj :
          MulAut.conjNormal (H := L) a y =
            conjugateNormalElement L hL a y := by
        apply Subtype.ext
        rfl
      have hconj' :
          (MulAut.conjNormal (H := L) a).toMonoidHom y =
            conjugateNormalElement L hL a y :=
        hconj
      simp only [IrreducibleCharacter.twist_values,
        lamConj, MonoidHom.comp_apply]
      rw [hconj']
      exact h₁
    have htrivialEq :
        lamConjTrivial = lamTrivial :=
      (twist_injective_on_linearCharactersTrivialOn
        hpsi₀') htwist
    have hlamEq : lamConj = lam :=
      congrArg Subtype.val htrivialEq
    exact DFunLike.congr_fun hlamEq x
  refine ⟨lam, ?_, hpsi₁Twist, hlamInvariant⟩
  intro n
  exact
    hlamN'
      ⟨Subgroup.inclusion hNL n, n.property⟩

end IrreducibleCharacter

namespace GroupTheory

variable {p : ℕ} [Fact p.Prime]

/-- Descend a linear character of a normal product, trivial on the normal
factor, to the quotient-Sylow coordinates used by the OW twist API. -/
def normalProductGallagherParameter
    (K : Subgroup A) [K.Normal]
    (S : Sylow p A)
    (lam :
      (K ⊔ (S : Subgroup A) : Subgroup A) →* ℂˣ)
    (hlam :
      ∀ k : K,
        lam (Subgroup.inclusion le_sup_left k) = 1) :
    (normalProductQuotientSylow K S :
      Subgroup (A ⧸ K)) →* ℂˣ :=
  let K' :=
    K.subgroupOf (K ⊔ (S : Subgroup A))
  let lamBar :
      (K ⊔ (S : Subgroup A) : Subgroup A) ⧸ K' →* ℂˣ :=
    QuotientGroup.lift K' lam (by
      intro x hx
      exact
        MonoidHom.mem_ker.mpr
          (hlam
            ⟨(x : A), hx⟩))
  lamBar.comp
    (normalProductQuotientEquiv K S).symm.toMonoidHom

/-- Pulling the descended parameter back along the normal-product quotient
projection recovers the original Gallagher linear character. -/
theorem normalProductGallagherParameter_comp_projection
    (K : Subgroup A) [K.Normal]
    (S : Sylow p A)
    (lam :
      (K ⊔ (S : Subgroup A) : Subgroup A) →* ℂˣ)
    (hlam :
      ∀ k : K,
        lam (Subgroup.inclusion le_sup_left k) = 1) :
    (normalProductGallagherParameter K S lam hlam).comp
        (normalProductQuotientProjection K S) =
      lam := by
  apply MonoidHom.ext
  intro x
  change
    QuotientGroup.lift
          (K.subgroupOf (K ⊔ (S : Subgroup A)))
          lam
          (by
            intro z hz
            exact
              MonoidHom.mem_ker.mpr
                (hlam ⟨(z : A), hz⟩))
          ((normalProductQuotientEquiv K S).symm
            (normalProductQuotientProjection K S x)) =
      lam x
  have hinverse :
      (normalProductQuotientEquiv K S).symm
          (normalProductQuotientProjection K S x) =
        QuotientGroup.mk'
          (K.subgroupOf (K ⊔ (S : Subgroup A))) x := by
    rw [← normalProductQuotientEquiv_mk K S]
    exact (normalProductQuotientEquiv K S).symm_apply_apply _
  rw [hinverse]
  exact
    QuotientGroup.lift_mk'
      (N := K.subgroupOf (K ⊔ (S : Subgroup A)))
      (φ := lam)
      (by
        intro z hz
        exact
          MonoidHom.mem_ker.mpr
            (hlam ⟨(z : A), hz⟩))
      x

/-- Ambient invariance of a Gallagher linear character descends to
conjugation invariance of its quotient-Sylow parameter. -/
theorem normalProductGallagherParameter_isConjugationInvariant
    (K : Subgroup A) [K.Normal]
    (S : Sylow p A)
    (hKS : (K ⊔ (S : Subgroup A)).Normal)
    (lam :
      (K ⊔ (S : Subgroup A) : Subgroup A) →* ℂˣ)
    (hlam :
      ∀ k : K,
        lam (Subgroup.inclusion le_sup_left k) = 1)
    (hlamInvariant :
      ∀ (a : A)
        (x : (K ⊔ (S : Subgroup A) : Subgroup A)),
        lam
            (conjugateNormalElement
              (K ⊔ (S : Subgroup A) : Subgroup A)
              hKS a x) =
          lam x) :
    letI :
        (normalProductQuotientSylow K S :
          Subgroup (A ⧸ K)).Normal :=
      normalProductQuotientSylow_normal K S hKS
    MonoidHom.IsConjugationInvariant
      (normalProductQuotientSylow K S :
        Subgroup (A ⧸ K))
      (normalProductGallagherParameter K S lam hlam) := by
  letI :
      (normalProductQuotientSylow K S :
        Subgroup (A ⧸ K)).Normal :=
    normalProductQuotientSylow_normal K S hKS
  intro g x
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective K g
  obtain ⟨y, rfl⟩ :=
    normalProductQuotientProjection_surjective K S x
  let y' :
      (K ⊔ (S : Subgroup A) : Subgroup A) :=
    conjugateNormalElement
      (K ⊔ (S : Subgroup A) : Subgroup A)
      hKS a⁻¹ y
  have hprojection :
      (⟨(QuotientGroup.mk' K a)⁻¹ *
          (normalProductQuotientProjection K S y :
            A ⧸ K) *
          QuotientGroup.mk' K a, by
        exact
          (inferInstance :
            (normalProductQuotientSylow K S :
              Subgroup (A ⧸ K)).Normal).conj_mem'
            _ (normalProductQuotientProjection K S y).property
            (QuotientGroup.mk' K a)⟩ :
        normalProductQuotientSylow K S) =
        normalProductQuotientProjection K S y' := by
    apply Subtype.ext
    simp only [normalProductQuotientProjection_apply,
      y', conjugateNormalElement, map_mul, map_inv,
      inv_inv]
  let mu :=
    normalProductGallagherParameter K S lam hlam
  have hrestrict :
      mu.comp (normalProductQuotientProjection K S) =
        lam :=
    normalProductGallagherParameter_comp_projection
      K S lam hlam
  calc
    mu
        ⟨(QuotientGroup.mk' K a)⁻¹ *
            (normalProductQuotientProjection K S y :
              A ⧸ K) *
            QuotientGroup.mk' K a, _⟩ =
      mu (normalProductQuotientProjection K S y') := by
        rw [hprojection]
    _ = lam y' :=
      DFunLike.congr_fun hrestrict y'
    _ = lam y :=
      hlamInvariant a⁻¹ y
    _ = mu (normalProductQuotientProjection K S y) :=
      (DFunLike.congr_fun hrestrict y).symm

end GroupTheory

variable {p : ℕ} [Fact p.Prime]

/-- Gallagher coordinates on a normal product can be expressed in the
quotient-Sylow coordinates used by the independent-twist theorem. -/
theorem exists_invariantNormalProductGallagherParameter
    (K : Subgroup A) [K.Normal]
    (S : Sylow p A)
    (hKS : (K ⊔ (S : Subgroup A)).Normal)
    (chi : IrreducibleCharacter K)
    (psi₀ psi₁ :
      IrreducibleCharacter
        (K ⊔ (S : Subgroup A) : Subgroup A))
    (hpsi₀ :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion le_sup_left) chi psi₀)
    (hpsi₁ :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion le_sup_left) chi psi₁)
    (hpsi₀Invariant :
      ∀ (a : A)
        (x : (K ⊔ (S : Subgroup A) : Subgroup A)),
        psi₀.values
            (conjugateNormalElement
              (K ⊔ (S : Subgroup A) : Subgroup A)
              hKS a x) =
          psi₀.values x)
    (hpsi₁Invariant :
      ∀ (a : A)
        (x : (K ⊔ (S : Subgroup A) : Subgroup A)),
        psi₁.values
            (conjugateNormalElement
              (K ⊔ (S : Subgroup A) : Subgroup A)
              hKS a x) =
          psi₁.values x) :
    ∃ (mu :
        (normalProductQuotientSylow K S :
          Subgroup (A ⧸ K)) →* ℂˣ),
      (letI :
          (normalProductQuotientSylow K S :
            Subgroup (A ⧸ K)).Normal :=
        normalProductQuotientSylow_normal K S hKS
      MonoidHom.IsConjugationInvariant
        (normalProductQuotientSylow K S :
          Subgroup (A ⧸ K))
        mu) ∧
      psi₁ =
        IrreducibleCharacter.twist
          (mu.comp
            (normalProductQuotientProjection K S))
          psi₀ := by
  obtain ⟨lam, hlam, hpsi₁Twist, hlamInvariant⟩ :=
    IrreducibleCharacter.exists_invariantLinearTwist_of_invariantExtensions
      K (K ⊔ (S : Subgroup A) : Subgroup A)
      hKS le_sup_left chi psi₀ psi₁
      hpsi₀ hpsi₁ hpsi₀Invariant hpsi₁Invariant
  let mu :=
    normalProductGallagherParameter K S lam hlam
  refine ⟨mu, ?_, ?_⟩
  · exact
      normalProductGallagherParameter_isConjugationInvariant
        K S hKS lam hlam hlamInvariant
  · have hrestrict :
        mu.comp (normalProductQuotientProjection K S) =
          lam := by
      exact
        normalProductGallagherParameter_comp_projection
          K S lam hlam
    rw [hpsi₁Twist, hrestrict]

variable {Γ : Type} [Group Γ] [Finite Γ]

/-! ### The source coordinate -/

/-- The one-sided source half of the independent Gallagher-coordinate
package. -/
def OkuyamaWajimaSourceGallagherParameterCoordinates
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (hinvariant : ∀ g : Γ, g • θ.1.1 = θ.1.1)
    (alpha :
      IrreducibleCharacter
        (K ⊔ (S : Subgroup Γ) : Subgroup Γ)) :
    Prop :=
  let c :=
    okuyamaWajimaInvariantCanonicalBaseExtensionData
      S K hK hKS d θ hinvariant
  ∃ (mu :
      (normalProductQuotientSylow K S :
        Subgroup (Γ ⧸ K)) →* ℂˣ),
    (letI :
        (normalProductQuotientSylow K S :
          Subgroup (Γ ⧸ K)).Normal :=
      normalProductQuotientSylow_normal K S hKS
    MonoidHom.IsConjugationInvariant
      (normalProductQuotientSylow K S :
        Subgroup (Γ ⧸ K))
      mu) ∧
    alpha =
      IrreducibleCharacter.twist
        (mu.comp
          (normalProductQuotientProjection K S))
        c.sourceExtension

/-- An invariant source extension automatically has the required
quotient-Sylow Gallagher coordinate. -/
theorem okuyamaWajimaSourceGallagherParameterCoordinates_of_extension
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (hinvariant : ∀ g : Γ, g • θ.1.1 = θ.1.1)
    (alpha :
      IrreducibleCharacter
        (K ⊔ (S : Subgroup Γ) : Subgroup Γ))
    (halphaExtension :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion le_sup_left)
        θ.1.1 alpha)
    (halphaInvariant :
      ∀ (g : Γ)
        (x : (K ⊔ (S : Subgroup Γ) : Subgroup Γ)),
        alpha.values
            (conjugateNormalElement
              (K ⊔ (S : Subgroup Γ) : Subgroup Γ)
              hKS g x) =
          alpha.values x) :
    OkuyamaWajimaSourceGallagherParameterCoordinates
      S K hK hKS d θ hinvariant alpha := by
  let c :=
    okuyamaWajimaInvariantCanonicalBaseExtensionData
      S K hK hKS d θ hinvariant
  exact
    exists_invariantNormalProductGallagherParameter
      K S hKS θ.1.1 c.sourceExtension alpha
      c.source_isExtension halphaExtension
      c.source_invariant halphaInvariant

namespace GroupTheory

/-! ### Native quotient coordinates on the target normal product -/

/-- The target normal-product projection is onto its quotient Sylow
subgroup. -/
theorem okuyamaWajimaTargetQuotientProjection_surjective
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K) :
    letI :
        (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ)).Normal :=
      internalFixedPoints_normal K (S : Subgroup Γ)
    Function.Surjective
      (okuyamaWajimaTargetQuotientProjection S K hK) := by
  letI :
      (okuyamaWajimaInternalFixedPoints
        K (S : Subgroup Γ)).Normal :=
    internalFixedPoints_normal K (S : Subgroup Γ)
  intro y
  have hy :
      (y :
        Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
          okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ)) ∈
        (okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ)).map
            (QuotientGroup.mk'
              (okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ))) := by
    rw [map_internalNormalProduct_eq_quotientSylow
      S K hK]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxy

/-- The kernel of the target normal-product projection is its internal
fixed-point subgroup. -/
theorem ker_okuyamaWajimaTargetQuotientProjection
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K) :
    letI :
        (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ)).Normal :=
      internalFixedPoints_normal K (S : Subgroup Γ)
    (okuyamaWajimaTargetQuotientProjection
        S K hK).ker =
      (okuyamaWajimaInternalFixedPoints
        K (S : Subgroup Γ)).subgroupOf
          (okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)) := by
  letI :
      (okuyamaWajimaInternalFixedPoints
        K (S : Subgroup Γ)).Normal :=
    internalFixedPoints_normal K (S : Subgroup Γ)
  ext x
  constructor
  · intro hx
    change
      okuyamaWajimaTargetQuotientProjection S K hK x =
        1 at hx
    have hx' :=
      congrArg
        (fun z :
          normalProductQuotientSylow
            (okuyamaWajimaInternalFixedPoints
              K (S : Subgroup Γ))
            (okuyamaWajimaSylowInNormalizer S) =>
          (z :
            Subgroup.normalizer
                ((S : Subgroup Γ) : Set Γ) ⧸
              okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ)))
        hx
    change
      QuotientGroup.mk'
          (okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ))
          (x :
            Subgroup.normalizer
              ((S : Subgroup Γ) : Set Γ)) =
        1 at hx'
    exact
      (QuotientGroup.eq_one_iff
        (x :
          Subgroup.normalizer
            ((S : Subgroup Γ) : Set Γ))).mp hx'
  · intro hx
    change
      okuyamaWajimaTargetQuotientProjection S K hK x =
        1
    apply Subtype.ext
    change
      QuotientGroup.mk'
          (okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ))
          (x :
            Subgroup.normalizer
              ((S : Subgroup Γ) : Set Γ)) =
        1
    exact
      (QuotientGroup.eq_one_iff
        (x :
          Subgroup.normalizer
            ((S : Subgroup Γ) : Set Γ))).mpr hx

/-- First-isomorphism coordinates from the target normal product modulo its
fixed points to the target quotient Sylow subgroup. -/
def okuyamaWajimaTargetNormalProductQuotientEquiv
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K) :
    letI :
        (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ)).Normal :=
      internalFixedPoints_normal K (S : Subgroup Γ)
    okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ) ⧸
        (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ)).subgroupOf
            (okuyamaWajimaInternalNormalProduct
              K (S : Subgroup Γ)) ≃*
      (normalProductQuotientSylow
        (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ))
        (okuyamaWajimaSylowInNormalizer S) :
          Subgroup
            (Subgroup.normalizer
                ((S : Subgroup Γ) : Set Γ) ⧸
              okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ))) := by
  letI :
      (okuyamaWajimaInternalFixedPoints
        K (S : Subgroup Γ)).Normal :=
    internalFixedPoints_normal K (S : Subgroup Γ)
  let f :=
    okuyamaWajimaTargetQuotientProjection S K hK
  have hker :
      (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ)).subgroupOf
            (okuyamaWajimaInternalNormalProduct
              K (S : Subgroup Γ)) =
        f.ker :=
    (ker_okuyamaWajimaTargetQuotientProjection
      S K hK).symm
  have hrange : f.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      (okuyamaWajimaTargetQuotientProjection_surjective
        S K hK)
  exact
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      ((QuotientGroup.quotientKerEquivRange f).trans
        ((MulEquiv.subgroupCongr hrange).trans
          Subgroup.topEquiv))

@[simp]
theorem okuyamaWajimaTargetNormalProductQuotientEquiv_mk
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (x :
      okuyamaWajimaInternalNormalProduct
        K (S : Subgroup Γ)) :
    letI :
        (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ)).Normal :=
      internalFixedPoints_normal K (S : Subgroup Γ)
    okuyamaWajimaTargetNormalProductQuotientEquiv
        S K hK
        (QuotientGroup.mk'
          ((okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ)).subgroupOf
              (okuyamaWajimaInternalNormalProduct
                K (S : Subgroup Γ))) x) =
      okuyamaWajimaTargetQuotientProjection
        S K hK x := by
  rfl

/-- Descend a target normal-product Gallagher character to the target
quotient-Sylow coordinate. -/
def okuyamaWajimaTargetGallagherParameter
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (lam :
      okuyamaWajimaInternalNormalProduct
        K (S : Subgroup Γ) →* ℂˣ)
    (hlam :
      ∀ d :
          okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ),
        lam
            (Subgroup.inclusion
              (internalFixedPoints_le_internalNormalProduct
                K (S : Subgroup Γ)) d) =
          1) :
    letI :
        (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ)).Normal :=
      internalFixedPoints_normal K (S : Subgroup Γ)
    (normalProductQuotientSylow
      (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
      (okuyamaWajimaSylowInNormalizer S) :
        Subgroup
          (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
            okuyamaWajimaInternalFixedPoints
              K (S : Subgroup Γ))) →* ℂˣ := by
  letI :
      (okuyamaWajimaInternalFixedPoints
        K (S : Subgroup Γ)).Normal :=
    internalFixedPoints_normal K (S : Subgroup Γ)
  let D' :=
    (okuyamaWajimaInternalFixedPoints
      K (S : Subgroup Γ)).subgroupOf
        (okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ))
  let lamBar :
      okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ) ⧸ D' →* ℂˣ :=
    QuotientGroup.lift D' lam (by
      intro x hx
      exact
        MonoidHom.mem_ker.mpr
          (hlam
            ⟨(x :
              Subgroup.normalizer
                ((S : Subgroup Γ) : Set Γ)), hx⟩))
  exact
    lamBar.comp
      (okuyamaWajimaTargetNormalProductQuotientEquiv
        S K hK).symm.toMonoidHom

/-- Pullback along the native target projection recovers the target
Gallagher linear character. -/
theorem okuyamaWajimaTargetGallagherParameter_comp_projection
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (lam :
      okuyamaWajimaInternalNormalProduct
        K (S : Subgroup Γ) →* ℂˣ)
    (hlam :
      ∀ d :
          okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ),
        lam
            (Subgroup.inclusion
              (internalFixedPoints_le_internalNormalProduct
                K (S : Subgroup Γ)) d) =
          1) :
    letI :
        (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ)).Normal :=
      internalFixedPoints_normal K (S : Subgroup Γ)
    (okuyamaWajimaTargetGallagherParameter
        S K hK lam hlam).comp
          (okuyamaWajimaTargetQuotientProjection
            S K hK) =
      lam := by
  letI :
      (okuyamaWajimaInternalFixedPoints
        K (S : Subgroup Γ)).Normal :=
    internalFixedPoints_normal K (S : Subgroup Γ)
  apply MonoidHom.ext
  intro x
  change
    QuotientGroup.lift
          ((okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ)).subgroupOf
              (okuyamaWajimaInternalNormalProduct
                K (S : Subgroup Γ)))
          lam
          (by
            intro z hz
            exact
              MonoidHom.mem_ker.mpr
                (hlam
                  ⟨(z :
                    Subgroup.normalizer
                      ((S : Subgroup Γ) : Set Γ)), hz⟩))
          ((okuyamaWajimaTargetNormalProductQuotientEquiv
            S K hK).symm
              (okuyamaWajimaTargetQuotientProjection
                S K hK x)) =
      lam x
  have hinverse :
      (okuyamaWajimaTargetNormalProductQuotientEquiv
          S K hK).symm
          (okuyamaWajimaTargetQuotientProjection
            S K hK x) =
        QuotientGroup.mk'
          ((okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ)).subgroupOf
              (okuyamaWajimaInternalNormalProduct
                K (S : Subgroup Γ))) x := by
    rw [← okuyamaWajimaTargetNormalProductQuotientEquiv_mk
      S K hK]
    exact
      (okuyamaWajimaTargetNormalProductQuotientEquiv
        S K hK).symm_apply_apply _
  rw [hinverse]
  exact
    QuotientGroup.lift_mk'
      (N :=
        (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ)).subgroupOf
            (okuyamaWajimaInternalNormalProduct
              K (S : Subgroup Γ)))
      (φ := lam)
      (by
        intro z hz
        exact
          MonoidHom.mem_ker.mpr
            (hlam
              ⟨(z :
                Subgroup.normalizer
                  ((S : Subgroup Γ) : Set Γ)), hz⟩))
      x

/-- Ambient normalizer-invariance of a target Gallagher character descends
to conjugation invariance of its target quotient-Sylow parameter. -/
theorem okuyamaWajimaTargetGallagherParameter_isConjugationInvariant
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (lam :
      okuyamaWajimaInternalNormalProduct
        K (S : Subgroup Γ) →* ℂˣ)
    (hlam :
      ∀ d :
          okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ),
        lam
            (Subgroup.inclusion
              (internalFixedPoints_le_internalNormalProduct
                K (S : Subgroup Γ)) d) =
          1)
    (hlamInvariant :
      ∀ (g :
          Subgroup.normalizer ((S : Subgroup Γ) : Set Γ))
        (x :
          okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)),
        lam
            (conjugateNormalElement
              (okuyamaWajimaInternalNormalProduct
                K (S : Subgroup Γ))
              (internalNormalProduct_normal
                K (S : Subgroup Γ) hKS)
              g x) =
          lam x) :
    letI :
        (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ)).Normal :=
      internalFixedPoints_normal K (S : Subgroup Γ)
    letI :
        (normalProductQuotientSylow
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
          (okuyamaWajimaSylowInNormalizer S) :
            Subgroup
              (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
                okuyamaWajimaInternalFixedPoints
                  K (S : Subgroup Γ))).Normal :=
      okuyamaWajimaQuotientSylow_normal S K hK hKS
    MonoidHom.IsConjugationInvariant
      (normalProductQuotientSylow
        (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
        (okuyamaWajimaSylowInNormalizer S) :
          Subgroup
            (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
              okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ)))
      (okuyamaWajimaTargetGallagherParameter
        S K hK lam hlam) := by
  letI :
      (okuyamaWajimaInternalFixedPoints
        K (S : Subgroup Γ)).Normal :=
    internalFixedPoints_normal K (S : Subgroup Γ)
  letI :
      (normalProductQuotientSylow
        (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
        (okuyamaWajimaSylowInNormalizer S) :
          Subgroup
            (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
              okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ))).Normal :=
    okuyamaWajimaQuotientSylow_normal S K hK hKS
  intro g x
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (okuyamaWajimaInternalFixedPoints
        K (S : Subgroup Γ)) g
  obtain ⟨y, rfl⟩ :=
    okuyamaWajimaTargetQuotientProjection_surjective
      S K hK x
  let y' :
      okuyamaWajimaInternalNormalProduct
        K (S : Subgroup Γ) :=
    conjugateNormalElement
      (okuyamaWajimaInternalNormalProduct
        K (S : Subgroup Γ))
      (internalNormalProduct_normal
        K (S : Subgroup Γ) hKS)
      a⁻¹ y
  have hprojection :
      (⟨(QuotientGroup.mk'
            (okuyamaWajimaInternalFixedPoints
              K (S : Subgroup Γ)) a)⁻¹ *
          (okuyamaWajimaTargetQuotientProjection
              S K hK y :
            Subgroup.normalizer
                ((S : Subgroup Γ) : Set Γ) ⧸
              okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ)) *
          QuotientGroup.mk'
            (okuyamaWajimaInternalFixedPoints
              K (S : Subgroup Γ)) a, by
        exact
          (inferInstance :
            (normalProductQuotientSylow
              (okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ))
              (okuyamaWajimaSylowInNormalizer S) :
                Subgroup
                  (Subgroup.normalizer
                      ((S : Subgroup Γ) : Set Γ) ⧸
                    okuyamaWajimaInternalFixedPoints
                      K (S : Subgroup Γ))).Normal).conj_mem'
            _
            (okuyamaWajimaTargetQuotientProjection
              S K hK y).property
            (QuotientGroup.mk'
              (okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ)) a)⟩ :
        normalProductQuotientSylow
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
          (okuyamaWajimaSylowInNormalizer S)) =
        okuyamaWajimaTargetQuotientProjection
          S K hK y' := by
    apply Subtype.ext
    simp only [okuyamaWajimaTargetQuotientProjection_apply,
      y', conjugateNormalElement, map_mul, map_inv,
      inv_inv]
  let mu :=
    okuyamaWajimaTargetGallagherParameter
      S K hK lam hlam
  have hrestrict :
      mu.comp
          (okuyamaWajimaTargetQuotientProjection
            S K hK) =
        lam :=
    okuyamaWajimaTargetGallagherParameter_comp_projection
      S K hK lam hlam
  calc
    mu
        ⟨(QuotientGroup.mk'
              (okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ)) a)⁻¹ *
            (okuyamaWajimaTargetQuotientProjection
                S K hK y :
              Subgroup.normalizer
                  ((S : Subgroup Γ) : Set Γ) ⧸
                okuyamaWajimaInternalFixedPoints
                  K (S : Subgroup Γ)) *
            QuotientGroup.mk'
              (okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ)) a, _⟩ =
      mu (okuyamaWajimaTargetQuotientProjection
        S K hK y') := by
        rw [hprojection]
    _ = lam y' :=
      DFunLike.congr_fun hrestrict y'
    _ = lam y :=
      hlamInvariant a⁻¹ y
    _ = mu (okuyamaWajimaTargetQuotientProjection
        S K hK y) :=
      (DFunLike.congr_fun hrestrict y).symm

end GroupTheory

/-! ### The target coordinate -/

/-- The one-sided target half of the independent Gallagher-coordinate
package. -/
def OkuyamaWajimaTargetGallagherParameterCoordinates
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (hinvariant : ∀ g : Γ, g • θ.1.1 = θ.1.1)
    (beta :
      IrreducibleCharacter
        (okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ))) :
    Prop :=
  let c :=
    okuyamaWajimaInvariantCanonicalBaseExtensionData
      S K hK hKS d θ hinvariant
  ∃ (mu :
      letI :
          (okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ)).Normal :=
        internalFixedPoints_normal K (S : Subgroup Γ)
      (normalProductQuotientSylow
        (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
        (okuyamaWajimaSylowInNormalizer S) :
          Subgroup
            (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
              okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ))) →* ℂˣ),
    (letI :
        (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ)).Normal :=
      internalFixedPoints_normal K (S : Subgroup Γ)
    letI :
        (normalProductQuotientSylow
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
          (okuyamaWajimaSylowInNormalizer S) :
            Subgroup
              (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
                okuyamaWajimaInternalFixedPoints
                  K (S : Subgroup Γ))).Normal :=
      okuyamaWajimaQuotientSylow_normal S K hK hKS
    MonoidHom.IsConjugationInvariant
      (normalProductQuotientSylow
        (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
        (okuyamaWajimaSylowInNormalizer S) :
          Subgroup
            (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
              okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ)))
      mu) ∧
    beta =
      IrreducibleCharacter.twist
        (mu.comp
          (okuyamaWajimaTargetQuotientProjection
            S K hK))
        c.targetExtension

/-- An invariant target extension automatically has the required native
target quotient-Sylow Gallagher coordinate. -/
theorem okuyamaWajimaTargetGallagherParameterCoordinates_of_extension
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (hinvariant : ∀ g : Γ, g • θ.1.1 = θ.1.1)
    (beta :
      IrreducibleCharacter
        (okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ)))
    (hbetaExtension :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion
          (internalFixedPoints_le_internalNormalProduct
            K (S : Subgroup Γ)))
        (okuyamaWajimaInternalFixedPointCharacter
          S K d θ)
        beta)
    (hbetaInvariant :
      ∀ (g :
          Subgroup.normalizer ((S : Subgroup Γ) : Set Γ))
        (x :
          okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)),
        beta.values
            (conjugateNormalElement
              (okuyamaWajimaInternalNormalProduct
                K (S : Subgroup Γ))
              (internalNormalProduct_normal
                K (S : Subgroup Γ) hKS)
              g x) =
          beta.values x) :
    OkuyamaWajimaTargetGallagherParameterCoordinates
      S K hK hKS d θ hinvariant beta := by
  letI :
      (okuyamaWajimaInternalFixedPoints
        K (S : Subgroup Γ)).Normal :=
    internalFixedPoints_normal K (S : Subgroup Γ)
  let c :=
    okuyamaWajimaInvariantCanonicalBaseExtensionData
      S K hK hKS d θ hinvariant
  obtain ⟨lam, hlam, hbetaTwist, hlamInvariant⟩ :=
    IrreducibleCharacter.exists_invariantLinearTwist_of_invariantExtensions
      (okuyamaWajimaInternalFixedPoints
        K (S : Subgroup Γ))
      (okuyamaWajimaInternalNormalProduct
        K (S : Subgroup Γ))
      (internalNormalProduct_normal
        K (S : Subgroup Γ) hKS)
      (internalFixedPoints_le_internalNormalProduct
        K (S : Subgroup Γ))
      (okuyamaWajimaInternalFixedPointCharacter
        S K d θ)
      c.targetExtension beta
      c.target_isExtension hbetaExtension
      c.target_invariant hbetaInvariant
  let mu :=
    okuyamaWajimaTargetGallagherParameter
      S K hK lam hlam
  refine ⟨mu, ?_, ?_⟩
  · exact
      okuyamaWajimaTargetGallagherParameter_isConjugationInvariant
        S K hK hKS lam hlam hlamInvariant
  · have hrestrict :
        mu.comp
            (okuyamaWajimaTargetQuotientProjection
              S K hK) =
          lam := by
      exact
        okuyamaWajimaTargetGallagherParameter_comp_projection
          S K hK lam hlam
    rw [hbetaTwist, hrestrict]

/-! ### Independent assembly -/

/-- The exact independent Gallagher-coordinate seam is automatic for an
ambient-invariant source extension and an independently chosen
normalizer-invariant target extension.

No equation or transport between the two quotient-Sylow parameters appears
in either the hypotheses or the proof. -/
theorem
    okuyamaWajimaIndependentGallagherParameterCoordinates_of_extensions
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (hinvariant : ∀ g : Γ, g • θ.1.1 = θ.1.1)
    (alpha :
      IrreducibleCharacter
        (K ⊔ (S : Subgroup Γ) : Subgroup Γ))
    (beta :
      IrreducibleCharacter
        (okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ)))
    (halphaExtension :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion le_sup_left)
        θ.1.1 alpha)
    (halphaInvariant :
      ∀ (g : Γ)
        (x : (K ⊔ (S : Subgroup Γ) : Subgroup Γ)),
        alpha.values
            (conjugateNormalElement
              (K ⊔ (S : Subgroup Γ) : Subgroup Γ)
              hKS g x) =
          alpha.values x)
    (hbetaExtension :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion
          (internalFixedPoints_le_internalNormalProduct
            K (S : Subgroup Γ)))
        (okuyamaWajimaInternalFixedPointCharacter
          S K d θ)
        beta)
    (hbetaInvariant :
      ∀ (g :
          Subgroup.normalizer ((S : Subgroup Γ) : Set Γ))
        (x :
          okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)),
        beta.values
            (conjugateNormalElement
              (okuyamaWajimaInternalNormalProduct
                K (S : Subgroup Γ))
              (internalNormalProduct_normal
                K (S : Subgroup Γ) hKS)
              g x) =
          beta.values x) :
    OkuyamaWajimaIndependentGallagherParameterCoordinates
      S K hK hKS d θ hinvariant alpha beta := by
  obtain ⟨muSource, hmuSource, halpha⟩ :=
    okuyamaWajimaSourceGallagherParameterCoordinates_of_extension
      S K hK hKS d θ hinvariant alpha
      halphaExtension halphaInvariant
  obtain ⟨muTarget, hmuTarget, hbeta⟩ :=
    okuyamaWajimaTargetGallagherParameterCoordinates_of_extension
      S K hK hKS d θ hinvariant beta
      hbetaExtension hbetaInvariant
  exact
    ⟨muSource, hmuSource, halpha,
      muTarget, hmuTarget, hbeta⟩

/-- Ordinary lying-over cardinalities agree for independently chosen
ambient-invariant source and target extensions. -/
theorem okuyamaWajima_natCard_over_eq_of_invariantExtensions
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (hinvariant : ∀ g : Γ, g • θ.1.1 = θ.1.1)
    (how :
      OkuyamaWajimaComplementUniformOrdinaryInput
        S K hK hKS d θ)
    (alpha :
      IrreducibleCharacter
        (K ⊔ (S : Subgroup Γ) : Subgroup Γ))
    (beta :
      IrreducibleCharacter
        (okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ)))
    (halphaExtension :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion le_sup_left)
        θ.1.1 alpha)
    (halphaInvariant :
      ∀ (g : Γ)
        (x : (K ⊔ (S : Subgroup Γ) : Subgroup Γ)),
        alpha.values
            (conjugateNormalElement
              (K ⊔ (S : Subgroup Γ) : Subgroup Γ)
              hKS g x) =
          alpha.values x)
    (hbetaExtension :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion
          (internalFixedPoints_le_internalNormalProduct
            K (S : Subgroup Γ)))
        (okuyamaWajimaInternalFixedPointCharacter
          S K d θ)
        beta)
    (hbetaInvariant :
      ∀ (g :
          Subgroup.normalizer ((S : Subgroup Γ) : Set Γ))
        (x :
          okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)),
        beta.values
            (conjugateNormalElement
              (okuyamaWajimaInternalNormalProduct
                K (S : Subgroup Γ))
              (internalNormalProduct_normal
                K (S : Subgroup Γ) hKS)
              g x) =
          beta.values x) :
    Nat.card
        (IrreducibleCharactersOverAlong
          (K ⊔ (S : Subgroup Γ) : Subgroup Γ).subtype
          alpha) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)).subtype
          beta) := by
  apply
    natCard_over_eq_of_independentGallagherParameterCoordinates
      S K hK hKS d θ hinvariant how alpha beta
  exact
    okuyamaWajimaIndependentGallagherParameterCoordinates_of_extensions
      S K hK hKS d θ hinvariant alpha beta
      halphaExtension halphaInvariant
      hbetaExtension hbetaInvariant

end McKayConjecture
