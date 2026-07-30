/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaPrimeLocal

/-!
# The printed Okuyama--Wajima theorem in prime-away coordinates

This file separates two logically different steps in the source-audited
prime-local argument.

* A quotient Sylow subgroup `R` determines its full preimage `V_r` in
  `V`.  The first part proves all coordinate transports between extension
  existence on the two restricted character triples and extension
  existence on `K V_r` and `V_r`.
* The printed Okuyama--Wajima theorem is used only after adjoining `Q`,
  on `K Q V_r` and its Sylow normalizer `Q V_r`.  Its exact application
  scope is named below; removing the adjoined `Q` is a separate Navarro
  local--global input.

In particular no Sylow or intersection assertion is made for the original
mixed-prime subgroup `V`.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open GroupTheory

variable {A : Type} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable (K Q V : Subgroup A) [K.Normal]

/-- The full preimage in `V` of a quotient Sylow subgroup in the target
Okuyama--Wajima character triple. -/
abbrev okuyamaWajimaTargetSylowPreimage
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    {r : ℕ} [Fact r.Prime]
    (R : Sylow r
      (V ⧸
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant).normalSubgroup)) :
    Subgroup V :=
  quotientSubgroupPreimage
    (invariantOkuyamaWajimaTargetTriple
      K Q V hV hCV d theta hinvariant).normalSubgroup
    (R : Subgroup
      (V ⧸
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant).normalSubgroup))

/-- The ambient image `V_r ≤ A` of the target quotient Sylow preimage. -/
abbrev okuyamaWajimaTargetSylowPreimageImage
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    {r : ℕ} [Fact r.Prime]
    (R : Sylow r
      (V ⧸
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant).normalSubgroup)) :
    Subgroup A :=
  (okuyamaWajimaTargetSylowPreimage
    K Q V hV hCV d theta hinvariant R).map V.subtype

/-- The fixed-point kernel lies in every ambient quotient Sylow
preimage. -/
theorem coprimeFixedPoints_le_okuyamaWajimaTargetSylowPreimageImage
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    {r : ℕ} [Fact r.Prime]
    (R : Sylow r
      (V ⧸
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant).normalSubgroup)) :
    coprimeFixedPoints K Q ≤
      okuyamaWajimaTargetSylowPreimageImage
        K Q V hV hCV d theta hinvariant R := by
  intro c hc
  let T :=
    invariantOkuyamaWajimaTargetTriple
      K Q V hV hCV d theta hinvariant
  let v : V := ⟨c, hCV hc⟩
  let l :
      okuyamaWajimaTargetSylowPreimage
        K Q V hV hCV d theta hinvariant R :=
    ⟨v,
      normal_le_quotientSubgroupPreimage
        T.normalSubgroup
        (R : Subgroup (V ⧸ T.normalSubgroup))
        hc⟩
  exact ⟨l, l.2, rfl⟩

/-- Every target quotient Sylow preimage still normalizes `Q`. -/
theorem okuyamaWajimaTargetSylowPreimageImage_le_normalizer
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    {r : ℕ} [Fact r.Prime]
    (R : Sylow r
      (V ⧸
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant).normalSubgroup)) :
    okuyamaWajimaTargetSylowPreimageImage
        K Q V hV hCV d theta hinvariant R ≤
      Subgroup.normalizer (Q : Set A) := by
  rintro _ ⟨v, _hv, rfl⟩
  exact hV v.2

/-- The corresponding full quotient Sylow preimage on the source side. -/
abbrev okuyamaWajimaSourceSylowPreimage
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    {r : ℕ} [Fact r.Prime]
    (R : Sylow r
      (V ⧸
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant).normalSubgroup)) :
    Subgroup (V ⊔ K : Subgroup A) :=
  letI :
      ((coprimeFixedPoints K Q).subgroupOf V).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hV.trans
        (normalizer_le_normalizer_inf_centralizer K Q))
  let e :=
    okuyamaWajimaQuotientEquiv
      K Q hQ hK V hV hCV
  quotientSubgroupPreimage
    (K.subgroupOf (V ⊔ K : Subgroup A))
    (R.mapSurjective
      (f := e.toMonoidHom) e.surjective :
      Subgroup
        ((V ⊔ K : Subgroup A) ⧸
          K.subgroupOf (V ⊔ K : Subgroup A)))

/-- The source Sylow preimage, mapped back to `A`, is exactly
`K V_r`.  This is the main quotient-coordinate identity needed to apply
the printed theorem locally. -/
theorem okuyamaWajimaSourceSylowPreimage_map_subtype
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    {r : ℕ} [Fact r.Prime]
    (R : Sylow r
      (V ⧸
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant).normalSubgroup)) :
    (okuyamaWajimaSourceSylowPreimage
        K Q V hQ hK hV hCV d theta hinvariant R).map
        (V ⊔ K : Subgroup A).subtype =
      okuyamaWajimaTargetSylowPreimageImage
          K Q V hV hCV d theta hinvariant R ⊔ K := by
  let C := coprimeFixedPoints K Q
  let B := (V ⊔ K : Subgroup A)
  let T :=
    invariantOkuyamaWajimaTargetTriple
      K Q V hV hCV d theta hinvariant
  let M := T.normalSubgroup
  let N := K.subgroupOf B
  let e :
      V ⧸ M ≃* B ⧸ N :=
    okuyamaWajimaQuotientEquiv
      K Q hQ hK V hV hCV
  let L :=
    okuyamaWajimaTargetSylowPreimage
      K Q V hV hCV d theta hinvariant R
  let W :=
    okuyamaWajimaTargetSylowPreimageImage
      K Q V hV hCV d theta hinvariant R
  let P : Sylow r (B ⧸ N) :=
    R.mapSurjective
      (f := e.toMonoidHom) e.surjective
  let H :=
    okuyamaWajimaSourceSylowPreimage
      K Q V hQ hK hV hCV d theta hinvariant R
  let j : V →* B := Subgroup.inclusion le_sup_left
  have he (v : V) :
      e (QuotientGroup.mk' M v) =
        QuotientGroup.mk' N (j v) := by
    exact
      okuyamaWajimaQuotientEquiv_mk
        K Q hQ hK V hV hCV v
  have hproduct :
      ∀ b : B,
        ∃ n : N, ∃ v : V,
          (n : B) * j v = b := by
    intro b
    exact
      (invariantOkuyamaWajimaFactorMatchedGroupData
        K Q V hQ hK hV hCV d theta hinvariant).ambient_eq_product b
  apply le_antisymm
  · rintro x ⟨b, hbH, rfl⟩
    obtain ⟨n, v, hnv⟩ := hproduct b
    have hquot :
        e (QuotientGroup.mk' M v) =
          QuotientGroup.mk' N b := by
      calc
        e (QuotientGroup.mk' M v) =
            QuotientGroup.mk' N (j v) :=
          he v
        _ = QuotientGroup.mk' N ((n : B) * j v) := by
          rw [map_mul]
          have hnOne :
              QuotientGroup.mk' N (n : B) = 1 :=
            (QuotientGroup.eq_one_iff (n : B)).mpr n.2
          rw [hnOne, one_mul]
        _ = QuotientGroup.mk' N b := by
          rw [hnv]
    have hbP :
        QuotientGroup.mk' N b ∈
          (P : Subgroup (B ⧸ N)) :=
      by
        change
          QuotientGroup.mk' N b ∈
            (R.mapSurjective
              (f := e.toMonoidHom) e.surjective :
              Subgroup (B ⧸ N))
        exact hbH
    have hvR :
        QuotientGroup.mk' M v ∈
          (R : Subgroup (V ⧸ M)) := by
      have hevP :
          e (QuotientGroup.mk' M v) ∈
            (P : Subgroup (B ⧸ N)) := by
        rw [hquot]
        exact hbP
      simpa [P, Subgroup.mem_map_equiv] using hevP
    have hvW : (v : A) ∈ W := by
      exact ⟨v, hvR, rfl⟩
    have hnK : ((n : B) : A) ∈ K :=
      n.2
    have hcoe :
        ((n : B) : A) * (v : A) = (b : A) :=
      congrArg Subtype.val hnv
    change (b : A) ∈ W ⊔ K
    rw [← hcoe]
    exact
      (W ⊔ K).mul_mem
        ((show K ≤ W ⊔ K from le_sup_right) hnK)
        ((show W ≤ W ⊔ K from le_sup_left) hvW)
  · apply sup_le
    · rintro x ⟨v, hvL, rfl⟩
      let b : B := j v
      have hbH : b ∈ H := by
        change
          QuotientGroup.mk' N b ∈
            (P : Subgroup (B ⧸ N))
        rw [← he v]
        change
          e (QuotientGroup.mk' M v) ∈
            (R : Subgroup (V ⧸ M)).map e.toMonoidHom
        exact
          Subgroup.mem_map_of_mem
            e.toMonoidHom hvL
      exact ⟨b, hbH, rfl⟩
    · intro k hk
      let b : B := ⟨k, (show K ≤ V ⊔ K from le_sup_right) hk⟩
      have hbN : b ∈ N :=
        hk
      have hbH : b ∈ H :=
        normal_le_quotientSubgroupPreimage
          N (P : Subgroup (B ⧸ N)) hbN
      exact ⟨b, hbH, rfl⟩

/-- Extension existence on a target restricted triple is extension
existence on the ambient image `V_r ≤ A`. -/
theorem okuyamaWajimaTarget_extendsToSylowPreimage_iff
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    {r : ℕ} [Fact r.Prime]
    (R : Sylow r
      (V ⧸
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant).normalSubgroup)) :
    CharacterTriple.ExtendsToQuotientSylowPreimage
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant) R ↔
      ∃ phi :
          IrreducibleCharacter
            (okuyamaWajimaTargetSylowPreimageImage
              K Q V hV hCV d theta hinvariant R),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion
            (coprimeFixedPoints_le_okuyamaWajimaTargetSylowPreimageImage
              K Q V hV hCV d theta hinvariant R))
          (d.characterEquiv theta).1 phi := by
  let C := coprimeFixedPoints K Q
  let T :=
    invariantOkuyamaWajimaTargetTriple
      K Q V hV hCV d theta hinvariant
  let M := T.normalSubgroup
  let L :=
    okuyamaWajimaTargetSylowPreimage
      K Q V hV hCV d theta hinvariant R
  let W :=
    okuyamaWajimaTargetSylowPreimageImage
      K Q V hV hCV d theta hinvariant R
  have hML : M ≤ L :=
    normal_le_quotientSubgroupPreimage
      M (R : Subgroup (V ⧸ M))
  have hCW : C ≤ W :=
    coprimeFixedPoints_le_okuyamaWajimaTargetSylowPreimageImage
      K Q V hV hCV d theta hinvariant R
  have hmap :=
    IrreducibleCharacter.exists_extensionAlong_map_subtype_iff
      C V hCV L hML hCW (d.characterEquiv theta).1
  have hinternal :=
    exists_extensionAlong_inclusion_iff_subgroupOf
      M L hML T.character
  change
    (∃ eta : IrreducibleCharacter L,
      IrreducibleCharacter.IsExtensionAlong
        (M.subgroupOf L).subtype
        (((d.characterEquiv theta).1.comap
          (Subgroup.subgroupOfEquivOfLe hCV)).comap
            (Subgroup.subgroupOfEquivOfLe hML))
        eta) ↔
      ∃ phi : IrreducibleCharacter W,
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion hCW)
          (d.characterEquiv theta).1 phi
  exact hinternal.symm.trans hmap.symm

/-- Extension existence on the corresponding source restricted triple is
extension existence on `K V_r` in ambient subgroup coordinates. -/
theorem okuyamaWajimaSource_extendsToSylowPreimage_iff
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    {r : ℕ} [Fact r.Prime]
    (R : Sylow r
      (V ⧸
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant).normalSubgroup)) :
    letI :
        ((coprimeFixedPoints K Q).subgroupOf V).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (hV.trans
          (normalizer_le_normalizer_inf_centralizer K Q))
    let e :=
      okuyamaWajimaQuotientEquiv
        K Q hQ hK V hV hCV
    CharacterTriple.ExtendsToQuotientSylowPreimage
        (invariantOkuyamaWajimaSourceTriple
          K Q V theta hinvariant)
          (R.mapSurjective
            (f := e.toMonoidHom) e.surjective) ↔
      ∃ psi :
          IrreducibleCharacter
            (okuyamaWajimaTargetSylowPreimageImage
                K Q V hV hCV d theta hinvariant R ⊔ K :
              Subgroup A),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion le_sup_right)
          theta.1.1 psi := by
  let C := coprimeFixedPoints K Q
  let B := (V ⊔ K : Subgroup A)
  let S :=
    invariantOkuyamaWajimaSourceTriple
      K Q V theta hinvariant
  let T :=
    invariantOkuyamaWajimaTargetTriple
      K Q V hV hCV d theta hinvariant
  let M := T.normalSubgroup
  let N := S.normalSubgroup
  let e :
      V ⧸ M ≃* B ⧸ N :=
    okuyamaWajimaQuotientEquiv
      K Q hQ hK V hV hCV
  let P : Sylow r (B ⧸ N) :=
    R.mapSurjective
      (f := e.toMonoidHom) e.surjective
  let H :=
    okuyamaWajimaSourceSylowPreimage
      K Q V hQ hK hV hCV d theta hinvariant R
  let W :=
    okuyamaWajimaTargetSylowPreimageImage
      K Q V hV hCV d theta hinvariant R
  have hNH : N ≤ H :=
    normal_le_quotientSubgroupPreimage
      N (P : Subgroup (B ⧸ N))
  have hKMap : K ≤ H.map B.subtype := by
    intro k hk
    let b : B :=
      ⟨k, (show K ≤ V ⊔ K from le_sup_right) hk⟩
    have hbN : b ∈ N :=
      hk
    exact
      ⟨b,
        normal_le_quotientSubgroupPreimage
          N (P : Subgroup (B ⧸ N)) hbN,
        rfl⟩
  have hmap :=
    IrreducibleCharacter.exists_extensionAlong_map_subtype_iff
      K B le_sup_right H hNH hKMap theta.1.1
  have hinternal :=
    exists_extensionAlong_inclusion_iff_subgroupOf
      N H hNH S.character
  have himage :
      H.map B.subtype = W ⊔ K :=
    okuyamaWajimaSourceSylowPreimage_map_subtype
      K Q V hQ hK hV hCV d theta hinvariant R
  have hcoord :=
    IrreducibleCharacter.exists_extensionAlong_inclusion_congr
      K (H.map B.subtype) (W ⊔ K)
      hKMap le_sup_right himage theta.1.1
  change
    (∃ eta : IrreducibleCharacter H,
      IrreducibleCharacter.IsExtensionAlong
        (N.subgroupOf H).subtype
        ((theta.1.1.comap
          (Subgroup.subgroupOfEquivOfLe le_sup_right)).comap
            (Subgroup.subgroupOfEquivOfLe hNH))
        eta) ↔
      ∃ psi : IrreducibleCharacter (W ⊔ K : Subgroup A),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion le_sup_right)
          theta.1.1 psi
  exact hinternal.symm.trans (hmap.symm.trans hcoord)

/-- The exact local semantic input needed after passing to quotient Sylow
preimages.  Unlike a uniform mixed-prime hypothesis, this proposition asks
for the OW extension conclusion only on the `r ≠ p` groups `V_r`. -/
def InvariantOkuyamaWajimaPrimeAwaySylowPreimageInput
    (_hQ : IsPGroup p Q)
    (_hK : IsPPrimeGroup p K)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  ∀ (r : ℕ) (hr : r.Prime),
    r ≠ p →
      letI : Fact r.Prime := ⟨hr⟩
      ∀ R : Sylow r
          (V ⧸
            (invariantOkuyamaWajimaTargetTriple
              K Q V hV hCV d theta hinvariant).normalSubgroup),
        okuyamaWajimaExtensionConclusion
          K Q
          (okuyamaWajimaTargetSylowPreimageImage
            K Q V hV hCV d theta hinvariant R)
          (coprimeFixedPoints_le_okuyamaWajimaTargetSylowPreimageImage
            K Q V hV hCV d theta hinvariant R)
          d theta

/-- Full coordinate adapter from OW conclusions on the `r ≠ p` quotient
Sylow preimages to the current prime-away semantic comparison. -/
theorem invariantOkuyamaWajimaPrimeAwayExtensionComparison_of_sylowPreimages
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hloc :
      InvariantOkuyamaWajimaPrimeAwaySylowPreimageInput
        K Q V hQ hK hV hCV d theta hinvariant) :
    InvariantOkuyamaWajimaPrimeAwayExtensionComparison
      K Q V hQ hK hV hCV d theta hinvariant := by
  rw [InvariantOkuyamaWajimaPrimeAwayExtensionComparison]
  intro r hr hrp
  letI : Fact r.Prime := ⟨hr⟩
  intro R
  have hsource :=
    okuyamaWajimaSource_extendsToSylowPreimage_iff
      K Q V hQ hK hV hCV d theta hinvariant R
  have htarget :=
    okuyamaWajimaTarget_extendsToSylowPreimage_iff
      K Q V hV hCV d theta hinvariant R
  exact
    hsource.trans
      ((hloc r hr hrp R).trans htarget.symm)

omit [Fact p.Prime] in
/-- If `W/C_K(Q)` is abelian, then the quotient of the local product
`W(KQ)` by `KQ` is abelian.  This is the exact abelian-quotient premise
in the printed OW theorem, proved through the second-isomorphism
equivalence rather than by a mixed-prime assertion. -/
theorem commutator_primeAwayLocalProduct_le_normalProduct
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hKQ : (K ⊔ Q).Normal)
    (W : Subgroup A)
    (hW : IsPPrimeGroup p W)
    (hWN : W ≤ Subgroup.normalizer (Q : Set A))
    (hCW : coprimeFixedPoints K Q ≤ W)
    (hcommW :
      _root_.commutator W ≤
        (coprimeFixedPoints K Q).subgroupOf W) :
    _root_.commutator (W ⊔ (K ⊔ Q) : Subgroup A) ≤
      (K ⊔ Q).subgroupOf (W ⊔ (K ⊔ Q)) := by
  let C := coprimeFixedPoints K Q
  let H := K ⊔ Q
  let G := W ⊔ H
  let M := C.subgroupOf W
  let N := H.subgroupOf G
  letI : H.Normal := hKQ
  letI : N.Normal := hKQ.subgroupOf G
  letI : M.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hWN.trans
        (normalizer_le_normalizer_inf_centralizer K Q))
  have hWH : W ⊓ H = C :=
    pPrimeNormalizer_inf_normalProduct_eq_fixedPoints
      K Q W hQ hK hW hWN hCW
  have hEq : M = H.subgroupOf W := by
    rw [← Subgroup.inf_subgroupOf_right H W,
      inf_comm, hWH]
  let e :
      W ⧸ M ≃* G ⧸ N :=
    (QuotientGroup.quotientMulEquivOfEq hEq).trans
      (QuotientGroup.quotientInfEquivProdNormalQuotient W H)
  have hsource :
      IsMulCommutative (W ⧸ M) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      hcommW
  have htarget :
      IsMulCommutative (G ⧸ N) :=
    Function.Surjective.mul_comm
      (f := e.toMonoidHom) e.surjective hsource
  exact
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      htarget

omit [Fact p.Prime] in
/-- The preceding abelian-quotient fact in the `K(QW)` parenthesization
used by the printed theorem. -/
theorem commutator_okuyamaWajimaPrimeLocalProduct_le
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hKQ : (K ⊔ Q).Normal)
    (W : Subgroup A)
    (hW : IsPPrimeGroup p W)
    (hWN : W ≤ Subgroup.normalizer (Q : Set A))
    (hCW : coprimeFixedPoints K Q ≤ W)
    (hcommW :
      _root_.commutator W ≤
        (coprimeFixedPoints K Q).subgroupOf W) :
    _root_.commutator (K ⊔ (Q ⊔ W) : Subgroup A) ≤
      (K ⊔ Q).subgroupOf (K ⊔ (Q ⊔ W)) := by
  have hG :
      K ⊔ (Q ⊔ W) = W ⊔ (K ⊔ Q) := by
    ac_rfl
  rw [hG]
  exact
    commutator_primeAwayLocalProduct_le_normalProduct
      K Q hQ hK hKQ W hW hWN hCW hcommW

/-- In the prime-away local product, the normalizer of the canonical
Sylow copy of `Q` is the internal copy of `QW`. -/
theorem normalizer_okuyamaWajimaSylowInPrimeAwayLocalProduct_eq
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (W : Subgroup A)
    (hW : IsPPrimeGroup p W)
    (hWN : W ≤ Subgroup.normalizer (Q : Set A))
    (hCW : coprimeFixedPoints K Q ≤ W) :
    Subgroup.normalizer
        ((okuyamaWajimaSylowInPrimeAwayLocalProduct
          K Q W hQ hK hW hWN :
          Subgroup (K ⊔ (Q ⊔ W) : Subgroup A)) :
          Set (K ⊔ (Q ⊔ W) : Subgroup A)) =
      (Q ⊔ W).subgroupOf (K ⊔ (Q ⊔ W)) := by
  let G := K ⊔ (Q ⊔ W)
  have hQG : Q ≤ G :=
    (show Q ≤ Q ⊔ W from le_sup_left).trans
      (show Q ⊔ W ≤ K ⊔ (Q ⊔ W) from le_sup_right)
  rw [coe_okuyamaWajimaSylowInPrimeAwayLocalProduct,
    ← Subgroup.subgroupOf_normalizer_eq hQG]
  ext x
  change
    (x : A) ∈ Subgroup.normalizer (Q : Set A) ↔
      (x : A) ∈ Q ⊔ W
  rw [← normalizer_inf_pPrimeKernel_sup_normalizing_eq
    K Q W hQ hK hWN hCW]
  change
    (x : A) ∈ Subgroup.normalizer (Q : Set A) ↔
      (x : A) ∈ Subgroup.normalizer (Q : Set A) ∧
        (x : A) ∈ G
  exact ⟨fun hx => ⟨hx, x.2⟩, fun hx => hx.1⟩

/-- The exact group-theoretic scope of the printed OW theorem on one
prime-away local product. -/
structure InvariantOkuyamaWajimaPrintedLocalScope
    (W : Subgroup A) where
  sylow : Sylow p (K ⊔ (Q ⊔ W) : Subgroup A)
  sylow_eq :
    (sylow : Subgroup (K ⊔ (Q ⊔ W) : Subgroup A)) =
      Q.subgroupOf (K ⊔ (Q ⊔ W))
  normalizer_eq :
    Subgroup.normalizer
        ((sylow : Subgroup (K ⊔ (Q ⊔ W) : Subgroup A)) :
          Set (K ⊔ (Q ⊔ W) : Subgroup A)) =
      (Q ⊔ W).subgroupOf (K ⊔ (Q ⊔ W))
  product_eq_top :
    K.subgroupOf (K ⊔ (Q ⊔ W)) ⊔
        Subgroup.normalizer
          ((sylow : Subgroup (K ⊔ (Q ⊔ W) : Subgroup A)) :
            Set (K ⊔ (Q ⊔ W) : Subgroup A)) =
      ⊤
  normalizer_inf_kernel_eq :
    Subgroup.normalizer
          ((sylow : Subgroup (K ⊔ (Q ⊔ W) : Subgroup A)) :
            Set (K ⊔ (Q ⊔ W) : Subgroup A)) ⊓
        K.subgroupOf (K ⊔ (Q ⊔ W)) =
      (coprimeFixedPoints K Q).subgroupOf
        (K ⊔ (Q ⊔ W))
  quotient_abelian :
    _root_.commutator (K ⊔ (Q ⊔ W) : Subgroup A) ≤
      (K ⊔ Q).subgroupOf (K ⊔ (Q ⊔ W))

/-- The green prime-local subgroup lemmas assemble all hypotheses in the
exact printed scope. -/
def invariantOkuyamaWajimaPrintedLocalScope
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hKQ : (K ⊔ Q).Normal)
    (W : Subgroup A)
    (hW : IsPPrimeGroup p W)
    (hWN : W ≤ Subgroup.normalizer (Q : Set A))
    (hCW : coprimeFixedPoints K Q ≤ W)
    (hcommW :
      _root_.commutator W ≤
        (coprimeFixedPoints K Q).subgroupOf W) :
    InvariantOkuyamaWajimaPrintedLocalScope (p := p) K Q W where
  sylow :=
    okuyamaWajimaSylowInPrimeAwayLocalProduct
      K Q W hQ hK hW hWN
  sylow_eq :=
    coe_okuyamaWajimaSylowInPrimeAwayLocalProduct
      K Q W hQ hK hW hWN
  normalizer_eq :=
    normalizer_okuyamaWajimaSylowInPrimeAwayLocalProduct_eq
      K Q hQ hK W hW hWN hCW
  product_eq_top := by
    rw [normalizer_okuyamaWajimaSylowInPrimeAwayLocalProduct_eq
      K Q hQ hK W hW hWN hCW,
      ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self]
  normalizer_inf_kernel_eq := by
    rw [normalizer_okuyamaWajimaSylowInPrimeAwayLocalProduct_eq
      K Q hQ hK W hW hWN hCW]
    ext x
    have hU :
        Q ⊔ W ≤ Subgroup.normalizer (Q : Set A) :=
      sup_le Subgroup.le_normalizer hWN
    have hCU :
        coprimeFixedPoints K Q ≤ Q ⊔ W :=
      hCW.trans le_sup_right
    have hinter :=
      pPrimeKernel_inf_eq_fixedPoints
        K Q hQ hK (Q ⊔ W) hU hCU
    change
      (x : A) ∈ (Q ⊔ W) ⊓ K ↔
        (x : A) ∈ coprimeFixedPoints K Q
    rw [inf_comm, hinter]
  quotient_abelian :=
    commutator_okuyamaWajimaPrimeLocalProduct_le
      K Q hQ hK hKQ W hW hWN hCW hcommW

/-- An abelian quotient `V/C_K(Q)` restricts to an abelian quotient on
every target quotient Sylow preimage. -/
theorem commutator_okuyamaWajimaTargetSylowPreimageImage_le
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hcommV :
      _root_.commutator V ≤
        (coprimeFixedPoints K Q).subgroupOf V)
    {r : ℕ} [Fact r.Prime]
    (R : Sylow r
      (V ⧸
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant).normalSubgroup)) :
    _root_.commutator
        (okuyamaWajimaTargetSylowPreimageImage
          K Q V hV hCV d theta hinvariant R) ≤
      (coprimeFixedPoints K Q).subgroupOf
        (okuyamaWajimaTargetSylowPreimageImage
          K Q V hV hCV d theta hinvariant R) := by
  let C := coprimeFixedPoints K Q
  let T :=
    invariantOkuyamaWajimaTargetTriple
      K Q V hV hCV d theta hinvariant
  let M := T.normalSubgroup
  let L :=
    okuyamaWajimaTargetSylowPreimage
      K Q V hV hCV d theta hinvariant R
  have hML : M ≤ L :=
    normal_le_quotientSubgroupPreimage
      M (R : Subgroup (V ⧸ M))
  have hcommL :
      _root_.commutator L ≤ M.subgroupOf L := by
    intro x hx
    have hxmap :
        (x : V) ∈
          (_root_.commutator L).map L.subtype :=
      Subgroup.mem_map_of_mem L.subtype hx
    rw [Subgroup.map_subtype_commutator] at hxmap
    have hxV :
        (x : V) ∈ _root_.commutator V :=
      (Subgroup.commutator_mono le_top le_top) hxmap
    exact hcommV hxV
  exact
    IrreducibleCharacter.commutator_map_subtype_le
      C V L hcommL

/-- Away from `p`, a target quotient Sylow preimage is itself a
`p'`-group. -/
theorem isPPrimeGroup_okuyamaWajimaTargetSylowPreimageImage_of_ne
    (hK : IsPPrimeGroup p K)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    {r : ℕ} [Fact r.Prime]
    (hrp : r ≠ p)
    (R : Sylow r
      (V ⧸
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant).normalSubgroup)) :
    IsPPrimeGroup p
      (okuyamaWajimaTargetSylowPreimageImage
        K Q V hV hCV d theta hinvariant R) := by
  let T :=
    invariantOkuyamaWajimaTargetTriple
      K Q V hV hCV d theta hinvariant
  let L :=
    okuyamaWajimaTargetSylowPreimage
      K Q V hV hCV d theta hinvariant R
  let W :=
    okuyamaWajimaTargetSylowPreimageImage
      K Q V hV hCV d theta hinvariant R
  have hTK :
      IsPPrimeGroup p T.normalSubgroup :=
    (invariantOkuyamaWajima_internalKernels_isPPrime
      K Q V hK hV hCV d theta hinvariant).2
  have hL : IsPPrimeGroup p L :=
    isPPrimeGroup_quotientSubgroupPreimage_sylow_of_ne
      hrp.symm T.normalSubgroup hTK R
  exact
    hL.of_equiv
      (L.equivMapOfInjective
        V.subtype V.subtype_injective)

/-- Source-faithful input for Okuyama--Wajima, Theorem 2(3), restricted
to the only instances used here.

For `W` a `p'` subgroup of `N_A(Q)` containing `C_K(Q)`, the elementary
lemmas in `GroupTheory.OkuyamaWajimaPrimeLocal` show that

* `Q` is Sylow in `K Q W`;
* its normalizer in that local group is `Q W`;
* the local group is the product of `K` with that normalizer; and
* the intersection of `K` with the normalizer is `C_K(Q)`.

The supplied `InvariantOkuyamaWajimaPrintedLocalScope` records these four
facts and that `(K Q W)/(K Q)` is abelian.  Thus the conclusion is
precisely the ordinary extension clause of the printed theorem, not an
arbitrary-external-action strengthening. -/
def InvariantOkuyamaWajimaPrintedExtensionTheoremInput
    (_hQ : IsPGroup p Q)
    (_hK : IsPPrimeGroup p K)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (_hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  ∀ (W : Subgroup A)
      (hCW : coprimeFixedPoints K Q ≤ W),
    InvariantOkuyamaWajimaPrintedLocalScope (p := p) K Q W →
      okuyamaWajimaExtensionConclusion
        K Q (Q ⊔ W)
        (hCW.trans le_sup_right)
        d theta

/-- The exact remaining Navarro step on a prime-away local piece:
adjoining the normal Sylow `p`-subgroup `Q` does not change extension
existence on either side.

This is deliberately separate from the printed OW input.  Its intended
proof is Navarro Theorem 5.10 plus the automatic coprime extension at the
`p`-local preimage (Corollary 6.2). -/
def InvariantOkuyamaWajimaPrimeAwayQDeletionInput
    (_hQ : IsPGroup p Q)
    (_hK : IsPPrimeGroup p K)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  ∀ (r : ℕ) (hr : r.Prime),
    r ≠ p →
      letI : Fact r.Prime := ⟨hr⟩
      ∀ R : Sylow r
          (V ⧸
            (invariantOkuyamaWajimaTargetTriple
              K Q V hV hCV d theta hinvariant).normalSubgroup),
        let W :=
          okuyamaWajimaTargetSylowPreimageImage
            K Q V hV hCV d theta hinvariant R
        let hCW :=
          coprimeFixedPoints_le_okuyamaWajimaTargetSylowPreimageImage
            K Q V hV hCV d theta hinvariant R
        ((∃ psi : IrreducibleCharacter (W ⊔ K : Subgroup A),
            IrreducibleCharacter.IsExtensionAlong
              (Subgroup.inclusion le_sup_right)
              theta.1.1 psi) ↔
          ∃ psi :
              IrreducibleCharacter ((Q ⊔ W) ⊔ K : Subgroup A),
            IrreducibleCharacter.IsExtensionAlong
              (Subgroup.inclusion le_sup_right)
              theta.1.1 psi) ∧
        ((∃ phi : IrreducibleCharacter W,
            IrreducibleCharacter.IsExtensionAlong
              (Subgroup.inclusion hCW)
              (d.characterEquiv theta).1 phi) ↔
          ∃ phi : IrreducibleCharacter (Q ⊔ W : Subgroup A),
            IrreducibleCharacter.IsExtensionAlong
              (Subgroup.inclusion (hCW.trans le_sup_right))
              (d.characterEquiv theta).1 phi)

/-- The printed OW theorem on `K Q V_r`, together with the Navarro
`Q`-deletion step, supplies every local semantic comparison required by
the quotient Sylow-preimage adapter. -/
theorem invariantOkuyamaWajimaPrimeAwaySylowPreimageInput_of_printed
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hKQ : (K ⊔ Q).Normal)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hcommV :
      _root_.commutator V ≤
        (coprimeFixedPoints K Q).subgroupOf V)
    (hprinted :
      InvariantOkuyamaWajimaPrintedExtensionTheoremInput
        K Q hQ hK d theta hinvariant)
    (hdelete :
      InvariantOkuyamaWajimaPrimeAwayQDeletionInput
        K Q V hQ hK hV hCV d theta hinvariant) :
    InvariantOkuyamaWajimaPrimeAwaySylowPreimageInput
      K Q V hQ hK hV hCV d theta hinvariant := by
  intro r hr hrp
  letI : Fact r.Prime := ⟨hr⟩
  intro R
  let W :=
    okuyamaWajimaTargetSylowPreimageImage
      K Q V hV hCV d theta hinvariant R
  have hCW : coprimeFixedPoints K Q ≤ W :=
    coprimeFixedPoints_le_okuyamaWajimaTargetSylowPreimageImage
      K Q V hV hCV d theta hinvariant R
  have hWN : W ≤ Subgroup.normalizer (Q : Set A) :=
    okuyamaWajimaTargetSylowPreimageImage_le_normalizer
      K Q V hV hCV d theta hinvariant R
  have hW : IsPPrimeGroup p W :=
    isPPrimeGroup_okuyamaWajimaTargetSylowPreimageImage_of_ne
      K Q V hK hV hCV d theta hinvariant hrp R
  have hcommW :
      _root_.commutator W ≤
        (coprimeFixedPoints K Q).subgroupOf W :=
    commutator_okuyamaWajimaTargetSylowPreimageImage_le
      K Q V hV hCV d theta hinvariant hcommV R
  let hscope :
      InvariantOkuyamaWajimaPrintedLocalScope (p := p) K Q W :=
    invariantOkuyamaWajimaPrintedLocalScope
      K Q hQ hK hKQ W hW hWN hCW hcommW
  have how :=
    hprinted W hCW hscope
  obtain ⟨hsource, htarget⟩ :=
    hdelete r hr hrp R
  exact hsource.trans (how.trans htarget.symm)

/-- Source-correct discharge of the existing named prime-away original
conclusion.  The only unproved inputs are now the printed theorem itself
and the explicitly separated Navarro `Q`-deletion seam. -/
theorem invariantOkuyamaWajimaPrimeAwayOriginalConclusion_of_printed
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hprinted :
      InvariantOkuyamaWajimaPrintedExtensionTheoremInput
        K Q hQ hK d theta hinvariant)
    (hdelete :
      InvariantOkuyamaWajimaPrimeAwayQDeletionInput
        K Q V hQ hK hV hCV d theta hinvariant) :
    InvariantOkuyamaWajimaPrimeAwayOriginalConclusion
      K Q V hQ hK hV hCV d theta hinvariant := by
  intro hKQ hcommV
  apply
    invariantOkuyamaWajimaPrimeAwayExtensionComparison_of_sylowPreimages
      K Q V hQ hK hV hCV d theta hinvariant
  exact
    invariantOkuyamaWajimaPrimeAwaySylowPreimageInput_of_printed
      K Q V hQ hK hKQ hV hCV d theta hinvariant hcommV
      hprinted hdelete

section Uniform

variable (U : Subgroup A)

/-- The Navarro `Q`-deletion seam uniformly over the intermediate
subgroups used by the good-element argument. -/
def UniformInvariantOkuyamaWajimaPrimeAwayQDeletionInput
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  ∀ (V : Subgroup A)
      (hCV : coprimeFixedPoints K Q ≤ V)
      (hVU : V ≤ U),
    InvariantOkuyamaWajimaPrimeAwayQDeletionInput
      K Q V hQ hK (hVU.trans hU) hCV d theta hinvariant

/-- The exact printed theorem plus the uniform Navarro deletion seam
discharge the existing uniform prime-away original input. -/
theorem uniformInvariantOkuyamaWajimaPrimeAwayOriginalInput_of_printed
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hprinted :
      InvariantOkuyamaWajimaPrintedExtensionTheoremInput
        K Q hQ hK d theta hinvariant)
    (hdelete :
      UniformInvariantOkuyamaWajimaPrimeAwayQDeletionInput
        K Q U hQ hK hU d theta hinvariant) :
    UniformInvariantOkuyamaWajimaPrimeAwayOriginalInput
      K Q U hQ hK hU d theta hinvariant := by
  intro V hCV hVU
  exact
    invariantOkuyamaWajimaPrimeAwayOriginalConclusion_of_printed
      K Q V hQ hK (hVU.trans hU) hCV d theta hinvariant
      hprinted (hdelete V hCV hVU)

end Uniform

end McKayConjecture
