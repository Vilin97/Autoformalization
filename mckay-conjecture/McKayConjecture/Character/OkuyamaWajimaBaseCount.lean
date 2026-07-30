/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.NormalProductRestriction
import McKayConjecture.Character.OkuyamaWajimaGoodElement
import McKayConjecture.Character.OverAlongTransport
import McKayConjecture.GroupTheory.OkuyamaWajimaComplement

/-!
# The Okuyama--Wajima base-extension count

Let `K ◁ Γ` be a normal `p′`-subgroup, let `S` be a Sylow `p`-subgroup,
and suppose `K ⊔ S` is normal in `Γ`.  This file packages the two
normal-product restriction steps around the ordinary Okuyama--Wajima count.

The only character-theoretic input not currently supplied by the repository
is an ambient-invariant choice of the two coprime extensions:

* an extension of `θ` from `K` to `K ⊔ S`, invariant under `Γ`;
* an extension of the Glauberman correspondent from `C_K(S)` to
  `(K ⊔ S) ∩ N_Γ(S)`, invariant under `N_Γ(S)`.

The structure `OkuyamaWajimaBaseExtensionData` states exactly that missing
input.  Given it and the current semantic uniform OW input, the final
cardinality equality has no chosen complement in its result type.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open CliffordCorrespondence
open GroupTheory

/-! ### Ordinary fibre transport through group equivalences -/

namespace CliffordCorrespondence

variable {G G' H H' : Type}
variable [Finite G] [Finite G'] [Finite H] [Finite H']
variable [Group G] [Group G'] [Group H] [Group H']

/-- Simultaneous relabelling of a commuting square transports an ordinary
lying-over fibre.  This is the ordinary analogue of the existing
prime-to-`p` transport equivalence. -/
def irreducibleCharactersOverAlongComapEquiv
    (eG : G' ≃* G)
    (eH : H' ≃* H)
    (φ : H →* G)
    (φ' : H' →* G')
    (hcomm :
      eG.toMonoidHom.comp φ' =
        φ.comp eH.toMonoidHom)
    (η : IrreducibleCharacter H) :
    IrreducibleCharactersOverAlong φ η ≃
      IrreducibleCharactersOverAlong
        φ' (η.comap eH) where
  toFun χ :=
    ⟨χ.1.comap eG,
      (liesOverAlong_comap_equiv_iff
        eG eH φ φ' hcomm η χ.1).2 χ.2⟩
  invFun χ :=
    ⟨χ.1.comap eG.symm, by
      apply
        (liesOverAlong_comap_equiv_iff
          eG eH φ φ' hcomm η
            (χ.1.comap eG.symm)).1
      simpa using χ.2⟩
  left_inv χ := by
    apply Subtype.ext
    simp
  right_inv χ := by
    apply Subtype.ext
    simp

end CliffordCorrespondence

/-! ### The exact canonical-extension input -/

variable {Γ : Type} [Group Γ] [Finite Γ]
variable {p : ℕ} [Fact p.Prime]

/-- The Glauberman correspondent, transported to the internal copy of
`C_K(S)` inside `N_Γ(S)`. -/
def okuyamaWajimaInternalFixedPointCharacter
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p) :
    IrreducibleCharacter
      (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ)) :=
  (d.characterEquiv θ).1.comap
    (Subgroup.subgroupOfEquivOfLe
      (show
        coprimeFixedPoints K (S : Subgroup Γ) ≤
          Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) from
        inf_le_right.trans
          (Subgroup.centralizer_le_normalizer
            ((S : Subgroup Γ) : Set Γ))))

/-- The exact missing canonical-extension and invariance package for the
base-count argument.

Ordinary normal-Hall extension existence supplies extensions with these
source characters, but the current API does not prove that a choice can be
made invariant under the indicated larger ambient groups. -/
structure OkuyamaWajimaBaseExtensionData
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p) where
  /-- The selected extension of `θ` to `K ⊔ S`. -/
  sourceExtension :
    IrreducibleCharacter (K ⊔ (S : Subgroup Γ) : Subgroup Γ)
  /-- The source selection really extends `θ`. -/
  source_isExtension :
    IrreducibleCharacter.IsExtensionAlong
      (Subgroup.inclusion le_sup_left)
      θ.1.1 sourceExtension
  /-- The source selection is invariant under `Γ`. -/
  source_invariant :
    ∀ (g : Γ)
      (x : (K ⊔ (S : Subgroup Γ) : Subgroup Γ)),
      sourceExtension.values
          (conjugateNormalElement
            (K ⊔ (S : Subgroup Γ) : Subgroup Γ)
            hKS g x) =
        sourceExtension.values x
  /-- The selected extension of the internal Glauberman correspondent to
  the internal normal product. -/
  targetExtension :
    IrreducibleCharacter
      (okuyamaWajimaInternalNormalProduct K (S : Subgroup Γ))
  /-- The target selection really extends the Glauberman correspondent. -/
  target_isExtension :
    IrreducibleCharacter.IsExtensionAlong
      (Subgroup.inclusion
        (internalFixedPoints_le_internalNormalProduct
          K (S : Subgroup Γ)))
      (okuyamaWajimaInternalFixedPointCharacter S K d θ)
      targetExtension
  /-- The target selection is invariant under `N_Γ(S)`. -/
  target_invariant :
    ∀ (g :
        Subgroup.normalizer ((S : Subgroup Γ) : Set Γ))
      (x : okuyamaWajimaInternalNormalProduct K (S : Subgroup Γ)),
      targetExtension.values
          (conjugateNormalElement
            (okuyamaWajimaInternalNormalProduct
              K (S : Subgroup Γ))
            (internalNormalProduct_normal
              K (S : Subgroup Γ) hKS)
            g x) =
        targetExtension.values x

/-- Named milestone for the genuinely missing invariant canonical-extension
theorem. -/
def OkuyamaWajimaCanonicalBaseExtensionHypothesis
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p) : Prop :=
  Nonempty (OkuyamaWajimaBaseExtensionData S K hKS d θ)

/-- A canonical classical choice from the named base-extension hypothesis. -/
def okuyamaWajimaCanonicalBaseExtensionData
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (hcanonical :
      OkuyamaWajimaCanonicalBaseExtensionHypothesis
        S K hKS d θ) :
    OkuyamaWajimaBaseExtensionData S K hKS d θ :=
  Classical.choice hcanonical

/-! ### Normal-product coordinates -/

/-- The source canonical-extension triple
`(Γ, K ⊔ S, sourceExtension)`. -/
def okuyamaWajimaSourceBaseTriple
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (c : OkuyamaWajimaBaseExtensionData S K hKS d θ) :
    CharacterTriple Γ where
  normalSubgroup := K ⊔ (S : Subgroup Γ)
  isNormal := hKS
  character := c.sourceExtension
  isInvariant := c.source_invariant

/-- The target canonical-extension triple inside `N_Γ(S)`. -/
def okuyamaWajimaTargetBaseTriple
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (c : OkuyamaWajimaBaseExtensionData S K hKS d θ) :
    CharacterTriple
      (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ)) where
  normalSubgroup :=
    okuyamaWajimaInternalNormalProduct K (S : Subgroup Γ)
  isNormal :=
    internalNormalProduct_normal K (S : Subgroup Γ) hKS
  character := c.targetExtension
  isInvariant := c.target_invariant

/-- The intersection in the source normal-product restriction, relabelled
as the original kernel `K`. -/
def okuyamaWajimaSourceIntersectionEquivKernel
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal) :
    (K ⊔ (S : Subgroup Γ)).subgroupOf
          (okuyamaWajimaAmbientComplement S K hK hKS ⊔ K) ≃*
      K :=
  (MulEquiv.subgroupCongr
      (normalProduct_subgroupOf_ambientComplement_sup_kernel_eq
        S K hK hKS)).trans
    (Subgroup.subgroupOfEquivOfLe le_sup_right)

@[simp]
theorem coe_okuyamaWajimaSourceIntersectionEquivKernel
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (x :
      (K ⊔ (S : Subgroup Γ)).subgroupOf
        (okuyamaWajimaAmbientComplement S K hK hKS ⊔ K)) :
    (okuyamaWajimaSourceIntersectionEquivKernel
        S K hK hKS x : Γ) =
      (x :
        (okuyamaWajimaAmbientComplement S K hK hKS ⊔ K :
          Subgroup Γ)) :=
  rfl

/-- The source character on the internal intersection. -/
def okuyamaWajimaSourceIntersectionCharacter
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p) :
    IrreducibleCharacter
      ((K ⊔ (S : Subgroup Γ)).subgroupOf
        (okuyamaWajimaAmbientComplement S K hK hKS ⊔ K)) :=
  θ.1.1.comap
    (okuyamaWajimaSourceIntersectionEquivKernel
      S K hK hKS)

/-- The intersection in the target normal-product restriction, relabelled
as the internal fixed-point subgroup. -/
def okuyamaWajimaTargetIntersectionEquivFixedPoints
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal) :
    (okuyamaWajimaInternalNormalProduct
        K (S : Subgroup Γ)).subgroupOf
          (okuyamaWajimaComplement S K hK hKS) ≃*
      okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ) :=
  (MulEquiv.subgroupCongr
      (internalNormalProduct_subgroupOf_complement_eq_fixedPoints_subgroupOf
        S K hK hKS)).trans
    (Subgroup.subgroupOfEquivOfLe
      (internalFixedPoints_le_okuyamaWajimaComplement
        S K hK hKS))

@[simp]
theorem coe_okuyamaWajimaTargetIntersectionEquivFixedPoints
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (x :
      (okuyamaWajimaInternalNormalProduct
        K (S : Subgroup Γ)).subgroupOf
          (okuyamaWajimaComplement S K hK hKS)) :
    ((okuyamaWajimaTargetIntersectionEquivFixedPoints
        S K hK hKS x :
      okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ)) :
        Subgroup.normalizer ((S : Subgroup Γ) : Set Γ)) =
      (x : okuyamaWajimaComplement S K hK hKS) :=
  rfl

/-- The target character on the internal intersection. -/
def okuyamaWajimaTargetIntersectionCharacter
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p) :
    IrreducibleCharacter
      ((okuyamaWajimaInternalNormalProduct
        K (S : Subgroup Γ)).subgroupOf
          (okuyamaWajimaComplement S K hK hKS)) :=
  (okuyamaWajimaInternalFixedPointCharacter S K d θ).comap
    (okuyamaWajimaTargetIntersectionEquivFixedPoints
      S K hK hKS)

/-- The selected source extension restricts to the source intersection
character. -/
theorem okuyamaWajimaSourceExtension_isExtensionToIntersection
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (c : OkuyamaWajimaBaseExtensionData S K hKS d θ) :
    IrreducibleCharacter.IsExtensionAlong
      (normalIntersectionInclusion
        (K ⊔ (S : Subgroup Γ))
        (okuyamaWajimaAmbientComplement S K hK hKS ⊔ K))
      (okuyamaWajimaSourceIntersectionCharacter
        S K hK hKS θ)
      c.sourceExtension := by
  intro x
  change
    c.sourceExtension.values
        (normalIntersectionInclusion
          (K ⊔ (S : Subgroup Γ))
          (okuyamaWajimaAmbientComplement S K hK hKS ⊔ K) x) =
      θ.1.1.values
        (okuyamaWajimaSourceIntersectionEquivKernel
          S K hK hKS x)
  convert c.source_isExtension
    (okuyamaWajimaSourceIntersectionEquivKernel
      S K hK hKS x) using 1
  apply congrArg c.sourceExtension.values
  apply Subtype.ext
  rfl

/-- The selected target extension restricts to the target intersection
character. -/
theorem okuyamaWajimaTargetExtension_isExtensionToIntersection
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (c : OkuyamaWajimaBaseExtensionData S K hKS d θ) :
    IrreducibleCharacter.IsExtensionAlong
      (normalIntersectionInclusion
        (okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ))
        (okuyamaWajimaComplement S K hK hKS))
      (okuyamaWajimaTargetIntersectionCharacter
        S K hK hKS d θ)
      c.targetExtension := by
  intro x
  change
    c.targetExtension.values
        (normalIntersectionInclusion
          (okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ))
          (okuyamaWajimaComplement S K hK hKS) x) =
      (okuyamaWajimaInternalFixedPointCharacter
        S K d θ).values
          (okuyamaWajimaTargetIntersectionEquivFixedPoints
            S K hK hKS x)
  convert c.target_isExtension
    (okuyamaWajimaTargetIntersectionEquivFixedPoints
      S K hK hKS x) using 1
  apply congrArg c.targetExtension.values
  apply Subtype.ext
  rfl

/-! ### The two normal-product restriction equivalences -/

/-- Restriction from `Γ` to `U ⊔ K` above the selected source extension. -/
def okuyamaWajimaSourceNormalProductRestrictionEquiv
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (c : OkuyamaWajimaBaseExtensionData S K hKS d θ) :
    IrreducibleCharactersOverAlong
        (K ⊔ (S : Subgroup Γ) : Subgroup Γ).subtype
        c.sourceExtension ≃
      IrreducibleCharactersOverAlong
        ((K ⊔ (S : Subgroup Γ)).subgroupOf
          (okuyamaWajimaAmbientComplement S K hK hKS ⊔ K)).subtype
        (okuyamaWajimaSourceIntersectionCharacter
          S K hK hKS θ) :=
  restrictionOverEquiv_of_normal_sup_eq_top
    (okuyamaWajimaSourceBaseTriple S K hKS d θ c)
    (okuyamaWajimaAmbientComplement S K hK hKS ⊔ K)
    (okuyamaWajimaSourceIntersectionCharacter
      S K hK hKS θ)
    (okuyamaWajimaSourceExtension_isExtensionToIntersection
      S K hK hKS d θ c)
    (normalProduct_sup_ambientComplement_sup_kernel_eq_top
      S K hK hKS)

/-- Restriction from `N_Γ(S)` to the internal complement above the
selected target extension. -/
def okuyamaWajimaTargetNormalProductRestrictionEquiv
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (c : OkuyamaWajimaBaseExtensionData S K hKS d θ) :
    IrreducibleCharactersOverAlong
        (okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ)).subtype
        c.targetExtension ≃
      IrreducibleCharactersOverAlong
        ((okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ)).subgroupOf
            (okuyamaWajimaComplement S K hK hKS)).subtype
        (okuyamaWajimaTargetIntersectionCharacter
          S K hK hKS d θ) :=
  restrictionOverEquiv_of_normal_sup_eq_top
    (okuyamaWajimaTargetBaseTriple S K hKS d θ c)
    (okuyamaWajimaComplement S K hK hKS)
    (okuyamaWajimaTargetIntersectionCharacter
      S K hK hKS d θ)
    (okuyamaWajimaTargetExtension_isExtensionToIntersection
      S K hK hKS d θ c)
    (internalNormalProduct_sup_okuyamaWajimaComplement_eq_top
      S K hK hKS)

/-! ### Aligning the restriction fibres with the OW fibres -/

/-- The source intersection fibre is the source fibre occurring in the
ordinary OW count, after harmless subgroup-coordinate transport. -/
def okuyamaWajimaSourceIntersectionFibreEquiv
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p) :
    IrreducibleCharactersOverAlong
        ((K ⊔ (S : Subgroup Γ)).subgroupOf
          (okuyamaWajimaAmbientComplement S K hK hKS ⊔ K)).subtype
        (okuyamaWajimaSourceIntersectionCharacter
          S K hK hKS θ) ≃
      IrreducibleCharactersOverAlong
        (K.subgroupOf
          (okuyamaWajimaAmbientComplement S K hK hKS ⊔ K)).subtype
        (θ.1.1.comap
          (Subgroup.subgroupOfEquivOfLe le_sup_right)) := by
  let V : Subgroup Γ :=
    okuyamaWajimaAmbientComplement S K hK hKS ⊔ K
  let I : Subgroup V :=
    (K ⊔ (S : Subgroup Γ)).subgroupOf V
  let KI : Subgroup V :=
    K.subgroupOf V
  let eI : I ≃* K :=
    okuyamaWajimaSourceIntersectionEquivKernel S K hK hKS
  let eK : KI ≃* K :=
    Subgroup.subgroupOfEquivOfLe le_sup_right
  let fK : K →* V :=
    Subgroup.inclusion le_sup_right
  have hcommI :
      (MulEquiv.refl V).toMonoidHom.comp I.subtype =
        fK.comp eI.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    rfl
  have hcommK :
      (MulEquiv.refl V).toMonoidHom.comp KI.subtype =
        fK.comp eK.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    rfl
  let EI :=
    irreducibleCharactersOverAlongComapEquiv
      (MulEquiv.refl V) eI fK I.subtype hcommI θ.1.1
  let EK :=
    irreducibleCharactersOverAlongComapEquiv
      (MulEquiv.refl V) eK fK KI.subtype hcommK θ.1.1
  exact EI.symm.trans EK

/-- The target intersection fibre is the target fibre occurring in the
ordinary OW count, after transport from the internal complement to its
ambient image. -/
def okuyamaWajimaTargetIntersectionFibreEquiv
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p) :
    IrreducibleCharactersOverAlong
        ((okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ)).subgroupOf
            (okuyamaWajimaComplement S K hK hKS)).subtype
        (okuyamaWajimaTargetIntersectionCharacter
          S K hK hKS d θ) ≃
      IrreducibleCharactersOverAlong
        ((coprimeFixedPoints K (S : Subgroup Γ)).subgroupOf
          (okuyamaWajimaAmbientComplement S K hK hKS)).subtype
        ((d.characterEquiv θ).1.comap
          (Subgroup.subgroupOfEquivOfLe
            (fixedPoints_le_okuyamaWajimaAmbientComplement
              S K hK hKS))) := by
  let HN : Subgroup Γ :=
    Subgroup.normalizer ((S : Subgroup Γ) : Set Γ)
  let D : Subgroup Γ :=
    coprimeFixedPoints K (S : Subgroup Γ)
  let DH : Subgroup HN :=
    okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ)
  let U : Subgroup HN :=
    okuyamaWajimaComplement S K hK hKS
  let Ua : Subgroup Γ :=
    okuyamaWajimaAmbientComplement S K hK hKS
  let L : Subgroup HN :=
    okuyamaWajimaInternalNormalProduct K (S : Subgroup Γ)
  let I : Subgroup U :=
    L.subgroupOf U
  let Da : Subgroup Ua :=
    D.subgroupOf Ua
  let phi : IrreducibleCharacter D :=
    (d.characterEquiv θ).1
  let phiH : IrreducibleCharacter DH :=
    okuyamaWajimaInternalFixedPointCharacter S K d θ
  let eI : I ≃* DH :=
    okuyamaWajimaTargetIntersectionEquivFixedPoints S K hK hKS
  let eU : U ≃* Ua :=
    okuyamaWajimaComplementEquivAmbientComplement S K hK hKS
  let eD : DH ≃* D :=
    Subgroup.subgroupOfEquivOfLe
      (show
        D ≤ HN from
        inf_le_right.trans
          (Subgroup.centralizer_le_normalizer
            ((S : Subgroup Γ) : Set Γ)))
  let eDa : Da ≃* D :=
    Subgroup.subgroupOfEquivOfLe
      (fixedPoints_le_okuyamaWajimaAmbientComplement
        S K hK hKS)
  let fDH : DH →* U :=
    Subgroup.inclusion
      (internalFixedPoints_le_okuyamaWajimaComplement
        S K hK hKS)
  let fD : D →* Ua :=
    Subgroup.inclusion
      (fixedPoints_le_okuyamaWajimaAmbientComplement
        S K hK hKS)
  have hcommI :
      (MulEquiv.refl U).toMonoidHom.comp I.subtype =
        fDH.comp eI.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    rfl
  have hcommAmbient :
      eU.toMonoidHom.comp fDH =
        fD.comp eD.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    rfl
  have hcommCopy :
      (MulEquiv.refl Ua).toMonoidHom.comp Da.subtype =
        fD.comp eDa.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    rfl
  let EI :=
    irreducibleCharactersOverAlongComapEquiv
      (MulEquiv.refl U) eI fDH I.subtype hcommI phiH
  let EA :=
    irreducibleCharactersOverAlongComapEquiv
      eU eD fD fDH hcommAmbient phi
  let EC :=
    irreducibleCharactersOverAlongComapEquiv
      (MulEquiv.refl Ua) eDa fD Da.subtype hcommCopy phi
  exact EI.symm.trans (EA.symm.trans EC)

/-! ### Base fibres and the conditional count -/

/-- The source base fibre, transported to the exact source fibre in the
ordinary OW theorem. -/
def okuyamaWajimaSourceBaseFibreEquivOW
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (c : OkuyamaWajimaBaseExtensionData S K hKS d θ) :
    IrreducibleCharactersOverAlong
        (K ⊔ (S : Subgroup Γ) : Subgroup Γ).subtype
        c.sourceExtension ≃
      IrreducibleCharactersOverAlong
        (K.subgroupOf
          (okuyamaWajimaAmbientComplement S K hK hKS ⊔ K)).subtype
        (θ.1.1.comap
          (Subgroup.subgroupOfEquivOfLe le_sup_right)) :=
  (okuyamaWajimaSourceNormalProductRestrictionEquiv
      S K hK hKS d θ c).trans
    (okuyamaWajimaSourceIntersectionFibreEquiv
      S K hK hKS θ)

/-- The target base fibre, transported to the exact target fibre in the
ordinary OW theorem. -/
def okuyamaWajimaTargetBaseFibreEquivOW
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (c : OkuyamaWajimaBaseExtensionData S K hKS d θ) :
    IrreducibleCharactersOverAlong
        (okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ)).subtype
        c.targetExtension ≃
      IrreducibleCharactersOverAlong
        ((coprimeFixedPoints K (S : Subgroup Γ)).subgroupOf
          (okuyamaWajimaAmbientComplement S K hK hKS)).subtype
        ((d.characterEquiv θ).1.comap
          (Subgroup.subgroupOfEquivOfLe
            (fixedPoints_le_okuyamaWajimaAmbientComplement
              S K hK hKS))) :=
  (okuyamaWajimaTargetNormalProductRestrictionEquiv
      S K hK hKS d θ c).trans
    (okuyamaWajimaTargetIntersectionFibreEquiv
      S K hK hKS d θ)

/-- The current semantic uniform OW input, specialized to the canonical
ambient image of the chosen complement.

The complement is hidden inside this proposition and does not occur as a
free parameter of the base-count theorem. -/
def OkuyamaWajimaComplementUniformOrdinaryInput
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p) : Prop :=
  UniformOkuyamaWajimaExtensionComparison
    K (S : Subgroup Γ)
    (okuyamaWajimaAmbientComplement S K hK hKS)
    d θ

/-- Conditional base canonical-extension count.

Once the invariant source/target extensions and the current uniform
ordinary OW input are supplied, the two normal-product restriction
equivalences and the OW count give equal base-fibre cardinalities.  The
chosen Schur--Zassenhaus complement does not occur in the result type. -/
theorem natCard_over_okuyamaWajimaBaseExtensions_eq_normalizer
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (hinvariant : ∀ g : Γ, g • θ.1.1 = θ.1.1)
    (c : OkuyamaWajimaBaseExtensionData S K hKS d θ)
    (how :
      OkuyamaWajimaComplementUniformOrdinaryInput
        S K hK hKS d θ) :
    Nat.card
        (IrreducibleCharactersOverAlong
          (K ⊔ (S : Subgroup Γ) : Subgroup Γ).subtype
          c.sourceExtension) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)).subtype
          c.targetExtension) := by
  let U :=
    okuyamaWajimaAmbientComplement S K hK hKS
  have hOW :=
    okuyamaWajima_natCard_irreducibleCharactersOverAlong_eq
      K (S : Subgroup Γ) U
      S.isPGroup' hK
      (okuyamaWajimaAmbientComplement_le_normalizer
        S K hK hKS)
      (fixedPoints_le_okuyamaWajimaAmbientComplement
        S K hK hKS)
      d θ hinvariant how
  calc
    Nat.card
        (IrreducibleCharactersOverAlong
          (K ⊔ (S : Subgroup Γ) : Subgroup Γ).subtype
          c.sourceExtension) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (K.subgroupOf (U ⊔ K)).subtype
          (θ.1.1.comap
            (Subgroup.subgroupOfEquivOfLe le_sup_right))) :=
      Nat.card_congr
        (okuyamaWajimaSourceBaseFibreEquivOW
          S K hK hKS d θ c)
    _ =
      Nat.card
        (IrreducibleCharactersOverAlong
          ((coprimeFixedPoints
            K (S : Subgroup Γ)).subgroupOf U).subtype
          ((d.characterEquiv θ).1.comap
            (Subgroup.subgroupOfEquivOfLe
              (fixedPoints_le_okuyamaWajimaAmbientComplement
                S K hK hKS)))) :=
      hOW.symm
    _ =
      Nat.card
        (IrreducibleCharactersOverAlong
          (okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)).subtype
          c.targetExtension) :=
      (Nat.card_congr
        (okuyamaWajimaTargetBaseFibreEquivOW
          S K hK hKS d θ c)).symm

/-- Canonically chosen form of the conditional base count, using the named
existence hypothesis for the missing invariant extensions. -/
theorem natCard_over_canonicalExtension_eq_normalizer
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (hinvariant : ∀ g : Γ, g • θ.1.1 = θ.1.1)
    (hcanonical :
      OkuyamaWajimaCanonicalBaseExtensionHypothesis
        S K hKS d θ)
    (how :
      OkuyamaWajimaComplementUniformOrdinaryInput
        S K hK hKS d θ) :
    let c :=
      okuyamaWajimaCanonicalBaseExtensionData
        S K hKS d θ hcanonical
    Nat.card
        (IrreducibleCharactersOverAlong
          (K ⊔ (S : Subgroup Γ) : Subgroup Γ).subtype
          c.sourceExtension) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)).subtype
          c.targetExtension) :=
  natCard_over_okuyamaWajimaBaseExtensions_eq_normalizer
    S K hK hKS d θ hinvariant
    (okuyamaWajimaCanonicalBaseExtensionData
      S K hKS d θ hcanonical)
    how

end McKayConjecture
