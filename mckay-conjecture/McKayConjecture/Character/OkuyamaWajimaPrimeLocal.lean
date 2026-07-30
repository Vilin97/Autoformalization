/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.NavarroLocalGlobalExtension
import McKayConjecture.Character.OkuyamaWajimaGoodElement
import McKayConjecture.GroupTheory.OkuyamaWajimaPrimeLocal

/-!
# Prime-local discharge of the Okuyama--Wajima extension comparison

This file isolates the source-audited route from the original
Okuyama--Wajima theorem to the semantic extension comparison used by the
good-element argument.

For the two canonical character triples `(VK, K, θ)` and
`(V, C_K(Q), θ*)`, Navarro's Sylow-preimage criterion reduces global
extension comparison to corresponding Sylow preimages of their isomorphic
quotients.  At the distinguished prime `p`, both extensions exist
automatically because the two kernels are `p'`-groups.  Thus the only
Okuyama--Wajima-specific input is the comparison at primes `r ≠ p`.

The original 1980 theorem is to be applied only in those `r ≠ p` local
pieces.  In particular, this file does not assert that `Q` is Sylow in
`KQV`, or that `V ∩ KQ = C_K(Q)`, for a mixed-prime subgroup `V`.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open GroupTheory

variable {A : Type} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable (K Q V : Subgroup A) [K.Normal]

/-- The exact prime-away local comparison left after the canonical OW
quotient equivalence has identified the source and target quotients.

This proposition quantifies only over primes `r ≠ p`.  Its intended proof
applies the original Okuyama--Wajima Sylow-normalizer theorem to the
corresponding `r`-local groups, together with Navarro local--global on the
resulting two-prime quotients. -/
def InvariantOkuyamaWajimaPrimeAwayExtensionComparison
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  CharacterTriple.PrimeAwaySylowPreimageExtensionComparison
    p
    (invariantOkuyamaWajimaSourceTriple
      K Q V theta hinvariant)
    (invariantOkuyamaWajimaTargetTriple
      K Q V hV hCV d theta hinvariant)
    (okuyamaWajimaQuotientEquiv
      K Q hQ hK V hV hCV)

/-- Formal statement of the remaining prime-away consequence of the
original Okuyama--Wajima theorem.

Normality of `KQ` and abelianness of `V / C_K(Q)` are premises rather
than conclusions.  This definition names the theorem statement and does
not assert its proof. -/
def InvariantOkuyamaWajimaPrimeAwayOriginalConclusion
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  (K ⊔ Q).Normal →
    _root_.commutator V ≤
        (coprimeFixedPoints K Q).subgroupOf V →
      InvariantOkuyamaWajimaPrimeAwayExtensionComparison
        K Q V hQ hK hV hCV d theta hinvariant

/-- The two OW normal subgroups are `p'`-groups in their canonical
internal coordinates. -/
theorem invariantOkuyamaWajima_internalKernels_isPPrime
    (hK : IsPPrimeGroup p K)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    IsPPrimeGroup p
        (invariantOkuyamaWajimaSourceTriple
          K Q V theta hinvariant).normalSubgroup ∧
      IsPPrimeGroup p
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant).normalSubgroup := by
  constructor
  · exact
      hK.of_equiv
        (Subgroup.subgroupOfEquivOfLe
          (show K ≤ V ⊔ K from le_sup_right)).symm
  · let C := coprimeFixedPoints K Q
    have hCK : C ≤ K := inf_le_left
    have hCInK :
        IsPPrimeGroup p (C.subgroupOf K) :=
      hK.to_subgroup (C.subgroupOf K)
    have hC : IsPPrimeGroup p C :=
      hCInK.of_equiv
        (Subgroup.subgroupOfEquivOfLe hCK)
    exact
      hC.of_equiv
        (Subgroup.subgroupOfEquivOfLe hCV).symm

/-- Navarro local--global on both canonical triples, automatic extension
at `p`, and the prime-away OW comparison imply the semantic global
extension conclusion. -/
theorem okuyamaWajimaExtensionConclusion_of_navarro_of_primeAway
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hNavarroSource :
      CharacterTriple.NavarroSylowPreimageExtensionConclusion
        (invariantOkuyamaWajimaSourceTriple
          K Q V theta hinvariant))
    (hNavarroTarget :
      CharacterTriple.NavarroSylowPreimageExtensionConclusion
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant))
    (haway :
      InvariantOkuyamaWajimaPrimeAwayExtensionComparison
        K Q V hQ hK hV hCV d theta hinvariant) :
    okuyamaWajimaExtensionConclusion
      K Q V hCV d theta := by
  let S :=
    invariantOkuyamaWajimaSourceTriple
      K Q V theta hinvariant
  let T :=
    invariantOkuyamaWajimaTargetTriple
      K Q V hV hCV d theta hinvariant
  let e :
      V ⧸ T.normalSubgroup ≃*
        (V ⊔ K : Subgroup A) ⧸ S.normalSubgroup :=
    okuyamaWajimaQuotientEquiv
      K Q hQ hK V hV hCV
  obtain ⟨hSK, hTK⟩ :=
    invariantOkuyamaWajima_internalKernels_isPPrime
      K Q V hK hV hCV d theta hinvariant
  have hglobal :
      S.HasExtension ↔ T.HasExtension :=
    CharacterTriple.hasExtension_iff_of_navarro_of_primeAwayComparison
      S T e hSK hTK hNavarroSource hNavarroTarget haway
  rw [okuyamaWajimaExtensionConclusion]
  rw [exists_extensionAlong_inclusion_iff_subgroupOf]
  rw [exists_extensionAlong_inclusion_iff_subgroupOf]
  exact hglobal

section Uniform

variable (U : Subgroup A)

/-- The needed abelian-quotient instance of Navarro's local--global
conclusion, uniformly for both canonical triples attached to every
intermediate subgroup `C_K(Q) ≤ V ≤ U`.

The commutator premise keeps this interface weaker than the unrestricted
Navarro theorem and leaves open a direct proof by Sylow-factor assembly. -/
def UniformInvariantOkuyamaWajimaNavarroInput
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  ∀ (V : Subgroup A)
      (hCV : coprimeFixedPoints K Q ≤ V)
      (hVU : V ≤ U),
    _root_.commutator V ≤
        (coprimeFixedPoints K Q).subgroupOf V →
      CharacterTriple.NavarroSylowPreimageExtensionConclusion
          (invariantOkuyamaWajimaSourceTriple
            K Q V theta hinvariant) ∧
        CharacterTriple.NavarroSylowPreimageExtensionConclusion
          (invariantOkuyamaWajimaTargetTriple
            K Q V (hVU.trans hU) hCV d theta hinvariant)

/-- The prime-away original OW conclusion uniformly for every abelian
intermediate subgroup. -/
def UniformInvariantOkuyamaWajimaPrimeAwayOriginalInput
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  ∀ (V : Subgroup A)
      (hCV : coprimeFixedPoints K Q ≤ V)
      (hVU : V ≤ U),
    InvariantOkuyamaWajimaPrimeAwayOriginalConclusion
      K Q V hQ hK (hVU.trans hU) hCV d theta hinvariant

/-- The source-audited prime-local route supplies exactly the semantic
uniform comparison consumed by `OkuyamaWajimaGoodElement`. -/
theorem uniformOkuyamaWajimaExtensionComparison_of_primeLocal
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hKQ : (K ⊔ Q).Normal)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hNavarro :
      UniformInvariantOkuyamaWajimaNavarroInput
        K Q U hU d theta hinvariant)
    (haway :
      UniformInvariantOkuyamaWajimaPrimeAwayOriginalInput
        K Q U hQ hK hU d theta hinvariant) :
    UniformOkuyamaWajimaExtensionComparison
      K Q U d theta := by
  intro V hCV hVU hcomm
  obtain ⟨hNavS, hNavT⟩ :=
    hNavarro V hCV hVU hcomm
  exact
    okuyamaWajimaExtensionConclusion_of_navarro_of_primeAway
      K Q V hQ hK (hVU.trans hU) hCV d theta hinvariant
      hNavS hNavT
      (haway V hCV hVU hKQ hcomm)

end Uniform

end McKayConjecture
