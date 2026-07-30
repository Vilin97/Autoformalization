/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.NavarroAbelianLocalGlobalExtension
import McKayConjecture.Character.OkuyamaWajimaPrimeLocal

/-!
# Navarro input for the Okuyama--Wajima comparison

For an intermediate subgroup
`C_K(Q) ≤ V ≤ N_A(Q)` with `[V,V] ≤ C_K(Q)`, the target character
triple has abelian outer quotient by definition.  The canonical
Okuyama--Wajima quotient equivalence

`V / C_K(Q) ≃ (VK) / K`

transports this commutativity to the source character triple.  The
abelian-quotient instance of Navarro's Sylow-preimage criterion therefore
applies to both triples.

This closes the Navarro local--global input used by the source-audited
prime-local Okuyama--Wajima reduction.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture

open CharacterTriple
open GroupTheory

variable {A : Type} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable (K Q V : Subgroup A) [K.Normal]

/-- The source Okuyama--Wajima triple satisfies Navarro's Sylow-preimage
criterion whenever the corresponding target quotient is abelian. -/
theorem invariantOkuyamaWajimaSource_navarroInput_of_commutator_le
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hcomm :
      _root_.commutator V ≤
        (coprimeFixedPoints K Q).subgroupOf V) :
    CharacterTriple.NavarroSylowPreimageExtensionConclusion
      (invariantOkuyamaWajimaSourceTriple
        K Q V theta hinvariant) := by
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
  have hcommT :
      _root_.commutator V ≤ T.normalSubgroup := by
    change
      _root_.commutator V ≤
        (coprimeFixedPoints K Q).subgroupOf V
    exact hcomm
  have htarget :
      IsMulCommutative (V ⧸ T.normalSubgroup) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      hcommT
  have hsource :
      IsMulCommutative
        ((V ⊔ K : Subgroup A) ⧸ S.normalSubgroup) :=
    Function.Surjective.mul_comm
      (f := e.toMonoidHom) e.surjective htarget
  exact
    CharacterTriple.navarroSylowPreimageExtensionConclusion_of_commutator_le
      S
      (Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
        hsource)

/-- The target Okuyama--Wajima triple satisfies Navarro's Sylow-preimage
criterion directly from its abelian outer quotient. -/
theorem invariantOkuyamaWajimaTarget_navarroInput_of_commutator_le
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hcomm :
      _root_.commutator V ≤
        (coprimeFixedPoints K Q).subgroupOf V) :
    CharacterTriple.NavarroSylowPreimageExtensionConclusion
      (invariantOkuyamaWajimaTargetTriple
        K Q V hV hCV d theta hinvariant) := by
  apply
    CharacterTriple.navarroSylowPreimageExtensionConclusion_of_commutator_le
  change
    _root_.commutator V ≤
      (coprimeFixedPoints K Q).subgroupOf V
  exact hcomm

/-- Both canonical Okuyama--Wajima triples satisfy Navarro's
Sylow-preimage criterion for one abelian intermediate subgroup. -/
theorem invariantOkuyamaWajimaNavarroInput_of_commutator_le
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hcomm :
      _root_.commutator V ≤
        (coprimeFixedPoints K Q).subgroupOf V) :
    CharacterTriple.NavarroSylowPreimageExtensionConclusion
        (invariantOkuyamaWajimaSourceTriple
          K Q V theta hinvariant) ∧
      CharacterTriple.NavarroSylowPreimageExtensionConclusion
        (invariantOkuyamaWajimaTargetTriple
          K Q V hV hCV d theta hinvariant) :=
  ⟨invariantOkuyamaWajimaSource_navarroInput_of_commutator_le
      K Q V hQ hK hV hCV d theta hinvariant hcomm,
    invariantOkuyamaWajimaTarget_navarroInput_of_commutator_le
      K Q V hV hCV d theta hinvariant hcomm⟩

section Uniform

variable (U : Subgroup A)

/-- The abelian-quotient Navarro theorem discharges the uniform Navarro
input for every intermediate subgroup in the Okuyama--Wajima reduction. -/
theorem uniformInvariantOkuyamaWajimaNavarroInput
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    UniformInvariantOkuyamaWajimaNavarroInput
      K Q U hU d theta hinvariant := by
  intro V hCV hVU hcomm
  exact
    invariantOkuyamaWajimaNavarroInput_of_commutator_le
      K Q V hQ hK (hVU.trans hU) hCV d theta hinvariant hcomm

end Uniform

end McKayConjecture
