/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GallagherBaseChange
import McKayConjecture.Character.GallagherEquivalenceTransport
import McKayConjecture.Character.PGroupQuotientGallagher

/-!
# Covariant Gallagher coordinates with independently chosen extensions

Transporting a Gallagher fibre along a commuting equivalence square carries
the chosen base extension to its literal pullback.  An independently chosen
base extension on the target need not equal that pullback.  The two differ
by the canonical quotient-linear base-change parameter, and multiplying by
its inverse gives the exact target Gallagher coordinate.

This file combines equivalence naturality with base-extension independence.
It is the elementary choice-control statement used in normalizer-equivariant
orbitwise gluing.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

variable {K K' : Type} [Group K] [Group K']
variable [Finite K] [Finite K']
variable {H : Subgroup K} {H' : Subgroup K'}
variable [H.Normal] [H'.Normal]

/-- The quotient-linear discrepancy between the literal pullback of a
source extension and an independently selected target extension. -/
def gallagherTransportBaseChangeParameter
    (eK : K' ≃* K)
    (eH : H' ≃* H)
    (subgroupSquare :
      eK.toMonoidHom.comp H'.subtype =
        H.subtype.comp eH.toMonoidHom)
    {χ : IrreducibleCharacter H}
    {ψ : IrreducibleCharacter K}
    {ψ' : IrreducibleCharacter K'}
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (hψ' :
      IsExtensionAlong H'.subtype
        (χ.comap eH) ψ') :
    (K' ⧸ H') →* ℂˣ :=
  gallagherBaseChangeParameter
    (hψ.comap_equiv eK eH subgroupSquare) hψ'

/-- Correct a transported quotient-linear parameter so that it is measured
relative to the independently selected target extension. -/
def gallagherTransportedLinearParameter
    (eK : K' ≃* K)
    (eH : H' ≃* H)
    (eQ : (K' ⧸ H') ≃* (K ⧸ H))
    (subgroupSquare :
      eK.toMonoidHom.comp H'.subtype =
        H.subtype.comp eH.toMonoidHom)
    {χ : IrreducibleCharacter H}
    {ψ : IrreducibleCharacter K}
    {ψ' : IrreducibleCharacter K'}
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (hψ' :
      IsExtensionAlong H'.subtype
        (χ.comap eH) ψ')
    (mu : (K ⧸ H) →* ℂˣ) :
    (K' ⧸ H') →* ℂˣ :=
  (gallagherTransportBaseChangeParameter
      eK eH subgroupSquare hψ hψ')⁻¹ *
    mu.comp eQ.toMonoidHom

/-- Pullback of a prime-to-`p` Gallagher character, followed by correction
for an independently chosen target extension, is exactly the target
Gallagher character with the corrected quotient-linear parameter. -/
theorem gallagherLinearCorrespondence_comap_with_baseChange
    {p : ℕ} [Fact p.Prime]
    (eK : K' ≃* K)
    (eH : H' ≃* H)
    (eQ : (K' ⧸ H') ≃* (K ⧸ H))
    (subgroupSquare :
      eK.toMonoidHom.comp H'.subtype =
        H.subtype.comp eH.toMonoidHom)
    (quotientMkCommutes :
      ∀ g : K',
        eQ (QuotientGroup.mk' H' g) =
          QuotientGroup.mk' H (eK g))
    {χ : IrreducibleCharacter H}
    {ψ : IrreducibleCharacter K}
    {ψ' : IrreducibleCharacter K'}
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (hψ' :
      IsExtensionAlong H'.subtype
        (χ.comap eH) ψ')
    (hχp : χ.IsPPrimeDegree p)
    (hχp' : (χ.comap eH).IsPPrimeDegree p)
    (hquotient : IsPGroup p (K ⧸ H))
    (hquotient' : IsPGroup p (K' ⧸ H'))
    (mu : (K ⧸ H) →* ℂˣ) :
    CliffordCorrespondence.pPrimeIrreducibleCharactersOverAlongComapEquiv
        eK eH H.subtype H'.subtype subgroupSquare χ p
        (gallagherLinearCorrespondenceOfPGroupQuotient
          H hquotient hψ hχp mu) =
      gallagherLinearCorrespondenceOfPGroupQuotient
        H' hquotient' hψ' hχp'
        (gallagherTransportedLinearParameter
          eK eH eQ subgroupSquare hψ hψ' mu) := by
  apply Subtype.ext
  apply Subtype.ext
  let transportedExtensionProof :=
    hψ.comap_equiv eK eH subgroupSquare
  let lam :=
    gallagherTransportBaseChangeParameter
      eK eH subgroupSquare hψ hψ'
  let muTransported :=
    mu.comp eQ.toMonoidHom
  let nu :=
    gallagherTransportedLinearParameter
      eK eH eQ subgroupSquare hψ hψ' mu
  have hbase :
      ψ' =
        twist (inflateLinearCharacter H' lam)
          (ψ.comap eK) :=
    gallagherBaseChangeParameter_spec
      transportedExtensionProof hψ'
  have hparameter : lam * nu = muTransported := by
    dsimp only [nu, gallagherTransportedLinearParameter]
    change lam * (lam⁻¹ * muTransported) = muTransported
    apply MonoidHom.ext
    intro x
    simp
  change
    (gallagherTensorCharacter hψ (linear mu)).comap eK =
      gallagherTensorCharacter hψ' (linear nu)
  calc
    (gallagherTensorCharacter hψ (linear mu)).comap eK =
        gallagherTensorCharacter transportedExtensionProof
          ((linear mu).comap eQ) :=
      gallagherTensorCharacter_comap_equiv
        eK eH eQ subgroupSquare quotientMkCommutes
          hψ (linear mu)
    _ =
        gallagherTensorCharacter transportedExtensionProof
          (linear muTransported) := by
      rw [linear_comap]
      rfl
    _ =
        gallagherTensorCharacter transportedExtensionProof
          (linear (lam * nu)) := by
      rw [hparameter]
    _ =
        gallagherTensorCharacter hψ' (linear nu) :=
      (gallagherTensorCharacter_linear_baseChange
        transportedExtensionProof hψ' lam nu hbase).symm

end IrreducibleCharacter
end McKayConjecture
