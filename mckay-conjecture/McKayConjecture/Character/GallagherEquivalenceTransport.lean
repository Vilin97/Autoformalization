/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ExtensionEquivalenceTransport
import McKayConjecture.Character.GallagherPPrime
import McKayConjecture.Character.OverAlongTransport
import McKayConjecture.GroupTheory.QuotientEquivalenceTransport

/-!
# Transport of the Gallagher correspondence

Gallagher tensoring is natural under a commuting isomorphism of an ambient
group, its normal subgroup, and the corresponding quotient.  This is the
precise elementary transport statement used when a fibre correspondence is
chosen on one orbit representative and propagated by conjugation.

The quotient equivalence is kept explicit.  In applications it is normally
the quotient map induced by the ambient equivalence, and
`quotient_mk_commutes` is then its defining formula.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

variable {K K' : Type} [Group K] [Group K']
variable [Finite K] [Finite K']
variable {H : Subgroup K} {H' : Subgroup K'}
variable [H.Normal] [H'.Normal]

/-- The Gallagher tensor character commutes with simultaneous transport of
the ambient group, normal subgroup, and quotient. -/
theorem gallagherTensorCharacter_comap_equiv
    (eK : K' ≃* K)
    (eH : H' ≃* H)
    (eQ : (K' ⧸ H') ≃* (K ⧸ H))
    (subgroup_square :
      eK.toMonoidHom.comp H'.subtype =
        H.subtype.comp eH.toMonoidHom)
    (quotient_mk_commutes :
      ∀ g : K',
        eQ (QuotientGroup.mk' H' g) =
          QuotientGroup.mk' H (eK g))
    {χ : IrreducibleCharacter H}
    {ψ : IrreducibleCharacter K}
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    (gallagherTensorCharacter hψ beta).comap eK =
      gallagherTensorCharacter
        (hψ.comap_equiv eK eH subgroup_square)
        (beta.comap eQ) := by
  apply IrreducibleCharacter.ext
  funext g
  rw [comap_values, gallagherTensorCharacter_values,
    gallagherTensorCharacter_values, comap_values,
    comap_values, quotient_mk_commutes]

/-- Canonical form of Gallagher tensor naturality, using the quotient
equivalence induced by the commuting ambient/subgroup square. -/
theorem gallagherTensorCharacter_comap_subgroupEquiv
    (eK : K' ≃* K)
    (eH : H' ≃* H)
    (subgroup_square :
      eK.toMonoidHom.comp H'.subtype =
        H.subtype.comp eH.toMonoidHom)
    {χ : IrreducibleCharacter H}
    {ψ : IrreducibleCharacter K}
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    (gallagherTensorCharacter hψ beta).comap eK =
      gallagherTensorCharacter
        (hψ.comap_equiv eK eH subgroup_square)
        (beta.comap
          (GroupTheory.quotientMulEquivOfSubgroupEquiv
            eK eH subgroup_square)) :=
  gallagherTensorCharacter_comap_equiv
    eK eH
    (GroupTheory.quotientMulEquivOfSubgroupEquiv
      eK eH subgroup_square)
    subgroup_square
    (GroupTheory.quotientMulEquivOfSubgroupEquiv_mk
      eK eH subgroup_square)
    hψ beta

/-- Naturality of the prime-to-`p` Gallagher correspondence in the exact
`PPrimeIrreducibleCharactersOverAlong` fibre coordinates used by Clifford
assembly. -/
theorem gallagherPPrimeCorrespondenceOfSource_comap_equiv
    {p : ℕ}
    (hp : p.Prime)
    (eK : K' ≃* K)
    (eH : H' ≃* H)
    (eQ : (K' ⧸ H') ≃* (K ⧸ H))
    (subgroup_square :
      eK.toMonoidHom.comp H'.subtype =
        H.subtype.comp eH.toMonoidHom)
    (quotient_mk_commutes :
      ∀ g : K',
        eQ (QuotientGroup.mk' H' g) =
          QuotientGroup.mk' H (eK g))
    {χ : IrreducibleCharacter H}
    {ψ : IrreducibleCharacter K}
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (hχp : χ.IsPPrimeDegree p)
    (beta : PPrimeIrreducibleCharacter (K ⧸ H) p) :
    CliffordCorrespondence.pPrimeIrreducibleCharactersOverAlongComapEquiv
        eK eH H.subtype H'.subtype subgroup_square χ p
        (gallagherPPrimeCorrespondenceOfSource
          hp hψ hχp beta) =
      gallagherPPrimeCorrespondenceOfSource
        hp
        (hψ.comap_equiv eK eH subgroup_square)
        hχp
        (pPrimeComapEquiv p eQ beta) := by
  apply Subtype.ext
  apply Subtype.ext
  exact
    gallagherTensorCharacter_comap_equiv
      eK eH eQ subgroup_square quotient_mk_commutes
        hψ beta.1

/-- Canonical commuting-square form of prime-to-`p` Gallagher
naturality. -/
theorem gallagherPPrimeCorrespondenceOfSource_comap_subgroupEquiv
    {p : ℕ}
    (hp : p.Prime)
    (eK : K' ≃* K)
    (eH : H' ≃* H)
    (subgroup_square :
      eK.toMonoidHom.comp H'.subtype =
        H.subtype.comp eH.toMonoidHom)
    {χ : IrreducibleCharacter H}
    {ψ : IrreducibleCharacter K}
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (hχp : χ.IsPPrimeDegree p)
    (beta : PPrimeIrreducibleCharacter (K ⧸ H) p) :
    CliffordCorrespondence.pPrimeIrreducibleCharactersOverAlongComapEquiv
        eK eH H.subtype H'.subtype subgroup_square χ p
        (gallagherPPrimeCorrespondenceOfSource
          hp hψ hχp beta) =
      gallagherPPrimeCorrespondenceOfSource
        hp
        (hψ.comap_equiv eK eH subgroup_square)
        hχp
        (pPrimeComapEquiv p
          (GroupTheory.quotientMulEquivOfSubgroupEquiv
            eK eH subgroup_square) beta) :=
  gallagherPPrimeCorrespondenceOfSource_comap_equiv
    hp eK eH
    (GroupTheory.quotientMulEquivOfSubgroupEquiv
      eK eH subgroup_square)
    subgroup_square
    (GroupTheory.quotientMulEquivOfSubgroupEquiv_mk
      eK eH subgroup_square)
    hψ hχp beta

end IrreducibleCharacter
end McKayConjecture
