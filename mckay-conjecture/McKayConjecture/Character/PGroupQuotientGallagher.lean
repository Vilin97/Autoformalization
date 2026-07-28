/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GallagherPPrime
import McKayConjecture.Character.PGroupPPrimeLinearEquiv

/-!
# Gallagher fibres over finite `p`-group quotients

Once a prime-to-`p` normal-subgroup character has been extended across a
finite `p`-group quotient, Gallagher's correspondence identifies the whole
prime-to-`p` fibre with the linear characters of the quotient.

The extension is an explicit input: it does not exist for a general
invariant character without an additional coprime-extension theorem.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (N : Subgroup G) [N.Normal]

/-- Gallagher's prime-to-`p` fibre over an extendible character, with the
quotient side expressed as multiplicative linear characters. -/
def gallagherLinearCorrespondenceOfPGroupQuotient
    (hquotient : IsPGroup p (G ⧸ N))
    {θ : IrreducibleCharacter N}
    {ψ : IrreducibleCharacter G}
    (hψ : IsExtensionAlong N.subtype θ ψ)
    (hθp : θ.IsPPrimeDegree p) :
    ((G ⧸ N) →* ℂˣ) ≃
      CliffordCorrespondence.PPrimeIrreducibleCharactersOverAlong
        N.subtype θ p :=
  (pGroupPPrimeLinearEquiv hquotient).symm.trans
    (gallagherPPrimeCorrespondenceOfSource
      (Fact.out : p.Prime) hψ hθp)

end IrreducibleCharacter
end McKayConjecture
