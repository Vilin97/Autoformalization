/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientPPrimeCharacterEnumeration
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCentralBlockRowMatching
import McKayConjecture.InductiveMcKay.AlternatingSixFiveConcreteFiniteTable
import McKayConjecture.InductiveMcKay.AlternatingSixThreeDisplayedRowBridge
import McKayConjecture.InductiveMcKay.AlternatingSixTwoAmbientRowMatching

/-!
# Numerical McKay equivalences for the canonical cover of `A₆`

Once the ambient ordinary table is completed, its arithmetic `p'` row
enumeration composes with the proved local normalizer tables and the finite
row matchings.  The resulting equivalences prove the literal McKay
cardinality statement at the three primes dividing `|A₆|`.

These numerical equivalences do not assert stabilizer equivariance or
projective factor-set compatibility.  Those stronger properties remain
separate inputs to the inductive McKay condition.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixCanonicalCoverNumericalMcKayFactTwo :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

local instance alternatingSixCanonicalCoverNumericalMcKayFactThree :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

local instance alternatingSixCanonicalCoverNumericalMcKayFactFive :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- Explicit numerical McKay character equivalence for the canonical cover
at `p = 2`. -/
def alternatingSixCanonicalCoverTwoMcKayCharacterEquiv
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    PPrimeIrreducibleCharacter AlternatingSixUniversalCover 2 ≃
      PPrimeIrreducibleCharacter
        (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) 2 :=
  (alternatingSixAmbientPPrimeCharacterEquiv T 2).symm.trans
    (alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow.trans
      alternatingSixTwoActualNormalizerPPrimeCharacterEquiv)

/-- Explicit numerical McKay character equivalence for the canonical cover
at `p = 3`. -/
def alternatingSixCanonicalCoverThreeMcKayCharacterEquiv
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    PPrimeIrreducibleCharacter AlternatingSixUniversalCover 3 ≃
      PPrimeIrreducibleCharacter
        (SylowNormalizer (alternatingSixUniversalCoverSylow 3)) 3 :=
  (alternatingSixAmbientPPrimeCharacterEquiv T 3).symm.trans
    alternatingSixThreeDisplayedOrderActualLocalCharacterEnumeration

/-- Explicit numerical McKay character equivalence for the canonical cover
at `p = 5`. -/
def alternatingSixCanonicalCoverFiveMcKayCharacterEquiv
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    PPrimeIrreducibleCharacter AlternatingSixUniversalCover 5 ≃
      PPrimeIrreducibleCharacter
        (SylowNormalizer (alternatingSixUniversalCoverSylow 5)) 5 :=
  (alternatingSixAmbientPPrimeCharacterEquiv T 5).symm.trans
    (alternatingSixAmbientFivePPrimeCentralBlockRowEquiv.trans
      alternatingSixFiveActualNormalizerPPrimeCharacterEquiv)

/-- The completed table proves the numerical McKay statement for the fixed
Sylow `2`-subgroup of the canonical cover. -/
theorem alternatingSixCanonicalCover_statement_two
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Statement AlternatingSixUniversalCover 2
      (alternatingSixUniversalCoverSylow 2) :=
  Cardinal.mk_congr
    (alternatingSixCanonicalCoverTwoMcKayCharacterEquiv T)

/-- The completed table proves the numerical McKay statement for the fixed
Sylow `3`-subgroup of the canonical cover. -/
theorem alternatingSixCanonicalCover_statement_three
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Statement AlternatingSixUniversalCover 3
      (alternatingSixUniversalCoverSylow 3) :=
  Cardinal.mk_congr
    (alternatingSixCanonicalCoverThreeMcKayCharacterEquiv T)

/-- The completed table proves the numerical McKay statement for the fixed
Sylow `5`-subgroup of the canonical cover. -/
theorem alternatingSixCanonicalCover_statement_five
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Statement AlternatingSixUniversalCover 5
      (alternatingSixUniversalCoverSylow 5) :=
  Cardinal.mk_congr
    (alternatingSixCanonicalCoverFiveMcKayCharacterEquiv T)

end InductiveMcKay
end McKayConjecture
