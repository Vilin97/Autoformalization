/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaProperBranchQuotientSourceComparison
import McKayConjecture.Character.OkuyamaWajimaProperBranchQuotientTargetComparison

/-!
# Automatic quotient coordinates in the proper Okuyama--Wajima branch

This file assembles the source and target extension-coordinate comparisons
for the subgroup selected by the Gorenstein construction.

The resulting structure is the complete quotient-coordinate input required
by `okuyamaWajimaProperBranchQuotientInductionAdapter`; no additional
normalizer-containment or character-transport hypothesis remains.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open GroupTheory

section SelectedQuotientCoordinates

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable
  (hK : IsPPrimeGroup p K)
  (hKP : (K ⊔ (P : Subgroup G)).Normal)

local instance selectedQuotientCoordinatesPConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

local instance selectedQuotientCoordinatesComplementConjugationAction :
    MulDistribMulAction
      (okuyamaWajimaProperBranchComplement K P hK hKP)
      P :=
  normalizingSubgroupConjugationAction
    (P : Subgroup G)
    (okuyamaWajimaProperBranchComplement K P hK hKP)
    (okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP)

variable
  {L :
    Subgroup
      (okuyamaWajimaProperBranchComplement K P hK hKP)}
  (d :
    OkuyamaWajimaCyclicQuotientSubgroup
      (okuyamaWajimaProperBranchComplement K P hK hKP)
      P L)
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)
  (gQ :
    GlaubermanCorrespondence K
      (okuyamaWajimaProperBranchQ
        P d.fixedPointPreimage) p)
  (gP :
    GlaubermanCorrespondence K (P : Subgroup G) p)

/-- The automatically selected proper quotient has both exact extension
coordinates required by the quotient recursive call. -/
theorem
    okuyamaWajimaProperBranchSelectedQuotientExtensionCoordinateComparison_automatic :
    OkuyamaWajimaProperBranchQuotientExtensionCoordinateComparison
      K P d.fixedPointPreimage theta hinvariant gQ gP hK where
  source :=
    okuyamaWajimaProperBranchQuotientSourceExtensionCoordinateComparison
      K P d.fixedPointPreimage theta hinvariant gQ hK
  target :=
    okuyamaWajimaProperBranchSelectedQuotientTargetExtensionCoordinateComparison
      K P hK hKP d theta hinvariant gQ gP

end SelectedQuotientCoordinates

end McKayConjecture
