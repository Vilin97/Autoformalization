/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaProperBranchQuotientComparison
import McKayConjecture.Character.OkuyamaWajimaProperBranchSubgroupInduction

/-!
# Automatic induction adapters in the proper Okuyama--Wajima branch

For the subgroup selected by the Gorenstein construction inside the
canonical ambient complement, both recursive coordinate adapters are
automatic.

* The quotient adapter uses the exact source and target comparisons for
  `N_G(Q) / Q`.
* The subgroup adapter uses the canonical group scope for
  `H = Q M K` and transports the printed statement on `H`.

Thus the proper-branch field of
`OkuyamaWajimaCanonicalBranchAssemblyInput` requires no residual
character-coordinate premise.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open GroupTheory

section SelectedProperBranchAdapters

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable
  (hK : IsPPrimeGroup p K)
  (hKP : (K ⊔ (P : Subgroup G)).Normal)

local instance selectedProperBranchAdaptersPConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

local instance selectedProperBranchAdaptersComplementConjugationAction :
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
  (gP :
    GlaubermanCorrespondence K (P : Subgroup G) p)

/-- The canonical Gorenstein-selected proper branch has both induction
adapters required by the printed strong-induction assembly.

This is the direct provider for the proper-branch field
`assembly.2 d hproper` of
`OkuyamaWajimaCanonicalBranchAssemblyInput`. -/
theorem
    okuyamaWajimaProperBranchSelectedInductionAdapters_automatic
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G))
    (hproper : d.fixedPoints < ⊤) :
    Nonempty
      (OkuyamaWajimaProperBranchInductionAdapters
        K P d.fixedPointPreimage
          (okuyamaWajimaProperBranchComplement K P hK hKP)
          theta hinvariant
          (okuyamaWajimaProperBranchSelectedGlaubermanCorrespondence
            K P hK hKP d)
          gP) := by
  let gQ :=
    okuyamaWajimaProperBranchSelectedGlaubermanCorrespondence
      K P hK hKP d
  let scope :
      OkuyamaWajimaProperBranchGroupScope
        K P d.fixedPointPreimage
          (okuyamaWajimaProperBranchComplement K P hK hKP) :=
    okuyamaWajimaProperBranchGroupScopeFromComplement
      K P hK hKP d hproper
  let coordinates :
      OkuyamaWajimaProperBranchQuotientExtensionCoordinateComparison
        K P d.fixedPointPreimage theta hinvariant gQ gP hK :=
    okuyamaWajimaProperBranchSelectedQuotientExtensionCoordinateComparison_automatic
      K P hK hKP d theta hinvariant gQ gP
  refine ⟨{ quotient := ?_, subgroup := ?_ }⟩
  · exact
      okuyamaWajimaProperBranchQuotientInductionAdapter
        K P d.fixedPointPreimage theta hinvariant gQ gP
          hK hcommutativeQuotient coordinates
  · exact
      okuyamaWajimaProperBranchSubgroupInductionHypothesis_of_printedStatement
        K P d.fixedPointPreimage
          (okuyamaWajimaProperBranchComplement K P hK hKP)
          theta hinvariant gQ hK scope hcommutativeQuotient

end SelectedProperBranchAdapters

end McKayConjecture
