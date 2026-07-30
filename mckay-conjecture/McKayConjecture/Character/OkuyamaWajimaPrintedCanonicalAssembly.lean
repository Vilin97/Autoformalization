/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaFullFixedOuterForward
import McKayConjecture.Character.OkuyamaWajimaFullFixedOuterReverse
import McKayConjecture.Character.OkuyamaWajimaProperBranchInductionAdapters

/-!
# Complete canonical assembly of the printed Okuyama--Wajima induction

The full-fixed branch is supplied by the two automatic outer
implications, while the proper branch is supplied by the automatic
quotient and subgroup induction adapters.  Combining these branchwise
results closes the residual canonical assembly interface and hence the
strong induction in the printed extension theorem.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open GroupTheory
open OkuyamaWajimaFullFixedOuterForward
open OkuyamaWajimaFullFixedOuterReverse

variable {p : ℕ} [Fact p.Prime]

/-- Every field of the canonical printed-induction assembly is
automatic. -/
theorem okuyamaWajimaPrintedCanonicalAssemblyInput_automatic :
    OkuyamaWajimaPrintedCanonicalAssemblyInput p := by
  intro G _ _ K _ P
  letI : MulDistribMulAction P K :=
    subgroupConjugationMulDistribMulAction K (P : Subgroup G)
  intro hK hproduct hcommutativeQuotient
    theta hinvariant gP _hP
  let hKP : (K ⊔ (P : Subgroup G)).Normal :=
    normal_sup_sylow_normal_of_sup_normalizer_eq_top
      K P hproduct
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let hM :
      M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP
  letI : MulDistribMulAction M P :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      M P hM
  let L := okuyamaWajimaActionKernel M P
  change
    (∀ (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
        (hfull : d.fixedPoints = ⊤),
        OkuyamaWajimaFullFixedCoordinates.FullFixedCoprimeCentralizationInput
              M P hM d P.isPGroup'
                (okuyamaWajimaAmbientComplement_isPPrimeGroup
                  K P hK hKP)
                hfull →
          OkuyamaWajimaFullFixedOuterAssemblyInput
            K P theta hinvariant gP) ∧
      ∀ (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
        (hproper : d.fixedPoints < ⊤),
        Nonempty
          (OkuyamaWajimaProperBranchInductionAdapters
            K P d.fixedPointPreimage M theta hinvariant
              (okuyamaWajimaProperBranchSelectedGlaubermanCorrespondence
                K P hK hKP d)
              gP)
  constructor
  · intro d hfull _hBurnside
    constructor
    · exact
        okuyamaWajimaFullFixed_source_of_target_canonicalSelected
          K P hK hKP theta hinvariant gP
            hcommutativeQuotient d hfull
    · intro hsource
      exact
        okuyamaWajimaFullFixed_target_of_source
          K P theta hinvariant hK hKP gP
            hcommutativeQuotient hsource d hfull
  · intro d hproper
    exact
      okuyamaWajimaProperBranchSelectedInductionAdapters_automatic
        K P hK hKP d theta hinvariant gP
          hcommutativeQuotient hproper

/-- The complete printed Okuyama--Wajima extension theorem for every
finite group. -/
theorem okuyamaWajimaPrintedExtensionStatement
    (G : Type) [Group G] [Finite G] :
    OkuyamaWajimaPrintedExtensionStatement (p := p) G :=
  okuyamaWajimaPrintedExtensionStatement_of_canonicalAssembly
    okuyamaWajimaPrintedCanonicalAssemblyInput_automatic G

end McKayConjecture
