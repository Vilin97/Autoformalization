/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanStrongRealization
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionFactorMatchedFibreEquivalence
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanExistence

/-!
# Canonical product Glauberman correspondence

The restriction-multiplicity characterization makes the classical
Glauberman correspondence unique.  In the central-intersection reduction
it is therefore enough to construct the Dade--Glauberman--Nagao comparison
for one correspondence; the public statement, which quantifies over every
packaged correspondence, follows automatically.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction

open ComplementReduction
open Proposition45

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The canonical product Glauberman correspondence, selected from its
unconditional existence theorem. -/
def canonicalProductGlaubermanCorrespondence
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    ProductGlaubermanCorrespondence S C hcentral :=
  Classical.choice
    (exists_productGlaubermanCorrespondence S C hcentral)

local instance productKernelConjugationAction
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    MulDistribMulAction
      (productSylow S C :
        Subgroup (product S C))
      (productPPrimeKernel S C hcentral) :=
  subgroupConjugationMulDistribMulAction
    (productPPrimeKernel S C hcentral)
    (productSylow S C :
      Subgroup (product S C))

/-- The canonical ordinary product correspondence has a canonical strong
action realization. -/
def canonicalProductStrongActionGlaubermanCorrespondence
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    StrongActionGlaubermanCorrespondence
      (productSylow S C :
        Subgroup (product S C))
      (productPPrimeKernel S C hcentral)
      q :=
  Classical.choose
    (GlaubermanCorrespondence.exists_strongActionRealization
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C))
      (productSylow S C).isPGroup'
      (productPPrimeKernel_isPPrimeGroup
        S C hcentral)
      (canonicalProductGlaubermanCorrespondence
        S C hcentral))

/-- Transporting the canonical strong action realization back to ambient
subgroups gives the canonical ordinary product correspondence. -/
theorem
    canonicalProductStrongActionGlaubermanCorrespondence_realizes
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    glaubermanCorrespondenceOfStrongConjugationAction
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))
        (canonicalProductStrongActionGlaubermanCorrespondence
          S C hcentral) =
      canonicalProductGlaubermanCorrespondence
        S C hcentral :=
  Classical.choose_spec
    (GlaubermanCorrespondence.exists_strongActionRealization
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C))
      (productSylow S C).isPGroup'
      (productPPrimeKernel_isPPrimeGroup
        S C hcentral)
      (canonicalProductGlaubermanCorrespondence
        S C hcentral))

/-- Every packaged product Glauberman correspondence is the canonical
one. -/
theorem productGlaubermanCorrespondence_eq_canonical
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral) :
    g = canonicalProductGlaubermanCorrespondence
      S C hcentral :=
  Subsingleton.elim _ _

/-- Agreement for the canonical product correspondence implies agreement
for every packaged correspondence. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_canonical
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (hcanonical :
      ∀ theta :
          PPrimeIrreducibleCharacter
            (product S C) q,
        ProductAmbientGlaubermanProjectiveObstructionClassAgreement
          S C hcentral hgenerate
          (canonicalProductGlaubermanCorrespondence
            S C hcentral)
          theta)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta := by
  rw [
    productGlaubermanCorrespondence_eq_canonical
      S C hcentral g]
  exact hcanonical theta

/-- Global Dade--Glauberman--Nagao agreement only needs to be proved for
the canonical product correspondence. -/
theorem
    productAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis_of_canonical
    (h :
      ∀ (X : Type) [Group X] [Finite X]
        (S : Sylow q X) (C : Subgroup X)
        (hCnormal : C.Normal)
        (hcentral :
          C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
        (hgenerate :
          C ⊔ Subgroup.normalizer (S : Set X) = ⊤),
          letI : C.Normal := hCnormal
          ∀ theta :
              PPrimeIrreducibleCharacter
                (product S C) q,
            ProductAmbientGlaubermanProjectiveObstructionClassAgreement
              S C hcentral hgenerate
              (canonicalProductGlaubermanCorrespondence
                S C hcentral)
              theta) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis
      q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  exact
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_canonical
      S C hcentral hgenerate
      (h X S C hCnormal hcentral hgenerate)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
