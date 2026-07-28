/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import
  McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45QuotientFactorInduction

/-!
# The quotient-factor character in Proposition 4.5

This file keeps the character-level central-index specialization separate
from the group and factor-set identifications.  For a character in the left
inertia-triple fibre, full central-index induction constructs an actual
prime-to-`q` irreducible character in the normalizer of the Sylow lift, with
the inverse coefficient scalar built into its subtype.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open ComplementReduction
open GroupTheory
open NormalSubgroupAssociatedFactorFibre
open NormalSubgroupFactorNormalizerFibre

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The bounded local-data provider obtained from the ambient central-index
induction hypothesis.  Naming it prevents the dependent choice term from
being repeatedly expanded in the concrete factor construction. -/
def productAmbientGlaubermanCentralIndexLocalProvider
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex X →
          ∀ Q : Sylow q Y,
            Nonempty (LocalInductiveMcKayData Q)) :
    CentralIndexBoundedLocalProvider q (centralIndex X) :=
  fun Y _ _ hY Q ↦ Classical.choice (ih Y hY Q)

/-- An opaque name for the source character fibre, used to keep concrete
Clifford-copy terms out of later declaration signatures. -/
def ProductAmbientGlaubermanLeftQuotientCharactersOver
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) : Type :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  PPrimeCharactersOver
    (productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta) q

/-- An opaque name for the exact inverse-coefficient normalizer fibre. -/
def ProductAmbientGlaubermanLeftQuotientFactorNormalizerFibre
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) : Type :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let T :=
    productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta
  NormalizerInverseCoefficientFibre T
    (productAmbientGlaubermanLeftOuterQuotientSylow
      S C hgenerate theta)

/-- The fixed associated-factor correspondence applied before normalizer
induction. -/
def productAmbientGlaubermanLeftQuotientFactorImage
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (chi :
      ProductAmbientGlaubermanLeftQuotientCharactersOver
        S C hgenerate theta) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let T :=
    productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta
  pPrimeCharacterEquiv Fact.out T
    (productAmbientGlaubermanLeftInertiaTriple_character_isPPrimeDegree
      S C hgenerate theta) chi

/-- The same associated-factor image, reordered into the central-scalar
fibre expected by normalizer induction. -/
def productAmbientGlaubermanLeftQuotientFactorCentralScalarImage
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (chi :
      ProductAmbientGlaubermanLeftQuotientCharactersOver
        S C hgenerate theta) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let T :=
    productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta
  inverseCoefficientCentralScalarEquiv T
    (productAmbientGlaubermanLeftQuotientFactorImage
      S C hgenerate theta chi)

/-- The full local inductive-McKay datum on the Sylow lift supplied by the
ambient central-index hypothesis.  Together with
`pPrimeCharacterEquivOfCentralIndexIH`, this is the actual datum used to
construct the inverse-coefficient normalizer character. -/
def productAmbientGlaubermanLeftQuotientFactorLocalDataOfCentralIndexIH
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex X →
          ∀ Q : Sylow q Y,
            Nonempty (LocalInductiveMcKayData Q))
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (hCnoncentral :
      ¬C ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let T :=
    productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta
  let Q :=
    productAmbientGlaubermanLeftOuterQuotientSylow
      S C hgenerate theta
  Classical.choice
    (ih (ExtensionGroup T)
      (productAmbientGlaubermanLeftQuotientFactorExtension_centralIndex_lt
        S C hgenerate hCnoncentral theta)
      (LiftedSylow T Q))

/-- The scalar-preserving correspondence on the canonical quotient factor
extension supplied by central-index induction.  It is named separately from
its application below so that the concrete Proposition 4.5 parameters do not
force Lean to elaborate the whole three-stage character equivalence at once. -/
def productAmbientGlaubermanLeftQuotientFactorScalarCorrespondenceOfCentralIndexIH
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex X →
          ∀ Q : Sylow q Y,
            Nonempty (LocalInductiveMcKayData Q))
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (hCnoncentral :
      ¬C ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let T :=
    productAmbientGlaubermanLeftInertiaTriple
      S C hgenerate theta
  let Q :=
    productAmbientGlaubermanLeftOuterQuotientSylow
      S C hgenerate theta
  centralScalarCorrespondenceOfCentralIndexIH
    ih
    (ExtensionGroup T)
    (productAmbientGlaubermanLeftQuotientFactorExtension_centralIndex_lt
      S C hgenerate hCnoncentral theta)
    (LiftedSylow T Q)
    (CoefficientSubgroup T)
    (coefficientSubgroup_le_center T)
    (InverseCoefficientScalar T)

/-- The actual prime-to-`q` normalizer character obtained from the
Proposition 4.5 left quotient factor character by central-index induction.
This is the output that still has to be identified with an extension of the
matched right normal character. -/
def productAmbientGlaubermanLeftQuotientFactorNormalizerImageOfCentralIndexIH
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex X →
          ∀ Q : Sylow q Y,
            Nonempty (LocalInductiveMcKayData Q))
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (hCnoncentral :
      ¬C ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (chi :
      ProductAmbientGlaubermanLeftQuotientCharactersOver
        S C hgenerate theta) :=
  productAmbientGlaubermanLeftQuotientFactorScalarCorrespondenceOfCentralIndexIH
    S C ih hgenerate hCnoncentral theta
    (productAmbientGlaubermanLeftQuotientFactorCentralScalarImage
      S C hgenerate theta chi)

/-- The irreducible-character component of the quotient-factor normalizer
image. -/
def productAmbientGlaubermanLeftQuotientFactorNormalizerCharacterOfCentralIndexIH
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex X →
          ∀ Q : Sylow q Y,
            Nonempty (LocalInductiveMcKayData Q))
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (hCnoncentral :
      ¬C ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (chi :
      ProductAmbientGlaubermanLeftQuotientCharactersOver
        S C hgenerate theta) :=
  (productAmbientGlaubermanLeftQuotientFactorNormalizerImageOfCentralIndexIH
    S C ih hgenerate hCnoncentral theta chi).1.1

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
