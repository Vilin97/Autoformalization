/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionOkuyamaWajimaCharacterInertiaGlaubermanAutomatic
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionOrdinaryCardinalityReduction

/-!
# Automatic ordinary inertia-fibre cardinalities

The canonical source-level Okuyama--Wajima assembly supplies the uniform
extension comparison inside the exact inertia group of each source
character.  The exact-inertia transport then counts the two normal-copy
fibres.  Finally, the standard inertia-triple equivalences relabel those
normal-copy fibres as the ordinary inertia fibres used by the
central-intersection reduction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CliffordEquivalence
open CliffordCorrespondence
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The automatic exact-inertia count in the ordinary inertia-fibre
coordinates used by the Proposition-4.5 cardinality reduction. -/
theorem productAmbientGlaubermanOrdinaryInertiaFibre_natCard_eq_automatic
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    Nat.card
        (IrreducibleCharactersOverInertia
          (product S C) theta.1) =
      Nat.card
        (IrreducibleCharactersOverInertia
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C
            (complementCharacterEquivOfGlauberman
              S C hcentral g) theta).1) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let phi :=
    internalTheorem44CharacterEquiv
      S C
      (complementCharacterEquivOfGlauberman
        S C hcentral g) theta
  calc
    Nat.card
        (IrreducibleCharactersOverInertia
          (product S C) theta.1) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (inertiaNormalCopy (product S C) theta.1).subtype
          (productAmbientGlaubermanLeftInertiaTheta
            S C hgenerate theta).1) :=
      Nat.card_congr
        (irreducibleCharactersOverInertiaEquivTriple
          (product S C) theta.1)
    _ =
      Nat.card
        (IrreducibleCharactersOverAlong
          (ProductAmbientGlaubermanRightNormalCopy
            S C hcentral hgenerate g theta).subtype
          (inertiaCopyCharacter
            (internalProductNormalizer S C)
            (productAmbientGlaubermanRightKernelTransportCharacter
              S C hcentral g theta))) :=
      productAmbientGlaubermanLeftOW_natCard_eq_rightInertia_automatic
        S C hcentral hgenerate g theta
    _ =
      Nat.card
        (IrreducibleCharactersOverInertia
          (internalProductNormalizer S C) phi.1) :=
      (Nat.card_congr
        (irreducibleCharactersOverInertiaEquivTriple
          (internalProductNormalizer S C) phi.1)).symm

end Proposition45

open Proposition45

/-- The global ordinary inertia-fibre cardinality hypothesis required by
the central-intersection reduction is unconditional. -/
theorem
    centralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
    (q : ℕ) [Fact q.Prime] :
    CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
      q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  intro theta
  exact
    productAmbientGlaubermanOrdinaryInertiaFibre_natCard_eq_automatic
      S C hcentral hgenerate g theta

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
