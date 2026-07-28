/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InnerAutomorphism
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientPPrimeCharacterEnumeration
import McKayConjecture.InductiveMcKay.AlternatingSixTwoAmbientRowMatching

/-!
# The two-local ambient character enumeration and transported row actions

A completed thirty-one-row ordinary character table turns the arithmetic
odd-dimensional ambient row subtype into an actual complete enumeration of
the ambient `2'`-degree irreducible characters.  This file proves that bridge
and transports the genuine `SylowAutStabilizer` actions back to the two
explicit finite row types.

The central-block row-order matching is proved equivariant under the inner
stabilizer elements supplied by the exact normalizer.  Full stabilizer
equivariance, including outer automorphisms, remains an explicit proposition.
No projective-row compatibility is asserted.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoAmbientCharacterBridgeFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The ambient row reached by applying a genuine Sylow-two stabilizer
automorphism to the character enumerated by a completed ambient table. -/
def alternatingSixAmbientTwoPPrimeRowIndexAction
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 2))
    (r : AlternatingSixAmbientPPrimeRowIndex 2) :
    AlternatingSixAmbientPPrimeRowIndex 2 :=
  (alternatingSixAmbientPPrimeCharacterEquiv T 2).symm
    (a • alternatingSixAmbientPPrimeCharacterEquiv T 2 r)

/-- The concrete local row reached by applying the restricted genuine
Sylow-two stabilizer automorphism to the enumerated actual-normalizer
character. -/
def alternatingSixTwoConcreteNormalizerRowAction
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 2))
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    AlternatingSixTwoConcreteNormalizerRow :=
  alternatingSixTwoActualNormalizerPPrimeCharacterEquiv.symm
    (a • alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r)

@[simp]
theorem alternatingSixAmbientTwoPPrimeRowIndexAction_one
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (r : AlternatingSixAmbientPPrimeRowIndex 2) :
    alternatingSixAmbientTwoPPrimeRowIndexAction T 1 r = r := by
  simp [alternatingSixAmbientTwoPPrimeRowIndexAction]

theorem alternatingSixAmbientTwoPPrimeRowIndexAction_mul
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a b :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 2))
    (r : AlternatingSixAmbientPPrimeRowIndex 2) :
    alternatingSixAmbientTwoPPrimeRowIndexAction T (a * b) r =
      alternatingSixAmbientTwoPPrimeRowIndexAction T a
        (alternatingSixAmbientTwoPPrimeRowIndexAction T b r) := by
  simp [alternatingSixAmbientTwoPPrimeRowIndexAction, mul_smul]

@[simp]
theorem alternatingSixTwoConcreteNormalizerRowAction_one
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    alternatingSixTwoConcreteNormalizerRowAction 1 r = r := by
  simp [alternatingSixTwoConcreteNormalizerRowAction]

theorem alternatingSixTwoConcreteNormalizerRowAction_mul
    (a b :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 2))
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    alternatingSixTwoConcreteNormalizerRowAction (a * b) r =
      alternatingSixTwoConcreteNormalizerRowAction a
        (alternatingSixTwoConcreteNormalizerRowAction b r) := by
  simp [alternatingSixTwoConcreteNormalizerRowAction, mul_smul]

/-- Ambient automorphisms preserve the matrix dimension attached to the
transported arithmetic row. -/
theorem alternatingSixAmbientTwoPPrimeRowIndexAction_dimension
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 2))
    (r : AlternatingSixAmbientPPrimeRowIndex 2) :
    (alternatingSixAmbientTwoPPrimeRowIndexAction T a r).1.dimension =
      r.1.dimension := by
  have hcharacters :
      alternatingSixAmbientPPrimeCharacterEquiv T 2
          (alternatingSixAmbientTwoPPrimeRowIndexAction T a r) =
        a • alternatingSixAmbientPPrimeCharacterEquiv T 2 r := by
    simp [alternatingSixAmbientTwoPPrimeRowIndexAction]
  calc
    (alternatingSixAmbientTwoPPrimeRowIndexAction T a r).1.dimension =
        (alternatingSixAmbientPPrimeCharacterEquiv T 2
          (alternatingSixAmbientTwoPPrimeRowIndexAction T a r)).1.degree := by
      rw [alternatingSixAmbientPPrimeCharacterEquiv_degree]
    _ = (a • alternatingSixAmbientPPrimeCharacterEquiv T 2 r).1.degree := by
      rw [hcharacters]
    _ = (alternatingSixAmbientPPrimeCharacterEquiv T 2 r).1.degree := by
      rfl
    _ = r.1.dimension :=
      alternatingSixAmbientPPrimeCharacterEquiv_degree T 2 r

/-- Full row-index equivariance of the central-block row-order matching.
This proposition is exactly the remaining ordinary-table action check; it
does not include any projective comparison. -/
def AlternatingSixTwoCentralBlockRowMatchingEquivariant
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) : Prop :=
  ∀
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 2))
    (r : AlternatingSixAmbientPPrimeRowIndex 2),
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        (alternatingSixAmbientTwoPPrimeRowIndexAction T a r) =
      alternatingSixTwoConcreteNormalizerRowAction a
        (alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
          r)

/-- Conjugation by one element of the exact normalizer, regarded as an
element of the ambient Sylow stabilizer. -/
def alternatingSixTwoNormalizerInnerSylowAutStabilizer
    (g :
      SylowNormalizer
        (alternatingSixUniversalCoverSylow 2)) :
    SylowAutStabilizer
      (alternatingSixUniversalCoverSylow 2) :=
  ⟨MulAut.conj g.1, by
    rw [SylowAutStabilizer.mem_iff]
    apply Sylow.ext
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp g.2⟩

@[simp]
theorem alternatingSixTwoNormalizerInnerSylowAutStabilizer_coe
    (g :
      SylowNormalizer
        (alternatingSixUniversalCoverSylow 2)) :
    (alternatingSixTwoNormalizerInnerSylowAutStabilizer g).1 =
      MulAut.conj g.1 :=
  rfl

/-- Restricting the ambient inner stabilizer to the exact normalizer is
conjugation by the same normalizer element. -/
@[simp]
theorem alternatingSixTwo_normalizerRestrictionHom_inner
    (g :
      SylowNormalizer
        (alternatingSixUniversalCoverSylow 2)) :
    SylowAutStabilizer.normalizerRestrictionHom
        (alternatingSixUniversalCoverSylow 2)
        (alternatingSixTwoNormalizerInnerSylowAutStabilizer g) =
      MulAut.conj g := by
  apply DFunLike.ext _ _
  intro x
  apply Subtype.ext
  rfl

/-- Every arithmetic ambient row is fixed by the inner stabilizer coming
from the exact normalizer. -/
@[simp]
theorem alternatingSixAmbientTwoPPrimeRowIndexAction_inner
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (g :
      SylowNormalizer
        (alternatingSixUniversalCoverSylow 2))
    (r : AlternatingSixAmbientPPrimeRowIndex 2) :
    alternatingSixAmbientTwoPPrimeRowIndexAction T
        (alternatingSixTwoNormalizerInnerSylowAutStabilizer g) r =
      r := by
  simp [alternatingSixAmbientTwoPPrimeRowIndexAction,
    alternatingSixTwoNormalizerInnerSylowAutStabilizer]

/-- Every concrete local row is fixed by the inner stabilizer coming from
the exact normalizer. -/
@[simp]
theorem alternatingSixTwoConcreteNormalizerRowAction_inner
    (g :
      SylowNormalizer
        (alternatingSixUniversalCoverSylow 2))
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    alternatingSixTwoConcreteNormalizerRowAction
        (alternatingSixTwoNormalizerInnerSylowAutStabilizer g) r =
      r := by
  apply alternatingSixTwoActualNormalizerPPrimeCharacterEquiv.injective
  simp only [alternatingSixTwoConcreteNormalizerRowAction,
    Equiv.apply_symm_apply]
  change
    SylowAutStabilizer.normalizerRestrictionHom
          (alternatingSixUniversalCoverSylow 2)
          (alternatingSixTwoNormalizerInnerSylowAutStabilizer g) •
        alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r =
      alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r
  rw [alternatingSixTwo_normalizerRestrictionHom_inner,
    pPrime_conj_smul]

/-- The central-block row-order matching is genuinely equivariant on the
inner part of the Sylow stabilizer. -/
theorem
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_inner_equivariant
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (g :
      SylowNormalizer
        (alternatingSixUniversalCoverSylow 2))
    (r : AlternatingSixAmbientPPrimeRowIndex 2) :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        (alternatingSixAmbientTwoPPrimeRowIndexAction T
          (alternatingSixTwoNormalizerInnerSylowAutStabilizer g) r) =
      alternatingSixTwoConcreteNormalizerRowAction
        (alternatingSixTwoNormalizerInnerSylowAutStabilizer g)
        (alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
          r) := by
  simp

/-- A completed ambient ordinary table plus the still-explicit
full-stabilizer equivariance check supplies the concrete two-local ordinary
character-table certificate.  Equivariance on the inner normalizer image
was proved above; no quotient-representative reduction of the remaining
quantifier is claimed here.  Projective rows remain separate obligations in
the downstream endpoint. -/
def alternatingSixTwoConcreteCharacterTableCertificateOfAmbientTable
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hequivariant :
      AlternatingSixTwoCentralBlockRowMatchingEquivariant T) :
    AlternatingSixTwoConcreteCharacterTableCertificate
      (AlternatingSixAmbientPPrimeRowIndex 2) where
  ambientEnumeration :=
    alternatingSixAmbientPPrimeCharacterEquiv T 2
  indexEquiv :=
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
  indexEquivariance := by
    intro a r
    exact hequivariant a r

end InductiveMcKay
end McKayConjecture
