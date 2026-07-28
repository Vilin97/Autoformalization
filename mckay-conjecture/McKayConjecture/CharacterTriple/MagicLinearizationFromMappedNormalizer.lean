/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraBrauerDimensionCriterion
import McKayConjecture.Character.ProjectiveNormalizerCorrection
import McKayConjecture.CharacterTriple.MagicLinearizationFromScalarCorrection

/-!
# Magic linearization from a mapped normalizer factor

The Brauer-normalizer theorem is naturally modular, whereas the
projective multiplicity action in ordinary character theory is over
characteristic zero.  The normalizer correction still crosses this
coefficient boundary once two concrete pieces of data are supplied:

* a homomorphism from the modular scalar units to the target scalar
  units;
* equality between the target projective factor and the image of the
  modular normalizer-lift factor.

Applying the Brauer-normalizer extension gives a modular scalar
cochain.  Mapping that cochain to the target field splits the target
factor, and the coefficient-independent scalar-correction construction
then gives a magic linearization.

The final section specializes the construction to a Brauer-primitive
Dade algebra for an abelian `p`-group.  Brauer-primitivity supplies the
scalar identification automatically, so the only remaining
cross-characteristic input is the explicit factor comparison.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {k K P A G V : Type}
variable [Field k] [Field K]
variable [Fintype P] [Group G]
variable [Ring A] [Algebra k A]
variable [AddCommGroup V] [Module K V]

section General

variable [Group P]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- Map the scalar cochain furnished by a Brauer-normalizer correction
to a second coefficient field. -/
def mappedBrauerScalar
    {I : InteriorAction (P := P) (A := A)}
    (T : ProjectiveNormalizerLift (k := k) (H := G) I)
    (E : BrauerNormalizerExtension (k := k) I)
    (Z : BrauerScalarIdentification
      (k := k) (P := P) (A := A))
    (ι : kˣ →* Kˣ)
    (g : G) :
    Kˣ :=
  ι (T.brauerScalar E Z g)

@[simp]
theorem mappedBrauerScalar_one
    {I : InteriorAction (P := P) (A := A)}
    (T : ProjectiveNormalizerLift (k := k) (H := G) I)
    (E : BrauerNormalizerExtension (k := k) I)
    (Z : BrauerScalarIdentification
      (k := k) (P := P) (A := A))
    (ι : kˣ →* Kˣ) :
    mappedBrauerScalar T E Z ι 1 = 1 := by
  change
    ι (Z.equiv.symm (E.hom (T.operator 1))) = 1
  rw [T.operator_one, map_one, map_one, map_one]

/-- The mapped Brauer scalar splits any target factor identified with
the image of the normalizer-lift factor. -/
theorem mappedBrauerScalar_mul
    (Q : ProjectiveRepresentation K G V)
    {I : InteriorAction (P := P) (A := A)}
    (T : ProjectiveNormalizerLift (k := k) (H := G) I)
    (E : BrauerNormalizerExtension (k := k) I)
    (Z : BrauerScalarIdentification
      (k := k) (P := P) (A := A))
    (ι : kˣ →* Kˣ)
    (factor_compatibility :
      ∀ g h,
        ι (T.factor g h) =
          Q.factor g h)
    (g h : G) :
    mappedBrauerScalar T E Z ι g *
        mappedBrauerScalar T E Z ι h =
      Q.factor g h *
        mappedBrauerScalar T E Z ι (g * h) := by
  calc
    mappedBrauerScalar T E Z ι g *
        mappedBrauerScalar T E Z ι h =
      ι (T.brauerScalar E Z g *
        T.brauerScalar E Z h) :=
      (ι.map_mul
        (T.brauerScalar E Z g)
        (T.brauerScalar E Z h)).symm
    _ =
      ι (T.factor g h *
        T.brauerScalar E Z (g * h)) := by
          rw [T.brauerScalar_mul]
    _ =
      Q.factor g h *
        mappedBrauerScalar T E Z ι (g * h) := by
          rw [ι.map_mul, factor_compatibility]
          rfl

/-- A Brauer-normalizer extension over `k` magic-linearizes a
normalized projective action over `K` once its factor is the image of
the normalizer-lift factor. -/
def magicLinearizationOfMappedNormalizerFactor
    (Q : ProjectiveRepresentation K G V)
    (hQ : Q.IsNormalized)
    {I : InteriorAction (P := P) (A := A)}
    (T : ProjectiveNormalizerLift (k := k) (H := G) I)
    (E : BrauerNormalizerExtension (k := k) I)
    (Z : BrauerScalarIdentification
      (k := k) (P := P) (A := A))
    (ι : kˣ →* Kˣ)
    (factor_compatibility :
      ∀ g h,
        ι (T.factor g h) =
          Q.factor g h) :
    MagicLinearization Q :=
  magicLinearizationOfScalarCorrection Q hQ
    (mappedBrauerScalar T E Z ι)
    (mappedBrauerScalar_one T E Z ι)
    (mappedBrauerScalar_mul Q T E Z ι
      factor_compatibility)

end General

section DadeAlgebra

variable {p : ℕ} [Fact p.Prime]
variable [CharP k p] [CommGroup P]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- For a Brauer-primitive Dade algebra of an abelian `p`-group, the
normalizer extension and a mapped factor comparison give a magic
linearization over any target field.  The scalar Brauer identification
is derived from primitivity rather than supplied separately. -/
def magicLinearizationOfMappedPrimitiveDadeNormalizer
    (Q : ProjectiveRepresentation K G V)
    (hQ : Q.IsNormalized)
    (S : DadeAlgebra p k P A)
    (hprimitive : S.IsBrauerPrimitive)
    (I : InteriorAction (P := P) (A := A))
    (T : ProjectiveNormalizerLift (k := k) (H := G) I)
    (E : BrauerNormalizerExtension (k := k) I)
    (ι : kˣ →* Kˣ)
    (factor_compatibility :
      ∀ g h,
        ι (T.factor g h) =
          Q.factor g h) :
    MagicLinearization Q :=
  magicLinearizationOfMappedNormalizerFactor Q hQ T E
    (brauerScalarIdentificationOfFinrankOne
      ((S.finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive).2
        hprimitive))
    ι factor_compatibility

/-- Nonempty (proposition-valued) form of the abelian Dade
normalizer-extension input.  This adapter makes the choice of extension
data internally and exposes only the mathematically invariant existence
statement. -/
def magicLinearizationOfMappedPrimitiveDadeHasNormalizerExtension
    (Q : ProjectiveRepresentation K G V)
    (hQ : Q.IsNormalized)
    (S : DadeAlgebra p k P A)
    (hprimitive : S.IsBrauerPrimitive)
    (I : InteriorAction (P := P) (A := A))
    (T : ProjectiveNormalizerLift (k := k) (H := G) I)
    (hE : HasBrauerNormalizerExtension (k := k) I)
    (ι : kˣ →* Kˣ)
    (factor_compatibility :
      ∀ g h,
        ι (T.factor g h) =
          Q.factor g h) :
    MagicLinearization Q :=
  magicLinearizationOfMappedPrimitiveDadeNormalizer
    Q hQ S hprimitive I T (Classical.choice hE)
      ι factor_compatibility

end DadeAlgebra

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
