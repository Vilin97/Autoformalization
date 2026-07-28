/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InteriorAlgebra

/-!
# Extensions of the Brauer map to an interior normalizer

For an interior Dade algebra, Puig--Turull's normalizer-extension
theorem constructs a homomorphism

`N_{Aˣ}(P) → A(P)ˣ`

whose restriction to units of `A^P` is the Brauer projection.  This is
the deep Dade-theoretic input used to turn a projective crossed
representation into a magic representation.

This file packages the exact extension datum.  It also exposes both
unit maps explicitly, so later cocycle cancellation can be proved
without any ambiguity about coercions.
-/

noncomputable section

namespace Representation

variable {k P A : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- Map on units induced by the Brauer projection `A^P → A(P)`. -/
def fixedUnitBrauerProjection :
    (fixedSubalgebra (k := k) (P := P) (A := A))ˣ →*
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A))ˣ :=
  Units.map
    (brauerAlgebraProjection
      (k := k) (P := P) (A := A)).toMonoidHom

@[simp]
theorem coe_fixedUnitBrauerProjection
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    (fixedUnitBrauerProjection
        (k := k) (P := P) (A := A) u :
      BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
    brauerAlgebraProjection (k := k) (P := P) (A := A) u :=
  rfl

/-- A homomorphic extension of the Brauer map from fixed units to the
whole interior normalizer. -/
structure BrauerNormalizerExtension
    (I : InteriorAction (P := P) (A := A)) where
  /-- The normalizer homomorphism. -/
  hom :
    I.unitNormalizer →*
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A))ˣ
  /-- On fixed units, `hom` is the unit map induced by the Brauer
  projection. -/
  extends_fixedUnit :
    hom.comp
        (I.fixedUnitToNormalizer (k := k)) =
      fixedUnitBrauerProjection (k := k) (P := P) (A := A)
  /-- Conjugation by a normalizer unit descends through the extension.
  This is the second conclusion of the Puig--Turull theorem:
  `br(c) ^ hom(s) = br(c ^ s)`. -/
  conjugation_compatible :
    ∀ (s : I.unitNormalizer)
      (c : fixedSubalgebra (k := k) (P := P) (A := A)),
      ∃ c' : fixedSubalgebra (k := k) (P := P) (A := A),
        (c' : A) =
            (↑(((s : Aˣ)⁻¹)) : A) * (c : A) *
              (s : Aˣ) ∧
          (↑((hom s)⁻¹) :
              BrauerQuotientAlgebra
                (k := k) (P := P) (A := A)) *
                brauerAlgebraProjection
                  (k := k) (P := P) (A := A) c *
              (hom s :
                BrauerQuotientAlgebra
                  (k := k) (P := P) (A := A)) =
            brauerAlgebraProjection
              (k := k) (P := P) (A := A) c'

namespace BrauerNormalizerExtension

variable
  {I : InteriorAction (P := P) (A := A)}
  (E : BrauerNormalizerExtension (k := k) I)

@[simp]
theorem hom_fixedUnitToNormalizer
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    E.hom (I.fixedUnitToNormalizer (k := k) u) =
      fixedUnitBrauerProjection (k := k) (P := P) (A := A) u :=
  congrArg (fun f ↦ f u) E.extends_fixedUnit

/-- Explicit form of compatibility with conjugation on the fixed
algebra. -/
theorem exists_fixedConjugate
    (s : I.unitNormalizer)
    (c : fixedSubalgebra (k := k) (P := P) (A := A)) :
    ∃ c' : fixedSubalgebra (k := k) (P := P) (A := A),
      (c' : A) =
          (↑(((s : Aˣ)⁻¹)) : A) * (c : A) *
            (s : Aˣ) ∧
        (↑((E.hom s)⁻¹) :
            BrauerQuotientAlgebra
              (k := k) (P := P) (A := A)) *
              brauerAlgebraProjection
                (k := k) (P := P) (A := A) c *
            (E.hom s :
              BrauerQuotientAlgebra
                (k := k) (P := P) (A := A)) =
          brauerAlgebraProjection
            (k := k) (P := P) (A := A) c' :=
  E.conjugation_compatible s c

end BrauerNormalizerExtension

/-- Proposition asserting the Puig--Turull extension theorem for one
specified interior action. -/
def HasBrauerNormalizerExtension
    (I : InteriorAction (P := P) (A := A)) : Prop :=
  Nonempty (BrauerNormalizerExtension (k := k) I)

end Representation
