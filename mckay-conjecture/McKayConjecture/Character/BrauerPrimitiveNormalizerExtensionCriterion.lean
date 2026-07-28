/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerScalarIdentificationFinrankOne
import McKayConjecture.Character.DadeAlgebraBrauerDimensionCriterion
import McKayConjecture.Character.DadeNormalizerExtension
import McKayConjecture.Character.EndopermutationBrauerPrimitiveCap
import McKayConjecture.Character.InteriorNormalizerBrauerAction

/-!
# The remaining normalizer-extension datum for a primitive Brauer quotient

When the algebra Brauer quotient is one-dimensional, every algebra
automorphism of it is the identity and every element is scalar.  Hence
the conjugation-compatibility clause in `BrauerNormalizerExtension` is
automatic.  The only remaining datum is a group homomorphism on the
interior unit normalizer extending the Brauer map on fixed units.

This file packages that smaller datum and proves that it is equivalent
to a full Brauer-normalizer extension when the interior action is
faithful and the Brauer quotient is one-dimensional.  For a
Brauer-primitive Dade algebra, one-dimensionality follows from the
fixed-index criterion.  Thus the genuinely additional Puig--Turull
input in the primitive case is precisely the extension of the
fixed-unit character; no separate conjugation hypothesis is needed.
-/

noncomputable section

namespace Representation

variable {k P A : Type}
variable [Field k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- The homomorphism part of a Brauer-normalizer extension, without a
separate conjugation-compatibility field. -/
structure BrauerNormalizerHomExtension
    (I : InteriorAction (P := P) (A := A)) where
  /-- The unit-valued homomorphism on the interior normalizer. -/
  hom :
    I.unitNormalizer →*
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A))ˣ
  /-- On fixed units, the homomorphism is induced by the Brauer
  projection. -/
  extends_fixedUnit :
    hom.comp (I.fixedUnitToNormalizer (k := k)) =
      fixedUnitBrauerProjection (k := k) (P := P) (A := A)

/-- Existence of the homomorphism part of a Brauer-normalizer
extension. -/
def HasBrauerNormalizerHomExtension
    (I : InteriorAction (P := P) (A := A)) : Prop :=
  Nonempty (BrauerNormalizerHomExtension (k := k) I)

namespace BrauerNormalizerExtension

/-- Forget the conjugation-compatibility certificate in a full
Brauer-normalizer extension. -/
def toHomExtension
    {I : InteriorAction (P := P) (A := A)}
    (E : BrauerNormalizerExtension (k := k) I) :
    BrauerNormalizerHomExtension (k := k) I where
  hom := E.hom
  extends_fixedUnit := E.extends_fixedUnit

end BrauerNormalizerExtension

private theorem algEquiv_eq_refl_of_finrank_eq_one
    {R : Type} [Ring R] [Algebra k R]
    (hfin : Module.finrank k R = 1)
    (e : R ≃ₐ[k] R) :
    e = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  let scalarEquiv : k ≃ₐ[k] R :=
    AlgEquiv.ofBijective
      (Algebra.ofId k R)
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfin)
  obtain ⟨a, rfl⟩ := scalarEquiv.surjective x
  exact e.commutes a

private theorem unit_conjugation_eq_self_of_finrank_eq_one
    {R : Type} [Ring R] [Algebra k R]
    (hfin : Module.finrank k R = 1)
    (u : Rˣ) (x : R) :
    (↑(u⁻¹) : R) * x * (u : R) = x := by
  let scalarEquiv : k ≃ₐ[k] R :=
    AlgEquiv.ofBijective
      (Algebra.ofId k R)
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfin)
  obtain ⟨a, rfl⟩ := scalarEquiv.surjective x
  change
    (↑(u⁻¹) : R) * algebraMap k R a * (u : R) =
      algebraMap k R a
  rw [← Algebra.commutes]
  simp

/-- On a one-dimensional algebra Brauer quotient, a faithful
normalizer acts trivially. -/
theorem InteriorAction.normalizerConjBrauerAlgEquiv_eq_refl_of_finrank_eq_one
    (I : InteriorAction (P := P) (A := A))
    (hI : Function.Injective I.unit)
    (hfin :
      Module.finrank k
          (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
        1)
    (s : I.unitNormalizer) :
    I.normalizerConjBrauerAlgEquiv (k := k) hI s =
      AlgEquiv.refl :=
  algEquiv_eq_refl_of_finrank_eq_one hfin _

/-- For a faithful interior action with a one-dimensional algebra
Brauer quotient, the homomorphism part automatically extends to full
Puig--Turull normalizer-extension data. -/
def brauerNormalizerExtensionOfHomExtension
    (I : InteriorAction (P := P) (A := A))
    (hI : Function.Injective I.unit)
    (hfin :
      Module.finrank k
          (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
        1)
    (E : BrauerNormalizerHomExtension (k := k) I) :
    BrauerNormalizerExtension (k := k) I where
  hom := E.hom
  extends_fixedUnit := E.extends_fixedUnit
  conjugation_compatible := by
    intro s c
    refine
      ⟨I.normalizerConjFixedAlgEquiv (k := k) s c,
        rfl, ?_⟩
    rw [unit_conjugation_eq_self_of_finrank_eq_one hfin]
    rw [← I.normalizerConjBrauerAlgEquiv_brauerAlgebraProjection
      hI s c]
    rw [I.normalizerConjBrauerAlgEquiv_eq_refl_of_finrank_eq_one
      hI hfin s]
    rfl

/-- In the faithful one-dimensional case, asking for the homomorphism
part is equivalent to asking for a full Brauer-normalizer extension. -/
theorem hasBrauerNormalizerExtension_iff_hasBrauerNormalizerHomExtension
    (I : InteriorAction (P := P) (A := A))
    (hI : Function.Injective I.unit)
    (hfin :
      Module.finrank k
          (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
        1) :
    HasBrauerNormalizerExtension (k := k) I ↔
      HasBrauerNormalizerHomExtension (k := k) I := by
  constructor
  · exact Nonempty.map
      BrauerNormalizerExtension.toHomExtension
  · rintro ⟨E⟩
    exact
      ⟨brauerNormalizerExtensionOfHomExtension
        I hI hfin E⟩

namespace DadeAlgebra

variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- For a Brauer-primitive Dade algebra, the full normalizer-extension
problem is exactly the problem of extending the fixed-unit Brauer
character to the interior unit normalizer. -/
theorem hasBrauerNormalizerExtension_iff_hasHomExtension_of_isBrauerPrimitive
    (S : DadeAlgebra p k P A)
    (I : InteriorAction (P := P) (A := A))
    (hI : Function.Injective I.unit)
    (hprimitive : S.IsBrauerPrimitive) :
    HasBrauerNormalizerExtension (k := k) I ↔
      HasBrauerNormalizerHomExtension (k := k) I := by
  apply
    hasBrauerNormalizerExtension_iff_hasBrauerNormalizerHomExtension
      I hI
  exact
    (S.finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive).2
      hprimitive

/-- Proposition form of the primitive normalizer-extension criterion:
the only additional premise is the fixed-unit character extension. -/
theorem hasBrauerNormalizerExtension_of_isBrauerPrimitive
    (S : DadeAlgebra p k P A)
    (I : InteriorAction (P := P) (A := A))
    (hI : Function.Injective I.unit)
    (hprimitive : S.IsBrauerPrimitive)
    (hhom : HasBrauerNormalizerHomExtension (k := k) I) :
    HasBrauerNormalizerExtension (k := k) I :=
  (S.hasBrauerNormalizerExtension_iff_hasHomExtension_of_isBrauerPrimitive
    I hI hprimitive).2 hhom

end DadeAlgebra

namespace PointedEndopermutationModule

variable
  {p : ℕ} [Fact p.Prime] [CharP k p]
  {V : Type}
  [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V]

/-- For a faithful Brauer-primitive pointed endopermutation module,
the sole additional normalizer-extension premise is a homomorphism
extending the Brauer map on fixed units.  In particular, no ordinary
Brauer-cap-line hypothesis is needed for the conjugation clause. -/
theorem hasBrauerNormalizerExtension_of_isBrauerPrimitive_of_homExtension
    (M : PointedEndopermutationModule p k P V)
    (hfaithful : Function.Injective M.action)
    (hprimitive : M.IsBrauerPrimitive)
    (hhom :
      letI :=
        endomorphismConjugationMulSemiringAction
          (representationLinearAction
            (linearActionRepresentation M.action))
      letI :=
        endomorphismConjugation_smulCommClass
          (representationLinearAction
            (linearActionRepresentation M.action))
      HasBrauerNormalizerHomExtension (k := k)
        (representationInteriorAction
          (linearActionRepresentation M.action))) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction
          (linearActionRepresentation M.action))
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction
          (linearActionRepresentation M.action))
    HasBrauerNormalizerExtension (k := k)
      (representationInteriorAction
        (linearActionRepresentation M.action)) := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction
        (linearActionRepresentation M.action))
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction
        (linearActionRepresentation M.action))
  let I :=
    representationInteriorAction
      (linearActionRepresentation M.action)
  have hI : Function.Injective I.unit :=
    representationInteriorAction_unit_injective
      (linearActionRepresentation M.action)
      (linearActionRepresentation_injective M.action hfaithful)
  exact
    M.comparisonDadeAlgebra.hasBrauerNormalizerExtension_of_isBrauerPrimitive
      I hI hprimitive hhom

end PointedEndopermutationModule
end Representation
