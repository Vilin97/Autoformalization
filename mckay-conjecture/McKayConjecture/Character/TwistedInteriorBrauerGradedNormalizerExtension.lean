/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerPrimitiveNormalizerExtensionCriterion
import McKayConjecture.Character.TwistedInteriorBrauerGradedCollapse
import McKayConjecture.Character.TwistedInteriorBrauerSubgroupCollapse

/-!
# Normalizer extensions from a graded Brauer collapse

This file connects the automorphism-graded collapse criterion to the
existing Puig--Turull normalizer-extension interfaces.  The collapse
always gives the homomorphism part.  When the ordinary Brauer quotient
is one-dimensional, the existing scalar-conjugation argument upgrades
it to a full normalizer extension.  In particular, this applies to a
Brauer-primitive Dade algebra.
-/

noncomputable section

namespace Representation
namespace InteriorAction
namespace TwistedBrauerGradedCollapse

variable {k P A : Type}
variable [Field k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

variable {I : InteriorAction (P := P) (A := A)}

/-- A normalized multiplicative collapse of the automorphism-graded
Brauer family supplies the entire homomorphism part of the
Puig--Turull normalizer extension. -/
def toBrauerNormalizerHomExtension
    (C : I.TwistedBrauerGradedCollapse (k := k))
    (hI : Function.Injective I.unit) :
    BrauerNormalizerHomExtension (k := k) I where
  hom := C.unitNormalizerUnitsHom hI
  extends_fixedUnit :=
    C.unitNormalizerUnitsHom_comp_fixedUnitToNormalizer hI

/-- Proposition-level reduction from an automorphism-graded collapse
to a Brauer normalizer homomorphism extension. -/
theorem hasBrauerNormalizerHomExtension_of_collapse
    (hI : Function.Injective I.unit)
    (hcollapse :
      Nonempty (I.TwistedBrauerGradedCollapse (k := k))) :
    HasBrauerNormalizerHomExtension (k := k) I :=
  hcollapse.map (fun C ↦ C.toBrauerNormalizerHomExtension hI)

/-- If the ordinary Brauer quotient is one-dimensional, a graded
collapse yields a full Puig--Turull normalizer extension. -/
def toBrauerNormalizerExtensionOfFinrankOne
    (C : I.TwistedBrauerGradedCollapse (k := k))
    (hI : Function.Injective I.unit)
    (hfin :
      Module.finrank k
          (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
        1) :
    BrauerNormalizerExtension (k := k) I :=
  brauerNormalizerExtensionOfHomExtension
    I hI hfin (C.toBrauerNormalizerHomExtension hI)

/-- Existence form of the one-dimensional upgrade. -/
theorem hasBrauerNormalizerExtension_of_collapse_of_finrank_eq_one
    (hI : Function.Injective I.unit)
    (hfin :
      Module.finrank k
          (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
        1)
    (hcollapse :
      Nonempty (I.TwistedBrauerGradedCollapse (k := k))) :
    HasBrauerNormalizerExtension (k := k) I :=
  hcollapse.map
    (fun C ↦
      C.toBrauerNormalizerExtensionOfFinrankOne hI hfin)

end TwistedBrauerGradedCollapse

namespace TwistedBrauerSubgroupCollapse

variable {k P A : Type}
variable [Field k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

variable {I : InteriorAction (P := P) (A := A)}

/-- A collapse over precisely the automorphisms induced by normalizer
units supplies the homomorphism part of the Puig--Turull extension. -/
def toBrauerNormalizerHomExtensionOfNormalizerActionRange
    (hI : Function.Injective I.unit)
    (C : NormalizerActionRangeCollapse (I := I) (k := k) hI) :
    BrauerNormalizerHomExtension (k := k) I where
  hom := C.unitNormalizerUnitsHom hI
  extends_fixedUnit :=
    C.unitNormalizerUnitsHom_comp_fixedUnitToNormalizer hI

/-- Proposition-level form of the sharp induced-action-range
criterion. -/
theorem hasBrauerNormalizerHomExtension_of_normalizerActionRangeCollapse
    (hI : Function.Injective I.unit)
    (hcollapse :
      Nonempty
        (NormalizerActionRangeCollapse (I := I) (k := k) hI)) :
    HasBrauerNormalizerHomExtension (k := k) I :=
  hcollapse.map
    (fun C ↦
      C.toBrauerNormalizerHomExtensionOfNormalizerActionRange hI)

/-- In the one-dimensional case, a collapse over the induced
normalizer-action subgroup yields a full normalizer extension. -/
def toBrauerNormalizerExtensionOfNormalizerActionRange
    (hI : Function.Injective I.unit)
    (C : NormalizerActionRangeCollapse (I := I) (k := k) hI)
    (hfin :
      Module.finrank k
          (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
        1) :
    BrauerNormalizerExtension (k := k) I :=
  brauerNormalizerExtensionOfHomExtension
    I hI hfin
      (C.toBrauerNormalizerHomExtensionOfNormalizerActionRange hI)

/-- Existence form of the sharp one-dimensional range criterion. -/
theorem hasBrauerNormalizerExtension_of_normalizerActionRangeCollapse_of_finrank_eq_one
    (hI : Function.Injective I.unit)
    (hfin :
      Module.finrank k
          (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
        1)
    (hcollapse :
      Nonempty
        (NormalizerActionRangeCollapse (I := I) (k := k) hI)) :
    HasBrauerNormalizerExtension (k := k) I :=
  hcollapse.map
    (fun C ↦
      C.toBrauerNormalizerExtensionOfNormalizerActionRange
        hI hfin)

end TwistedBrauerSubgroupCollapse
end InteriorAction

namespace DadeAlgebra

open InteriorAction.TwistedBrauerSubgroupCollapse

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [CharP k p] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- For a Brauer-primitive Dade algebra, it suffices to collapse the
twisted components indexed by automorphisms actually induced by
normalizer units. -/
theorem hasBrauerNormalizerExtension_of_isBrauerPrimitive_of_normalizerActionRangeCollapse
    (S : DadeAlgebra p k P A)
    (I : InteriorAction (P := P) (A := A))
    (hI : Function.Injective I.unit)
    (hprimitive : S.IsBrauerPrimitive)
    (hcollapse :
      Nonempty
        (NormalizerActionRangeCollapse
          (I := I) (k := k) hI)) :
    HasBrauerNormalizerExtension (k := k) I := by
  apply
    S.hasBrauerNormalizerExtension_of_isBrauerPrimitive
      I hI hprimitive
  exact
    hasBrauerNormalizerHomExtension_of_normalizerActionRangeCollapse
      (I := I) hI hcollapse

/-- For a Brauer-primitive Dade algebra, an automorphism-graded
collapse supplies a full Puig--Turull normalizer extension. -/
theorem hasBrauerNormalizerExtension_of_isBrauerPrimitive_of_collapse
    (S : DadeAlgebra p k P A)
    (I : InteriorAction (P := P) (A := A))
    (hI : Function.Injective I.unit)
    (hprimitive : S.IsBrauerPrimitive)
    (hcollapse :
      Nonempty (I.TwistedBrauerGradedCollapse (k := k))) :
    HasBrauerNormalizerExtension (k := k) I := by
  apply
    S.hasBrauerNormalizerExtension_of_isBrauerPrimitive
      I hI hprimitive
  exact
    InteriorAction.TwistedBrauerGradedCollapse.hasBrauerNormalizerHomExtension_of_collapse
      (I := I) hI hcollapse

end DadeAlgebra
end Representation
