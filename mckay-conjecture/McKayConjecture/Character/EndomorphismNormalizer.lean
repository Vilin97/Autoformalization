/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ProjectiveNormalizerCorrection
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Interior normalizer units as linear automorphisms

When the interior algebra is an endomorphism algebra, its units are the
general linear group.  This file transports the corrected normalizer
homomorphism to an honest linear action.
-/

noncomputable section

namespace Representation

variable {k P H V : Type}
variable [Field k] [Group P] [Fintype P] [Group H]
variable [AddCommGroup V] [Module k V]
variable [MulSemiringAction P (Module.End k V)]
variable [SMulCommClass P k (Module.End k V)]

namespace InteriorAction

variable (I : InteriorAction (P := P) (A := Module.End k V))

/-- Interpret a unit of an endomorphism-algebra normalizer as a linear
automorphism of the underlying module. -/
def normalizerLinearEquiv :
    I.unitNormalizer →* (V ≃ₗ[k] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom.comp
    I.unitNormalizer.subtype

omit [Fintype P] [SMulCommClass P k (Module.End k V)] in
@[simp]
theorem normalizerLinearEquiv_toLinearMap
    (n : I.unitNormalizer) :
    (I.normalizerLinearEquiv n : Module.End k V) =
      (n : (Module.End k V)ˣ) := by
  exact
    LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap
      (n : (Module.End k V)ˣ)

omit [Fintype P] [SMulCommClass P k (Module.End k V)] in
@[simp]
theorem normalizerLinearEquiv_apply
    (n : I.unitNormalizer) (v : V) :
    I.normalizerLinearEquiv n v =
      (((n : (Module.End k V)ˣ) : Module.End k V)) v :=
  rfl

omit [Fintype P] in
/-- Scalar normalizer units act by the expected scalar linear
automorphisms. -/
theorem normalizerLinearEquiv_scalarUnitNormalizer
    (z : kˣ) :
    I.normalizerLinearEquiv
        (I.scalarUnitNormalizer (k := k) z) =
      DistribMulAction.toModuleAut k V z := by
  apply LinearEquiv.ext
  intro v
  rfl

end InteriorAction

namespace ProjectiveNormalizerLift

variable
  {I : InteriorAction (P := P) (A := Module.End k V)}
  (T : ProjectiveNormalizerLift (k := k) (H := H) I)
  (E : BrauerNormalizerExtension (k := k) I)
  (Z : BrauerScalarIdentification
    (k := k) (P := P) (A := Module.End k V))

/-- The corrected normalizer homomorphism, viewed as an honest linear
action. -/
def correctedLinearAction : H →* (V ≃ₗ[k] V) :=
  I.normalizerLinearEquiv.comp (T.correctedHom E Z)

@[simp]
theorem correctedLinearAction_apply
    (g : H) (v : V) :
    T.correctedLinearAction E Z g v =
      (((I.scalarUnitNormalizer
            (k := k) (T.brauerScalar E Z g)⁻¹ *
          T.operator g : I.unitNormalizer) :
        (Module.End k V)ˣ) : Module.End k V) v :=
  rfl

end ProjectiveNormalizerLift
end Representation
