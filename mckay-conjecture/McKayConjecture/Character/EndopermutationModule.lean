/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismCentralSimple
import McKayConjecture.Character.EndomorphismInteriorAction

/-!
# Pointed endopermutation modules

An endopermutation module is a linear action whose conjugation action on
its endomorphism algebra admits a stable permutation basis.  The pointed
form used here carries a stable basis containing the identity endomorphism.
It is exactly the constructive form needed to make the endomorphism algebra
a Dade algebra.
-/

noncomputable section

namespace Representation

variable (p : ℕ) [Fact p.Prime]
variable (k P V : Type)
variable [Field k] [CharP k p]
variable [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V] [Nontrivial V]

/-- A pointed endopermutation module for a finite `p`-group. -/
structure PointedEndopermutationModule where
  /-- The linear action on the module. -/
  action : P →* (V ≃ₗ[k] V)
  /-- The acting group is a `p`-group. -/
  isPGroup : IsPGroup p P
  /-- The endomorphism algebra has a stable basis containing its identity. -/
  permutationBasis :
    letI :=
      endomorphismConjugationMulSemiringAction action
    letI :=
      endomorphismConjugation_smulCommClass action
    PointedPermutationAlgebraBasis
      (k := k) (P := P) (A := Module.End k V)

namespace PointedEndopermutationModule

variable
  {p k P V}
  [hp : Fact p.Prime]
  [hk : Field k] [hchar : CharP k p]
  [hP : Group P] [hPfin : Fintype P]
  [hV : AddCommGroup V] [hmod : Module k V]
  [hVfin : FiniteDimensional k V] [hVne : Nontrivial V]

set_option linter.overlappingInstances false in
/-- The endomorphism algebra of a pointed endopermutation module, with its
conjugation action, is a Dade algebra. -/
def toDadeAlgebra
    (M : PointedEndopermutationModule p k P V) :
    letI :=
      endomorphismConjugationMulSemiringAction M.action
    letI :=
      endomorphismConjugation_smulCommClass M.action
    DadeAlgebra p k P (Module.End k V) := by
  letI :=
    endomorphismConjugationMulSemiringAction M.action
  letI :=
    endomorphismConjugation_smulCommClass M.action
  exact
    { isCentral := inferInstance
      isSimple := endomorphism_isSimpleRing
      finiteDimensional := inferInstance
      isPGroup := M.isPGroup
      permutationBasis := M.permutationBasis }

set_option linter.overlappingInstances false in
/-- The canonical interior action attached to a pointed endopermutation
module. -/
def interiorAction
    (M : PointedEndopermutationModule p k P V) :
    letI :=
      endomorphismConjugationMulSemiringAction M.action
    InteriorAction (P := P) (A := Module.End k V) := by
  letI :=
    endomorphismConjugationMulSemiringAction M.action
  exact interiorActionOfLinearAction M.action

end PointedEndopermutationModule
end Representation
