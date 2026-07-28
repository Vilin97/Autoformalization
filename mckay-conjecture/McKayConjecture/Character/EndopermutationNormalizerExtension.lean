/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismBrauerNormalizerExtension
import McKayConjecture.Character.EndopermutationModule

/-!
# A comparison criterion for endopermutation normalizer extensions

This file specializes the endomorphism Brauer comparison construction
to the linear action carried by a pointed endopermutation module.  It
isolates a useful sufficient criterion: for a faithful action, the
canonical comparison isomorphism immediately supplies the
Brauer-normalizer extension.

The general Puig--Turull theorem still requires Dade's local-extension
argument when this direct module Brauer comparison is unavailable.
-/

noncomputable section

namespace Representation

variable
  {p k P V}
  [Fact p.Prime]
  [Field k] [CharP k p]
  [Group P] [Fintype P]
  [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V]

namespace PointedEndopermutationModule

/-- The direct endomorphism Brauer comparison property for the
representation underlying a pointed endopermutation module. -/
def HasEndomorphismBrauerComparison
    (M : PointedEndopermutationModule p k P V) : Prop :=
  EndomorphismBrauerComparisonIsomorphism
    (linearActionRepresentation M.action)

omit [Fact p.Prime] [CharP k p]
  [FiniteDimensional k V] [Nontrivial V] in
/-- A faithful pointed endopermutation module satisfying the direct
endomorphism Brauer comparison has a Brauer-normalizer extension. -/
theorem hasBrauerNormalizerExtension_of_comparison
    (M : PointedEndopermutationModule p k P V)
    (hfaithful : Function.Injective M.action)
    (hcomparison : M.HasEndomorphismBrauerComparison) :
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
  exact
    hasBrauerNormalizerExtension_of_endomorphismComparison
      (linearActionRepresentation M.action)
      (linearActionRepresentation_injective M.action hfaithful)
      hcomparison

end PointedEndopermutationModule
end Representation
