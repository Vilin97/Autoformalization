/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraBrauerDimensionCriterion
import McKayConjecture.Character.EndopermutationNormalizerExtension

/-!
# Brauer-primitive endopermutation modules with a cap line

For a pointed endopermutation module `M`, Brauer-primitivity says that
the Brauer quotient of `End(M)` is one-dimensional.  This does not by
itself identify that quotient with the endomorphism algebra of the
ordinary module Brauer quotient.

This file isolates an explicit additional cap hypothesis: the ordinary
Brauer quotient of the underlying linear representation is a line.
Under these two dimension-one hypotheses, the canonical endomorphism
Brauer homomorphism is automatically an isomorphism.  For a faithful
action, the existing comparison construction then gives the
Puig--Turull normalizer extension.

`HasBrauerCapLine` is deliberately stronger and more explicit than
`EndopermutationModule.IsCapped`: the latter only asserts that the
endomorphism-algebra Brauer quotient is nonzero.
-/

noncomputable section

namespace Representation
namespace PointedEndopermutationModule

private theorem algHom_bijective_of_finrank_eq_one
    {k R S : Type}
    [Field k]
    [Ring R] [Algebra k R]
    [Ring S] [Algebra k S]
    (hR : Module.finrank k R = 1)
    (hS : Module.finrank k S = 1)
    (f : R →ₐ[k] S) :
    Function.Bijective f := by
  letI : FiniteDimensional k R :=
    FiniteDimensional.of_finrank_eq_succ hR
  letI : FiniteDimensional k S :=
    FiniteDimensional.of_finrank_eq_succ hS
  letI : Nontrivial R :=
    Module.nontrivial_of_finrank_pos (by
      rw [hR]
      exact Nat.zero_lt_one)
  letI : Nontrivial S :=
    Module.nontrivial_of_finrank_pos (by
      rw [hS]
      exact Nat.zero_lt_one)
  have hf_ne : f.toLinearMap ≠ 0 := by
    intro hf
    have hone : f.toLinearMap 1 = 0 := by
      rw [hf]
      rfl
    change f 1 = 0 at hone
    rw [map_one] at hone
    exact one_ne_zero hone
  have hsurjective : Function.Surjective f.toLinearMap :=
    surjective_of_nonzero_of_finrank_eq_one hS hf_ne
  have hinjective : Function.Injective f.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hR.trans hS.symm)).2 hsurjective
  exact ⟨hinjective, hsurjective⟩

variable
  {p k P V}
  [Fact p.Prime]
  [Field k] [CharP k p]
  [Group P] [Fintype P]
  [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V]

/-- The Dade algebra used by the direct endomorphism Brauer comparison.
Its action is reconstructed from the representation associated to
`M.action`; the round-trip theorem identifies this action with the
original one. -/
def comparisonDadeAlgebra
    (M : PointedEndopermutationModule p k P V) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction
          (linearActionRepresentation M.action))
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction
          (linearActionRepresentation M.action))
    DadeAlgebra p k P (Module.End k V) := by
  rw [representationLinearAction_linearActionRepresentation]
  exact M.toDadeAlgebra

/-- Brauer-primitivity of the Dade algebra `End(M)`, expressed without
exposing the locally installed conjugation-action instances. -/
def IsBrauerPrimitive
    (M : PointedEndopermutationModule p k P V) : Prop := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction
        (linearActionRepresentation M.action))
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction
        (linearActionRepresentation M.action))
  exact M.comparisonDadeAlgebra.IsBrauerPrimitive

/-- The explicit cap-line hypothesis used in this file: the ordinary
Brauer quotient of the underlying linear representation has dimension
one. -/
def HasBrauerCapLine
    (M : PointedEndopermutationModule p k P V) : Prop :=
  Module.finrank k
      (BrauerQuotient
        (linearActionRepresentation M.action)) =
    1

/-- The two local hypotheses which force the direct endomorphism
Brauer comparison: a unique fixed endomorphism-basis index and a
one-dimensional ordinary Brauer quotient. -/
def HasPrimitiveBrauerCap
    (M : PointedEndopermutationModule p k P V) : Prop :=
  M.IsBrauerPrimitive ∧ M.HasBrauerCapLine

/-- Brauer-primitivity of `M` is exactly one-dimensionality of the
Brauer quotient of its endomorphism algebra. -/
theorem isBrauerPrimitive_iff_finrank_endomorphismBrauerQuotient_eq_one
    (M : PointedEndopermutationModule p k P V) :
    M.IsBrauerPrimitive ↔
      letI :=
        endomorphismConjugationMulSemiringAction
          (representationLinearAction
            (linearActionRepresentation M.action))
      letI :=
        endomorphismConjugation_smulCommClass
          (representationLinearAction
            (linearActionRepresentation M.action))
      Module.finrank k
          (BrauerQuotientAlgebra
            (k := k) (P := P) (A := Module.End k V)) =
        1 := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction
        (linearActionRepresentation M.action))
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction
        (linearActionRepresentation M.action))
  exact
    (DadeAlgebra.finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive
      M.comparisonDadeAlgebra).symm

/-- A primitive cap makes the canonical map
`End(M)(P) → End(M(P))` an algebra isomorphism.

The proof uses only the two dimension-one statements.  The map is
nonzero because it preserves `1`, hence it is surjective onto the
one-dimensional target; equality of finite dimensions then gives
injectivity. -/
theorem endomorphismBrauerComparisonIsomorphism_of_primitiveCap
    (M : PointedEndopermutationModule p k P V)
    (hcap : M.HasPrimitiveBrauerCap) :
    M.HasEndomorphismBrauerComparison := by
  change
    EndomorphismBrauerComparisonIsomorphism
      (linearActionRepresentation M.action)
  unfold EndomorphismBrauerComparisonIsomorphism
  have hmodule :
      Module.finrank k
          (BrauerQuotient
            (linearActionRepresentation M.action)) =
        1 := by
    exact hcap.2
  letI :
      FiniteDimensional k
        (BrauerQuotient
          (linearActionRepresentation M.action)) :=
    FiniteDimensional.of_finrank_eq_succ hmodule
  letI :
      Nontrivial
        (BrauerQuotient
          (linearActionRepresentation M.action)) :=
    Module.nontrivial_of_finrank_pos (by
      rw [hmodule]
      exact Nat.zero_lt_one)
  have htarget :
      Module.finrank k
          (Module.End k
            (BrauerQuotient
              (linearActionRepresentation M.action))) =
        1 := by
    rw [Module.finrank_linearMap, hmodule]
  refine
    algHom_bijective_of_finrank_eq_one
      (f := endomorphismBrauerAlgHom
        (linearActionRepresentation M.action)) ?_ htarget
  exact
    (M.isBrauerPrimitive_iff_finrank_endomorphismBrauerQuotient_eq_one).1
      hcap.1

/-- Explicit normalizer-extension data obtained from a faithful
Brauer-primitive pointed endopermutation module with a cap line. -/
def brauerNormalizerExtensionOfPrimitiveCap
    (M : PointedEndopermutationModule p k P V)
    (hfaithful : Function.Injective M.action)
    (hcap : M.HasPrimitiveBrauerCap) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction
          (linearActionRepresentation M.action))
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction
          (linearActionRepresentation M.action))
    BrauerNormalizerExtension (k := k)
      (representationInteriorAction
        (linearActionRepresentation M.action)) :=
  brauerNormalizerExtensionOfEndomorphismComparison
    (linearActionRepresentation M.action)
    (linearActionRepresentation_injective M.action hfaithful)
    (M.endomorphismBrauerComparisonIsomorphism_of_primitiveCap
      hcap)

/-- Proposition form of the primitive-cap normalizer-extension
criterion. -/
theorem hasBrauerNormalizerExtension_of_primitiveCap
    (M : PointedEndopermutationModule p k P V)
    (hfaithful : Function.Injective M.action)
    (hcap : M.HasPrimitiveBrauerCap) :
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
        (linearActionRepresentation M.action)) :=
  ⟨M.brauerNormalizerExtensionOfPrimitiveCap
    hfaithful hcap⟩

end PointedEndopermutationModule
end Representation
