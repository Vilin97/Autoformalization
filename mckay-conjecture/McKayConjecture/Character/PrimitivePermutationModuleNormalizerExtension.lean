/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerPrimitiveNormalizerExtensionCriterion
import McKayConjecture.Character.PermutationModuleBrauerNormalizerExtension

/-!
# Primitive permutation modules and Brauer normalizer extensions

For a module with a finite permutation basis, the endomorphism Brauer
comparison is already an isomorphism.  Consequently a faithful action
has a full Brauer-normalizer extension, independently of any
primitivity hypothesis.

This file records the two bridges needed by the residue-Dade
interface.  First, forgetting the conjugation certificate gives the
required fixed-unit homomorphism extension.  Second, if a Dade
structure on the same endomorphism algebra is Brauer-primitive, the
primitive normalizer criterion reconstructs the full extension from
that homomorphism.

Brauer-primitivity also forces the ordinary module Brauer quotient to
be a line in this permutation setting.  Thus no separate cap-line
hypothesis is needed: it follows from the endomorphism comparison and
the one-dimensionality of the primitive Dade-algebra quotient.
-/

noncomputable section

namespace Representation
namespace PermutationModuleBasis

variable {p : ℕ} [Fact p.Prime]
variable {k P V ι : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [MulAction P ι] [Finite ι]

variable (B : PermutationModuleBasis
  (k := k) (P := P) (V := V) (ι := ι))

noncomputable local instance primitivePermutationGroupFintype :
    Fintype P :=
  Fintype.ofFinite P

local instance primitivePermutationConjugationAction :
    MulSemiringAction P (Module.End k V) :=
  endomorphismConjugationMulSemiringAction
    (representationLinearAction
      (Representation.ofDistribMulAction k P V))

local instance primitivePermutationConjugationScalarComm :
    SMulCommClass P k (Module.End k V) :=
  endomorphismConjugation_smulCommClass
    (representationLinearAction
      (Representation.ofDistribMulAction k P V))

/-- The full permutation-module normalizer extension, with its
conjugation certificate forgotten, supplies exactly the homomorphism
field required by the primitive residue-Dade interface. -/
theorem hasBrauerNormalizerHomExtension_of_faithfulPermutationBasis
    (hP : IsPGroup p P)
    (hfaithful : Function.Injective B.representation) :
    HasBrauerNormalizerHomExtension (k := k)
      (representationInteriorAction B.representation) :=
  Nonempty.map
    BrauerNormalizerExtension.toHomExtension
    (B.hasBrauerNormalizerExtension_of_faithfulPermutationBasis
      hP hfaithful)

/-- If the conjugation endomorphism algebra carries a
Brauer-primitive Dade structure, the ordinary Brauer quotient of a
permutation module is automatically one-dimensional.

The endomorphism comparison identifies the primitive algebra quotient
with the endomorphism algebra of the module quotient.  Its dimension
is therefore the square of the module-quotient dimension, and a
natural number whose square is one is itself one. -/
theorem finrank_brauerQuotient_eq_one_of_isBrauerPrimitive
    (S : DadeAlgebra p k P (Module.End k V))
    (hprimitive : S.IsBrauerPrimitive) :
    Module.finrank k (BrauerQuotient B.representation) = 1 := by
  let hcomparison :=
    B.endomorphismBrauerComparisonIsomorphism_of_permutationBasis
      S.isPGroup
  letI : Module.Finite k (BrauerQuotient B.representation) :=
    Module.Finite.of_basis
      (B.brauerQuotientFixedBasis S.isPGroup)
  have hend :
      Module.finrank k
          (Module.End k (BrauerQuotient B.representation)) =
        1 := by
    calc
      Module.finrank k
          (Module.End k (BrauerQuotient B.representation)) =
          Module.finrank k
            (BrauerQuotientAlgebra
              (k := k) (P := P) (A := Module.End k V)) :=
        (endomorphismBrauerAlgEquiv
          B.representation hcomparison).toLinearEquiv.finrank_eq.symm
      _ = 1 :=
        (S.finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive).2
          hprimitive
  rw [Module.finrank_linearMap] at hend
  exact Nat.dvd_one.mp ⟨_, hend.symm⟩

/-- Primitive-permutation bridge in the form used downstream: a
faithful permutation action and a Brauer-primitive Dade structure on
its endomorphism algebra have a full Brauer-normalizer extension.

The proof deliberately passes through the smaller homomorphism datum
to expose that the primitive criterion makes conjugation compatibility
automatic.  (The permutation comparison in fact supplies the full
extension even without `hprimitive`.) -/
theorem hasBrauerNormalizerExtension_of_faithfulPermutationBasis_of_isBrauerPrimitive
    (S : DadeAlgebra p k P (Module.End k V))
    (hfaithful : Function.Injective B.representation)
    (hprimitive : S.IsBrauerPrimitive) :
    HasBrauerNormalizerExtension (k := k)
      (representationInteriorAction B.representation) := by
  apply
    S.hasBrauerNormalizerExtension_of_isBrauerPrimitive
      (representationInteriorAction B.representation)
      (representationInteriorAction_unit_injective
        B.representation hfaithful)
      hprimitive
  exact
    B.hasBrauerNormalizerHomExtension_of_faithfulPermutationBasis
      S.isPGroup hfaithful

end PermutationModuleBasis
end Representation
