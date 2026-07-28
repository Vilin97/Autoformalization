/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerScalarIdentificationFinrankOne
import McKayConjecture.Character.EndomorphismBrauerNormalizerExtension
import McKayConjecture.Character.PermutationModuleBrauerFinrankOne
import McKayConjecture.Character.PermutationModuleEndomorphismBrauerComparison

/-!
# Brauer normalizer extensions for faithful permutation modules

For a faithful representation with a permutation basis, the
endomorphism Brauer comparison supplies the Puig--Turull normalizer
extension.  If the basis action has a unique fixed index, the module
Brauer quotient is one-dimensional, hence so is the Brauer quotient of
the endomorphism algebra.  Its scalar units then have the canonical
identification with the coefficient-field units.
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

local notation "Fix" =>
  MulAction.fixedPoints P ι

noncomputable local instance permutationNormalizerGroupFintype :
    Fintype P :=
  Fintype.ofFinite P

local instance permutationNormalizerConjugationAction :
    MulSemiringAction P (Module.End k V) :=
  endomorphismConjugationMulSemiringAction
    (representationLinearAction
      (Representation.ofDistribMulAction k P V))

local instance permutationNormalizerConjugationScalarComm :
    SMulCommClass P k (Module.End k V) :=
  endomorphismConjugation_smulCommClass
    (representationLinearAction
      (Representation.ofDistribMulAction k P V))

/-- A faithful permutation representation has a Brauer normalizer
extension. -/
theorem hasBrauerNormalizerExtension_of_faithfulPermutationBasis
    (hP : IsPGroup p P)
    (hfaithful : Function.Injective B.representation) :
    HasBrauerNormalizerExtension (k := k)
      (representationInteriorAction B.representation) :=
  hasBrauerNormalizerExtension_of_endomorphismComparison
    B.representation hfaithful
    (B.endomorphismBrauerComparisonIsomorphism_of_permutationBasis hP)

/-- Explicit normalizer-extension data for a faithful permutation
representation. -/
def brauerNormalizerExtensionOfFaithfulPermutationBasis
    (hP : IsPGroup p P)
    (hfaithful : Function.Injective B.representation) :
    BrauerNormalizerExtension (k := k)
      (representationInteriorAction B.representation) :=
  brauerNormalizerExtensionOfEndomorphismComparison
    B.representation hfaithful
    (B.endomorphismBrauerComparisonIsomorphism_of_permutationBasis hP)

include B

/-- If the basis action has a unique fixed index, the Brauer quotient
of the endomorphism algebra is one-dimensional. -/
theorem finrank_endomorphismBrauerQuotientAlgebra_eq_one
    (hP : IsPGroup p P)
    [Unique Fix] :
    Module.finrank k
        (BrauerQuotientAlgebra
          (k := k) (P := P) (A := Module.End k V)) =
      1 := by
  let hcomparison :=
    B.endomorphismBrauerComparisonIsomorphism_of_permutationBasis hP
  letI :
      Module.Finite k (BrauerQuotient B.representation) :=
    Module.Finite.of_basis
      (B.brauerQuotientFixedBasis hP)
  calc
    Module.finrank k
        (BrauerQuotientAlgebra
          (k := k) (P := P) (A := Module.End k V)) =
        Module.finrank k
          (Module.End k (BrauerQuotient B.representation)) :=
      (endomorphismBrauerAlgEquiv
        B.representation hcomparison).toLinearEquiv.finrank_eq
    _ =
        Module.finrank k (BrauerQuotient B.representation) *
          Module.finrank k (BrauerQuotient B.representation) :=
      Module.finrank_linearMap k k
        (BrauerQuotient B.representation)
        (BrauerQuotient B.representation)
    _ = 1 := by
      rw [B.finrank_brauerQuotient_eq_one hP]

/-- Pointed form of the preceding theorem: a specified fixed index and
a subsingleton fixed-point type force the endomorphism-algebra Brauer
quotient to have dimension one. -/
theorem finrank_endomorphismBrauerQuotientAlgebra_eq_one_of_subsingleton
    (hP : IsPGroup p P)
    (i : Fix)
    [Subsingleton Fix] :
    Module.finrank k
        (BrauerQuotientAlgebra
          (k := k) (P := P) (A := Module.End k V)) =
      1 := by
  letI : Unique Fix :=
    { default := i
      uniq := fun j ↦ Subsingleton.elim j i }
  exact B.finrank_endomorphismBrauerQuotientAlgebra_eq_one hP

/-- Canonical scalar-unit identification for the one-dimensional
endomorphism-algebra Brauer quotient. -/
def endomorphismBrauerScalarIdentification
    (hP : IsPGroup p P)
    [Unique Fix] :
    BrauerScalarIdentification
      (k := k) (P := P) (A := Module.End k V) :=
  brauerScalarIdentificationOfFinrankOne
    (B.finrank_endomorphismBrauerQuotientAlgebra_eq_one hP)

/-- Pointed/subsingleton form of the canonical scalar identification. -/
def endomorphismBrauerScalarIdentificationOfSubsingleton
    (hP : IsPGroup p P)
    (i : Fix)
    [Subsingleton Fix] :
    BrauerScalarIdentification
      (k := k) (P := P) (A := Module.End k V) :=
  brauerScalarIdentificationOfFinrankOne
    (B.finrank_endomorphismBrauerQuotientAlgebra_eq_one_of_subsingleton
      hP i)

/-- The two pieces of data used by the normalizer-correction
construction, bundled for a faithful permutation representation with a
unique fixed basis index. -/
def brauerNormalizerExtensionAndScalarIdentification
    (hP : IsPGroup p P)
    (hfaithful : Function.Injective B.representation)
    [Unique Fix] :
    BrauerNormalizerExtension (k := k)
        (representationInteriorAction B.representation) ×
      BrauerScalarIdentification
        (k := k) (P := P) (A := Module.End k V) :=
  (B.brauerNormalizerExtensionOfFaithfulPermutationBasis
      hP hfaithful,
    B.endomorphismBrauerScalarIdentification hP)

end PermutationModuleBasis
end Representation
