/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismBrauerNormalizerAction

/-!
# The endomorphism Brauer comparison isomorphism

The natural algebra homomorphism

`End(V)(P) → End(V(P))`

was constructed in `EndomorphismBrauerHom`.  This file names its
bijectivity property and packages the resulting canonical algebra
equivalence.  Proving the property for the capped endopermutation
modules in Dade theory is a separate, substantive theorem.
-/

noncomputable section

namespace Representation

variable {k P V : Type}
variable [Field k] [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]

/-- The natural endomorphism Brauer homomorphism is an isomorphism. -/
def EndomorphismBrauerComparisonIsomorphism
    (ρ : Representation k P V) : Prop :=
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  Function.Bijective (endomorphismBrauerAlgHom ρ)

/-- Canonical algebra equivalence obtained from a proof of the
endomorphism Brauer comparison theorem. -/
def endomorphismBrauerAlgEquiv
    (ρ : Representation k P V)
    (h : EndomorphismBrauerComparisonIsomorphism ρ) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    BrauerQuotientAlgebra
        (k := k) (P := P) (A := Module.End k V) ≃ₐ[k]
      Module.End k (BrauerQuotient ρ) := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  exact AlgEquiv.ofBijective
    (endomorphismBrauerAlgHom ρ) h

@[simp]
theorem endomorphismBrauerAlgEquiv_apply
    (ρ : Representation k P V)
    (h : EndomorphismBrauerComparisonIsomorphism ρ) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    ∀ x :
        BrauerQuotientAlgebra
          (k := k) (P := P) (A := Module.End k V),
      endomorphismBrauerAlgEquiv ρ h x =
        endomorphismBrauerAlgHom ρ x := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  intro x
  rfl

end Representation
