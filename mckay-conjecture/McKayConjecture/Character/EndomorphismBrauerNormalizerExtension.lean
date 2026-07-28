/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeNormalizerExtension
import McKayConjecture.Character.EndomorphismBrauerComparison
import McKayConjecture.Character.InteriorNormalizerConjugation

/-!
# A normalizer extension from the endomorphism Brauer comparison

For a faithful representation, the interior normalizer acts honestly
on the module Brauer quotient.  If the canonical comparison

`End(V)(P) → End(V(P))`

is an isomorphism, transporting this action back produces the desired
homomorphic extension of the algebra Brauer map.  Thus the construction
in this file reduces the Puig--Turull extension theorem to the
Dade-specific endomorphism comparison theorem.
-/

noncomputable section

namespace Representation

variable {k P V : Type}
variable [Field k] [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]

/-- Unit-valued normalizer action on the module Brauer quotient. -/
def normalizerBrauerQuotientUnitHom
    (ρ : Representation k P V)
    (hρ : Function.Injective ρ) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    (representationInteriorAction ρ).unitNormalizer →*
      (Module.End k (BrauerQuotient ρ))ˣ :=
  linearActionUnit
    (normalizerBrauerQuotientLinearAction ρ hρ)

/-- Transport the honest normalizer action through the inverse of the
endomorphism Brauer comparison isomorphism. -/
def endomorphismBrauerNormalizerHom
    (ρ : Representation k P V)
    (hρ : Function.Injective ρ)
    (hB : EndomorphismBrauerComparisonIsomorphism ρ) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    (representationInteriorAction ρ).unitNormalizer →*
      (BrauerQuotientAlgebra
        (k := k) (P := P) (A := Module.End k V))ˣ := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  exact
    (Units.map
      (endomorphismBrauerAlgEquiv ρ hB).symm.toAlgHom.toMonoidHom).comp
        (normalizerBrauerQuotientUnitHom ρ hρ)

@[simp]
theorem endomorphismBrauerAlgEquiv_endomorphismBrauerNormalizerHom
    (ρ : Representation k P V)
    (hρ : Function.Injective ρ)
    (hB : EndomorphismBrauerComparisonIsomorphism ρ) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    ∀ s : (representationInteriorAction ρ).unitNormalizer,
      Units.map
          (endomorphismBrauerAlgEquiv ρ hB).toAlgHom.toMonoidHom
          (endomorphismBrauerNormalizerHom ρ hρ hB s) =
        normalizerBrauerQuotientUnitHom ρ hρ s := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  intro s
  apply Units.ext
  simp [endomorphismBrauerNormalizerHom]

/-- On a fixed-algebra unit, the module-quotient normalizer action is
the image of its algebra Brauer projection under the comparison
isomorphism. -/
theorem normalizerBrauerQuotientUnitHom_fixedUnit
    (ρ : Representation k P V)
    (hρ : Function.Injective ρ)
    (hB : EndomorphismBrauerComparisonIsomorphism ρ) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    ∀
      u :
        (fixedSubalgebra
          (k := k) (P := P) (A := Module.End k V))ˣ,
      normalizerBrauerQuotientUnitHom ρ hρ
          ((representationInteriorAction ρ).fixedUnitToNormalizer
            (k := k) u) =
        Units.map
          (endomorphismBrauerAlgEquiv ρ hB).toAlgHom.toMonoidHom
          (fixedUnitBrauerProjection
            (k := k) (P := P) (A := Module.End k V) u) := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  intro u
  apply Units.ext
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ :=
    brauerProjection_surjective ρ z
  rfl

/-- Conjugation by the normalizer action on the module Brauer quotient
agrees with conjugation of fixed endomorphisms before passing to the
algebra Brauer quotient. -/
theorem normalizerBrauerQuotientUnitHom_conjugation
    (ρ : Representation k P V)
    (hρ : Function.Injective ρ) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    ∀
      (s : (representationInteriorAction ρ).unitNormalizer)
      (c :
        fixedSubalgebra
          (k := k) (P := P) (A := Module.End k V)),
      (↑((normalizerBrauerQuotientUnitHom ρ hρ s)⁻¹) :
          Module.End k (BrauerQuotient ρ)) *
            fixedEndomorphismBrauerAlgHom ρ c *
          (normalizerBrauerQuotientUnitHom ρ hρ s :
            Module.End k (BrauerQuotient ρ)) =
        fixedEndomorphismBrauerAlgHom ρ
          ((representationInteriorAction ρ).normalizerConjFixedAlgEquiv
            (k := k) s c) := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  intro s c
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ :=
    brauerProjection_surjective ρ z
  rfl

/-- The endomorphism Brauer comparison isomorphism constructs the
Puig--Turull normalizer extension for a faithful representation. -/
def brauerNormalizerExtensionOfEndomorphismComparison
    (ρ : Representation k P V)
    (hρ : Function.Injective ρ)
    (hB : EndomorphismBrauerComparisonIsomorphism ρ) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    BrauerNormalizerExtension (k := k)
      (representationInteriorAction ρ) := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  let I := representationInteriorAction ρ
  let Z := endomorphismBrauerAlgEquiv ρ hB
  exact
    { hom := endomorphismBrauerNormalizerHom ρ hρ hB
      extends_fixedUnit := by
        apply MonoidHom.ext
        intro u
        apply
          (Units.mapEquiv
            Z.toRingEquiv.toMulEquiv).injective
        change
          Units.map Z.toAlgHom.toMonoidHom
              (endomorphismBrauerNormalizerHom ρ hρ hB
                (I.fixedUnitToNormalizer (k := k) u)) =
            Units.map Z.toAlgHom.toMonoidHom
              (fixedUnitBrauerProjection
                (k := k) (P := P) (A := Module.End k V) u)
        rw [
          endomorphismBrauerAlgEquiv_endomorphismBrauerNormalizerHom]
        exact normalizerBrauerQuotientUnitHom_fixedUnit
          ρ hρ hB u
      conjugation_compatible := by
        intro s c
        refine
          ⟨I.normalizerConjFixedAlgEquiv (k := k) s c,
            rfl, ?_⟩
        have hsU :=
          endomorphismBrauerAlgEquiv_endomorphismBrauerNormalizerHom
            ρ hρ hB s
        have hs :
            Z
                ((endomorphismBrauerNormalizerHom
                  ρ hρ hB s :
                    (BrauerQuotientAlgebra
                      (k := k) (P := P)
                      (A := Module.End k V))ˣ) :
                  BrauerQuotientAlgebra
                    (k := k) (P := P)
                    (A := Module.End k V)) =
              (normalizerBrauerQuotientUnitHom ρ hρ s :
                Module.End k (BrauerQuotient ρ)) :=
          congrArg Units.val hsU
        have hsInv :
            Z
                (↑((endomorphismBrauerNormalizerHom
                    ρ hρ hB s)⁻¹) :
                  BrauerQuotientAlgebra
                    (k := k) (P := P)
                    (A := Module.End k V)) =
              (↑((normalizerBrauerQuotientUnitHom
                    ρ hρ s)⁻¹) :
                Module.End k (BrauerQuotient ρ)) := by
          exact congrArg Units.val
            (congrArg Inv.inv hsU)
        apply Z.injective
        rw [map_mul, map_mul, hsInv, hs]
        rw [endomorphismBrauerAlgEquiv_apply,
          endomorphismBrauerAlgHom_brauerAlgebraProjection]
        rw [endomorphismBrauerAlgEquiv_apply,
          endomorphismBrauerAlgHom_brauerAlgebraProjection]
        exact
          normalizerBrauerQuotientUnitHom_conjugation
            ρ hρ s c }

/-- Proposition form of the preceding construction. -/
theorem hasBrauerNormalizerExtension_of_endomorphismComparison
    (ρ : Representation k P V)
    (hρ : Function.Injective ρ)
    (hB : EndomorphismBrauerComparisonIsomorphism ρ) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    HasBrauerNormalizerExtension (k := k)
      (representationInteriorAction ρ) :=
  ⟨brauerNormalizerExtensionOfEndomorphismComparison
    ρ hρ hB⟩

end Representation
