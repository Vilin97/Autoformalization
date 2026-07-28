/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismNormalizer
import McKayConjecture.CharacterTriple.ProjectiveRepresentation

/-!
# Realizing projective operators in an interior normalizer

A normalized projective representation gives a projective normalizer lift
as soon as each chosen operator normalizes the interior group.  This file
provides the constructor and records that forgetting the normalizer
membership recovers the original operator literally.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K P G V : Type}
variable [Field K] [Group P] [Fintype P] [Group G]
variable [AddCommGroup V] [Module K V]
variable [MulSemiringAction P (Module.End K V)]
variable [SMulCommClass P K (Module.End K V)]

/-- The endomorphism-algebra unit represented by a linear
automorphism. -/
def operatorUnit (f : V ≃ₗ[K] V) :
    (Module.End K V)ˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm f

@[simp]
theorem generalLinearEquiv_operatorUnit
    (f : V ≃ₗ[K] V) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv K V
        (operatorUnit f) =
      f :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).apply_symm_apply f

/-- Realize a projective operator as an element of a specified interior
normalizer. -/
def normalizerOperator
    (Q : ProjectiveRepresentation K G V)
    (I : Representation.InteriorAction
      (P := P) (A := Module.End K V))
    (operator_mem :
      ∀ g, operatorUnit (Q.operator g) ∈ I.unitNormalizer)
    (g : G) :
    I.unitNormalizer :=
  ⟨operatorUnit (Q.operator g), operator_mem g⟩

omit [Fintype P] [SMulCommClass P K (Module.End K V)] in
@[simp]
theorem normalizerLinearEquiv_normalizerOperator
    (Q : ProjectiveRepresentation K G V)
    (I : Representation.InteriorAction
      (P := P) (A := Module.End K V))
    (operator_mem :
      ∀ g, operatorUnit (Q.operator g) ∈ I.unitNormalizer)
    (g : G) :
    I.normalizerLinearEquiv
        (normalizerOperator Q I operator_mem g) =
      Q.operator g :=
  generalLinearEquiv_operatorUnit (Q.operator g)

/-- A normalized projective action whose operators normalize the interior
group, bundled as a projective normalizer lift. -/
def toProjectiveNormalizerLift
    (Q : ProjectiveRepresentation K G V)
    (I : Representation.InteriorAction
      (P := P) (A := Module.End K V))
    (operator_mem :
      ∀ g, operatorUnit (Q.operator g) ∈ I.unitNormalizer)
    (operator_one : Q.operator 1 = 1) :
    Representation.ProjectiveNormalizerLift
      (k := K) (H := G) I where
  operator := normalizerOperator Q I operator_mem
  factor := Q.factor
  operator_one := by
    apply Subtype.ext
    apply
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).injective
    change
      Q.operator 1 =
        LinearMap.GeneralLinearGroup.generalLinearEquiv K V
          ((1 : I.unitNormalizer) : (Module.End K V)ˣ)
    rw [operator_one]
    rfl
  operator_mul := by
    intro g h
    apply Subtype.ext
    apply
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).injective
    change
      I.normalizerLinearEquiv
          (normalizerOperator Q I operator_mem g *
            normalizerOperator Q I operator_mem h) =
        I.normalizerLinearEquiv
          (I.scalarUnitNormalizer (k := K) (Q.factor g h) *
            normalizerOperator Q I operator_mem (g * h))
    rw [_root_.map_mul, _root_.map_mul,
      I.normalizerLinearEquiv_scalarUnitNormalizer,
      normalizerLinearEquiv_normalizerOperator,
      normalizerLinearEquiv_normalizerOperator,
      normalizerLinearEquiv_normalizerOperator]
    exact Q.map_mul g h

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
