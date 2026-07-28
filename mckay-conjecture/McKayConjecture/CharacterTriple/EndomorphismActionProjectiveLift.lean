/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.Algebra.Central.End
import McKayConjecture.CharacterTriple.ProjectiveRepresentation

/-!
# Projective lifts of actions on full endomorphism algebras

Skolem--Noether for a full endomorphism algebra is available in
mathlib as `AlgEquiv.eq_linearEquivConjAlgEquiv`.  Choosing an inner
implementer for every element of a group action produces a projective
linear representation: multiplicativity of the algebra action makes
the discrepancy between two implementers scalar.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple

universe u v w

variable {K : Type u} {V : Type v} {G : Type w}
variable [Field K] [AddCommGroup V] [Module K V]
variable [Nontrivial V] [Group G]

namespace EndomorphismAction

abbrev AlgAut :=
  Module.End K V ≃ₐ[K] Module.End K V

/-- A chosen inner implementer of one algebra automorphism in a group
action on a full endomorphism algebra. -/
def innerImplementer
    (α : G →* AlgAut (K := K) (V := V))
    (g : G) :
    V ≃ₗ[K] V :=
  Classical.choose
    (AlgEquiv.eq_linearEquivConjAlgEquiv (α g))

omit [Nontrivial V] in
/-- The chosen implementer induces the prescribed algebra
automorphism. -/
theorem innerImplementer_conjAlgEquiv
    (α : G →* AlgAut (K := K) (V := V))
    (g : G) :
    α g = (innerImplementer α g).conjAlgEquiv K :=
  Classical.choose_spec
    (AlgEquiv.eq_linearEquivConjAlgEquiv (α g))

omit [Nontrivial V] in
/-- Conjugation by a product of linear equivalences is the product of
their conjugation automorphisms. -/
theorem conjAlgEquiv_mul
    (f g : V ≃ₗ[K] V) :
    (f * g).conjAlgEquiv K =
      f.conjAlgEquiv K * g.conjAlgEquiv K := by
  apply AlgEquiv.ext
  intro x
  apply LinearMap.ext
  intro v
  rfl

omit [Nontrivial V] in
/-- Multiplying two chosen implementers and choosing the implementer
of the product induce the same algebra automorphism. -/
theorem innerImplementer_mul_conjAlgEquiv
    (α : G →* AlgAut (K := K) (V := V))
    (g h : G) :
    (innerImplementer α g *
        innerImplementer α h).conjAlgEquiv K =
      (innerImplementer α (g * h)).conjAlgEquiv K := by
  rw [conjAlgEquiv_mul]
  rw [← innerImplementer_conjAlgEquiv α g,
    ← innerImplementer_conjAlgEquiv α h,
    ← innerImplementer_conjAlgEquiv α (g * h)]
  exact (map_mul α g h).symm

/-- Scalar discrepancy between the chosen implementers of `g`, `h`,
and `g * h`. -/
def innerFactor
    (α : G →* AlgAut (K := K) (V := V))
    (g h : G) :
    Kˣ :=
  Classical.choose
    ((LinearEquiv.conjAlgEquiv_ext_iff'
      (innerImplementer α g * innerImplementer α h)
      (innerImplementer α (g * h))).mp
        (innerImplementer_mul_conjAlgEquiv α g h))

omit [Nontrivial V] in
/-- The chosen inner implementers obey the projective multiplication
law with factor `innerFactor`. -/
theorem innerImplementer_mul
    (α : G →* AlgAut (K := K) (V := V))
    (g h : G) :
    innerImplementer α g * innerImplementer α h =
      scalarLinearEquiv K V (innerFactor α g h) *
        innerImplementer α (g * h) := by
  have hfactor :=
    Classical.choose_spec
      ((LinearEquiv.conjAlgEquiv_ext_iff'
        (innerImplementer α g * innerImplementer α h)
        (innerImplementer α (g * h))).mp
          (innerImplementer_mul_conjAlgEquiv α g h))
  calc
    innerImplementer α g * innerImplementer α h =
        innerFactor α g h • innerImplementer α (g * h) :=
      hfactor
    _ =
        scalarLinearEquiv K V (innerFactor α g h) *
          innerImplementer α (g * h) := by
      ext x
      rfl

/-- The projective representation obtained by choosing inner
implementers for an action on a full endomorphism algebra. -/
def projectiveLift
    (α : G →* AlgAut (K := K) (V := V)) :
    ProjectiveRepresentation K G V where
  operator := innerImplementer α
  factor := innerFactor α
  map_mul := innerImplementer_mul α

omit [Nontrivial V] in
@[simp]
theorem projectiveLift_operator
    (α : G →* AlgAut (K := K) (V := V))
    (g : G) :
    (projectiveLift α).operator g =
      innerImplementer α g :=
  rfl

omit [Nontrivial V] in
@[simp]
theorem projectiveLift_factor
    (α : G →* AlgAut (K := K) (V := V))
    (g h : G) :
    (projectiveLift α).factor g h =
      innerFactor α g h :=
  rfl

omit [Nontrivial V] in
/-- Every chosen projective lift still induces exactly the original
endomorphism-algebra action. -/
theorem projectiveLift_operator_conjAlgEquiv
    (α : G →* AlgAut (K := K) (V := V))
    (g : G) :
    α g =
      ((projectiveLift α).operator g).conjAlgEquiv K :=
  innerImplementer_conjAlgEquiv α g

end EndomorphismAction
end CharacterTriple
end McKayConjecture
