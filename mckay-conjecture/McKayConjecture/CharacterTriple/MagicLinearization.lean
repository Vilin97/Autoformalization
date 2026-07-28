/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCohomology
import McKayConjecture.CharacterTriple.ProjectiveLinearLift

/-!
# Linearizing a projective action by a magic representation

A magic-representation argument produces an honest linear action on a
multiplicity space and compares each inherited projective operator with
the honest operator by a nonzero scalar.  This file records that output as
data and proves, independently of the construction of the magic action,
that it trivializes the projective factor class.

This is the algebraic interface needed by the Dade--Glauberman--Nagao
step: the difficult local theorem constructs `MagicLinearization`; all
subsequent factor-set and cohomology consequences are formal.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K : Type u} {G : Type v} {V : Type w}
variable [Field K] [Group G]
variable [AddCommGroup V] [Module K V]

/-- A genuine linear action whose operators agree with a projective action
up to an explicitly chosen nonzero scalar at each group element. -/
structure MagicLinearization
    (P : ProjectiveRepresentation K G V) where
  /-- The honest action supplied by the magic representation. -/
  action : G →* (V ≃ₗ[K] V)
  /-- The scalar comparing the projective and honest operators. -/
  scalar : G → Kˣ
  /-- Pointwise comparison of the two operator systems. -/
  operator_eq :
    ∀ (g : G) (v : V),
      P.operator g v = (scalar g : K) • action g v

namespace MagicLinearization

variable {P : ProjectiveRepresentation K G V}

/-- A magic linearization identifies the projective representation with
the scalar rescaling of its honest action. -/
theorem projective_eq_rescale [Nontrivial V]
    (M : MagicLinearization P) :
    P =
      (ProjectiveRepresentation.ofLinearAction M.action).rescale
        M.scalar := by
  apply ProjectiveRepresentation.ext_of_operator_eq
  funext g
  apply LinearEquiv.ext
  intro v
  simpa only [ProjectiveRepresentation.rescale_operator,
    ProjectiveRepresentation.ofLinearAction,
    LinearEquiv.mul_apply, scalarLinearEquiv_apply] using
      M.operator_eq g v

/-- The factor set of a magic-linearized projective action is the
coboundary obtained by gauging the constant-one factor set by the
comparison scalar. -/
theorem factorSet_eq_gauge_one [Nontrivial V]
    (M : MagicLinearization P) :
    P.factorSet =
      (FactorSet.one : FactorSet G Kˣ).gauge M.scalar := by
  let Q :=
    (ProjectiveRepresentation.ofLinearAction M.action).rescale
      M.scalar
  have hoperator : P.operator = Q.operator := by
    funext g
    apply LinearEquiv.ext
    intro v
    simpa only [Q, ProjectiveRepresentation.rescale_operator,
      ProjectiveRepresentation.ofLinearAction,
      LinearEquiv.mul_apply, scalarLinearEquiv_apply] using
        M.operator_eq g v
  have hfactor : P.factor = Q.factor :=
    ProjectiveRepresentation.factor_eq_of_operator_eq
      P Q hoperator
  apply FactorSet.ext
  intro g h
  have hvalue := congrFun (congrFun hfactor g) h
  simpa only [Q, ProjectiveRepresentation.rescale_factor,
    ProjectiveRepresentation.ofLinearAction,
    ProjectiveRepresentation.factorSet_apply,
    FactorSet.gauge_apply, FactorSet.one_apply, mul_one] using hvalue

end MagicLinearization

section Cohomology

variable {K G V : Type}
variable [Field K] [Group G]
variable [AddCommGroup V] [Module K V]
variable {P : ProjectiveRepresentation K G V}

namespace MagicLinearization

/-- A magic linearization kills the projective obstruction class. -/
theorem factorSet_h2Class_eq_zero [Nontrivial V]
    (M : MagicLinearization P) :
    letI := trivialMulDistribMulAction G Kˣ
    P.factorSet.h2Class = 0 := by
  letI := trivialMulDistribMulAction G Kˣ
  rw [M.factorSet_eq_gauge_one,
    FactorSet.h2Class_gauge,
    FactorSet.h2Class_one]

end MagicLinearization
end Cohomology

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
