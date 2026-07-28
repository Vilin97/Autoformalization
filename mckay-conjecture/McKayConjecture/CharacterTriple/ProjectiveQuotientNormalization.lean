/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveQuotientDescent

/-!
# Normalization of exact quotient descents

Exact quotient compatibility already forces the identity operator to be
the identity: the distinguished normal subgroup contains `1`, and all of
its chosen operators are assumed to be trivial.  Consequently the exact
quotient descent is normalized as well.

These elementary adapters remove separate normalization hypotheses from
constructions whose projective actions arise by exact quotient descent.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K G V : Type}
variable [Field K] [Group G]
variable [AddCommGroup V] [Module K V]
variable {P : ProjectiveRepresentation K G V}
variable {N : Subgroup G} [N.Normal]

omit [N.Normal] in
/-- Exact quotient compatibility forces normalization of the source
projective representation. -/
theorem IsQuotientCompatible.isNormalized
    (hP : P.IsQuotientCompatible N) :
    P.IsNormalized := by
  change P.operator 1 = 1
  simpa only [Subgroup.coe_one] using
    hP.operator_normal (1 : N)

/-- The exact quotient descent of a quotient-compatible projective
representation is normalized. -/
theorem quotientDescent_isNormalized
    (hP : P.IsQuotientCompatible N) :
    (P.quotientDescent N hP).IsNormalized := by
  change (P.quotientDescent N hP).operator 1 = 1
  have hone :=
    P.quotientDescent_operator_mk hP (1 : G)
  rw [map_one] at hone
  exact hone.trans hP.isNormalized

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
