/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.MagicLinearization
import McKayConjecture.CharacterTriple.ProjectiveNormalizerLift

/-!
# Magic linearization from a Brauer-normalizer extension

The projective operators in the Dade--Glauberman--Nagao argument lie in
an interior normalizer.  Once the Brauer map extends to that normalizer
and the Brauer quotient is identified with the ground field, the
normalizer correction gives an honest linear action.  This file packages
the resulting action as `MagicLinearization`.
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

/-- A projective action whose chosen operators are realized in an
endomorphism-algebra interior normalizer becomes magic-linearized after
the Brauer-normalizer correction. -/
def magicLinearizationOfNormalizerCorrection
    (Q : ProjectiveRepresentation K G V)
    (I : Representation.InteriorAction
      (P := P) (A := Module.End K V))
    (T : Representation.ProjectiveNormalizerLift
      (k := K) (H := G) I)
    (E : Representation.BrauerNormalizerExtension (k := K) I)
    (Z : Representation.BrauerScalarIdentification
      (k := K) (P := P) (A := Module.End K V))
    (operator_eq :
      ∀ g,
        I.normalizerLinearEquiv (T.operator g) =
          Q.operator g) :
    MagicLinearization Q where
  action := T.correctedLinearAction E Z
  scalar := T.brauerScalar E Z
  operator_eq := by
    intro g v
    have hop := LinearEquiv.congr_fun (operator_eq g) v
    change
      Q.operator g v =
        (T.brauerScalar E Z g : K) •
          I.normalizerLinearEquiv
            (I.scalarUnitNormalizer
                (k := K) (T.brauerScalar E Z g)⁻¹ *
              T.operator g) v
    rw [← hop]
    rw [_root_.map_mul,
      I.normalizerLinearEquiv_scalarUnitNormalizer]
    simp only [LinearEquiv.mul_apply]
    change
      I.normalizerLinearEquiv (T.operator g) v =
        (T.brauerScalar E Z g : K) •
          ((((T.brauerScalar E Z g)⁻¹ : Kˣ) : K) •
            I.normalizerLinearEquiv (T.operator g) v)
    rw [smul_smul]
    simp

/-- Direct form: normalized projective operators that normalize an
interior action are magic-linearized by any compatible Brauer-normalizer
extension and scalar Brauer identification. -/
def magicLinearizationOfNormalizerData
    (Q : ProjectiveRepresentation K G V)
    (I : Representation.InteriorAction
      (P := P) (A := Module.End K V))
    (operator_mem :
      ∀ g, operatorUnit (Q.operator g) ∈ I.unitNormalizer)
    (operator_one : Q.operator 1 = 1)
    (E : Representation.BrauerNormalizerExtension (k := K) I)
    (Z : Representation.BrauerScalarIdentification
      (k := K) (P := P) (A := Module.End K V)) :
    MagicLinearization Q :=
  magicLinearizationOfNormalizerCorrection Q I
    (toProjectiveNormalizerLift Q I operator_mem operator_one)
    E Z
    (normalizerLinearEquiv_normalizerOperator Q I operator_mem)

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
