/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionCoefficient
import McKayConjecture.GroupTheory.CentralExtensionSylowNormalizer
import McKayConjecture.InductiveMcKay.CentralScalarPreservation

/-!
# Scalar-fibre local correspondences for factor extensions

Let `U` be the finite central extension of `Q` defined by a normalized
factor set.  A Sylow subgroup of `Q` has a unique Sylow lift to `U`.  The
central coefficient subgroup lies in the normalizer of that lift, hence in
every intermediate subgroup selected by local inductive-McKay data.

Consequently the local correspondence on `U` restricts to an equivalence on
the prime-to-`p` characters with any prescribed scalar character of the
coefficient subgroup.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace InductiveMcKay
namespace FactorExtensionScalarCorrespondence

open CharacterTriple
open GroupTheory

variable {Q : Type u} {C : Type v}
variable [Group Q] [CommGroup C] [Finite Q] [Finite C]
variable {p : ℕ} [Fact p.Prime]
variable (alpha : FactorSet Q C) (halpha : alpha.IsNormalized)

/-- The central extension determined by the factor set. -/
abbrev extension :
    CentralExtension
      (FactorSet.CentralExtensionGroup alpha halpha) Q :=
  FactorSet.CentralExtensionGroup.centralExtension alpha halpha

/-- The unique Sylow lift of `S` to the factor-set extension. -/
abbrev sylowLift (S : Sylow p Q) :
    Sylow p (FactorSet.CentralExtensionGroup alpha halpha) :=
  (extension alpha halpha).sylowLift S

@[simp]
theorem sylowLift_mapSurjective
    (S : Sylow p Q) :
    (sylowLift alpha halpha S).mapSurjective
        (extension alpha halpha).surjective =
      S :=
  (extension alpha halpha).sylowLift_mapSurjective S

/-- The central coefficient subgroup lies in every local intermediate for
the lifted Sylow subgroup. -/
theorem coefficientSubgroup_le_intermediate
    (S : Sylow p Q)
    (d : LocalInductiveMcKayData
      (sylowLift alpha halpha S)) :
    FactorSet.CentralExtensionGroup.coefficientSubgroup
        alpha halpha ≤
      d.intermediate :=
  (FactorSet.CentralExtensionGroup.coefficientSubgroup_le_normalizer
      alpha halpha
      (sylowLift alpha halpha S :
        Set (FactorSet.CentralExtensionGroup alpha halpha))).trans
    d.normalizer_le

/-- The local correspondence on the factor extension, restricted to the
characters affording the scalar character induced by `iota` on the central
coefficient subgroup. -/
def scalarFibreCorrespondence
    (S : Sylow p Q)
    (d : LocalInductiveMcKayData
      (sylowLift alpha halpha S))
    (iota : C →* ℂˣ) :
    PPrimeCentralScalarCharacter
        (FactorSet.CentralExtensionGroup alpha halpha) p
        (FactorSet.CentralExtensionGroup.coefficientSubgroup
          alpha halpha)
        (FactorSet.CentralExtensionGroup.coefficientScalarCharacter
          alpha halpha iota) ≃
      PPrimeCentralScalarCharacter
        d.intermediate p
        (d.subgroupInIntermediate
          (FactorSet.CentralExtensionGroup.coefficientSubgroup
            alpha halpha))
        (d.centralScalarInIntermediate
          (FactorSet.CentralExtensionGroup.coefficientSubgroup
            alpha halpha)
          (coefficientSubgroup_le_intermediate
            alpha halpha S d)
          (FactorSet.CentralExtensionGroup.coefficientScalarCharacter
            alpha halpha iota)) :=
  d.centralScalarCorrespondence
    (FactorSet.CentralExtensionGroup.coefficientSubgroup
      alpha halpha)
    (FactorSet.CentralExtensionGroup.coefficientSubgroup_le_center
      alpha halpha)
    (coefficientSubgroup_le_intermediate alpha halpha S d)
    (FactorSet.CentralExtensionGroup.coefficientScalarCharacter
      alpha halpha iota)

@[simp]
theorem scalarFibreCorrespondence_apply_coe
    (S : Sylow p Q)
    (d : LocalInductiveMcKayData
      (sylowLift alpha halpha S))
    (iota : C →* ℂˣ)
    (chi :
      PPrimeCentralScalarCharacter
        (FactorSet.CentralExtensionGroup alpha halpha) p
        (FactorSet.CentralExtensionGroup.coefficientSubgroup
          alpha halpha)
        (FactorSet.CentralExtensionGroup.coefficientScalarCharacter
          alpha halpha iota)) :
    (scalarFibreCorrespondence
      alpha halpha S d iota chi).1 =
        d.correspondence chi.1 :=
  rfl

end FactorExtensionScalarCorrespondence
end InductiveMcKay
end McKayConjecture
