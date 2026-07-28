/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCentralExtension

/-!
# The coefficient subgroup of a factor-set central extension

The kernel of a factor-set extension is the canonical central copy of its
coefficient group.  This file packages that copy as a named subgroup,
identifies it with the coefficient group, and transports scalar characters
across the identification.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet
namespace CentralExtensionGroup

variable {G : Type u} {A : Type v}
variable [Group G] [CommGroup A]
variable (alpha : FactorSet G A) (halpha : alpha.IsNormalized)

/-- The canonical central copy of the coefficient group. -/
abbrev coefficientSubgroup :
    Subgroup (CentralExtensionGroup alpha halpha) :=
  (coefficientEmbedding alpha halpha).range

/-- The coefficient subgroup is canonically isomorphic to the coefficient
group itself. -/
def coefficientEquiv :
    coefficientSubgroup alpha halpha ≃* A :=
  (MonoidHom.ofInjective
    (coefficientEmbedding_injective alpha halpha)).symm

/-- A coefficient element, regarded as an element of the coefficient
subgroup. -/
def coefficientSubgroupElement
    (a : A) :
  coefficientSubgroup alpha halpha :=
  ⟨coefficientEmbedding alpha halpha a,
    ⟨a, rfl⟩⟩

@[simp]
theorem coefficientSubgroupElement_coe
    (a : A) :
    (coefficientSubgroupElement alpha halpha a :
      CentralExtensionGroup alpha halpha) =
        coefficientEmbedding alpha halpha a :=
  rfl

@[simp]
theorem coefficientEquiv_coefficientSubgroupElement
    (a : A) :
    coefficientEquiv alpha halpha
        (coefficientSubgroupElement alpha halpha a) =
      a := by
  exact
    (MonoidHom.ofInjective
      (coefficientEmbedding_injective alpha halpha)
      ).symm_apply_apply a

@[simp]
theorem coefficientEmbedding_coefficientEquiv
    (z : coefficientSubgroup alpha halpha) :
    coefficientEmbedding alpha halpha
        (coefficientEquiv alpha halpha z) =
      (z :
        CentralExtensionGroup alpha halpha) := by
  exact
    congrArg Subtype.val
      ((MonoidHom.ofInjective
        (coefficientEmbedding_injective alpha halpha)
        ).apply_symm_apply z)

/-- Transport a multiplicative scalar character of the coefficient group
to its canonical central copy in the extension. -/
def coefficientScalarCharacter
    {K : Type w} [CommGroup K]
    (iota : A →* K) :
    coefficientSubgroup alpha halpha →* K :=
  iota.comp (coefficientEquiv alpha halpha).toMonoidHom

@[simp]
theorem coefficientScalarCharacter_coefficientSubgroupElement
    {K : Type w} [CommGroup K]
    (iota : A →* K) (a : A) :
    coefficientScalarCharacter alpha halpha iota
        (coefficientSubgroupElement alpha halpha a) =
      iota a := by
  simp [coefficientScalarCharacter]

/-- The named coefficient subgroup is central. -/
theorem coefficientSubgroup_le_center :
    coefficientSubgroup alpha halpha ≤
      Subgroup.center
        (CentralExtensionGroup alpha halpha) :=
  coefficientEmbedding_range_le_center alpha halpha

/-- Hence the coefficient subgroup lies in the normalizer of every
subgroup, in particular every Sylow subgroup. -/
theorem coefficientSubgroup_le_normalizer
    (S : Set (CentralExtensionGroup alpha halpha)) :
    coefficientSubgroup alpha halpha ≤
      Subgroup.normalizer S :=
  coefficientSubgroup_le_center alpha halpha |>.trans
    (Subgroup.center_le_normalizer S)

end CentralExtensionGroup
end FactorSet
end CharacterTriple
end McKayConjecture
