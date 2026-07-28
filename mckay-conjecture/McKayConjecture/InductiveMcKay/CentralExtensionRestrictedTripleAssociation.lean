/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedQuotientDescent
import McKayConjecture.InductiveMcKay.CentralExtensionRestrictedTripleQuotient

/-!
# Associated projective descent for restricted central-extension triples

The two pullback projections constructed for central-extension descent are
quotient maps of character triples.  This file gives the induced maps on
normal subgroups, proves exact inflation of both normal characters, and
therefore descends any associated projective representations on the
restricted triples.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace InductiveMcKay
namespace SylowAutomorphismLift

open GroupTheory
open CharacterTriple

variable {A : Type u} {Q : Type v}
variable [Group A] [Group Q] [Finite A] [Finite Q]
variable {p : ℕ} [Fact p.Prime]
variable {E : CentralExtension A Q} {S : Sylow p Q}
variable
  (L : SylowAutomorphismLift E S)
  (d : LocalInductiveMcKayData (E.sylowLift S))
  (χ : PPrimeIrreducibleCharacter Q p)

/-- The normal subgroup of the restricted ambient triple is canonically
the original cover group. -/
def restrictedAmbientNormalEquiv :
    (restrictedAmbientTriple L χ).normalSubgroup ≃* A :=
  ((EquivariantLocalCorrespondence.ambientTriple
      (inflatedCharacter E χ)).normalSubgroupInEquiv
    (ambientLiftPullback L χ)
    (ambientNormal_le_liftPullback L χ)).trans
      (semidirectNormalEquiv
        (PPrimeCharacterStabilizer.ambientAction
          (P := E.sylowLift S)
          (χ := inflatedCharacter E χ)))

/-- The normal subgroup of the restricted intermediate triple is
canonically the upstairs intermediate subgroup. -/
def restrictedIntermediateNormalEquiv :
    (restrictedIntermediateTriple L d χ).normalSubgroup ≃*
      d.toEquivariant.intermediate :=
  ((d.toEquivariant.intermediateTriple
      (inflatedCharacter E χ)).normalSubgroupInEquiv
    (intermediateLiftPullback L d χ)
    (intermediateNormal_le_liftPullback L d χ)).trans
      (semidirectNormalEquiv
        (d.toEquivariant.stabilizerIntermediateAction
          (inflatedCharacter E χ)))

@[simp]
theorem restrictedAmbientNormalEquiv_apply
    (x : (restrictedAmbientTriple L χ).normalSubgroup) :
    restrictedAmbientNormalEquiv L χ x =
      x.1.1.left :=
  rfl

@[simp]
theorem restrictedIntermediateNormalEquiv_apply
    (x : (restrictedIntermediateTriple L d χ).normalSubgroup) :
    restrictedIntermediateNormalEquiv L d χ x =
      x.1.1.left :=
  rfl

/-- The normal-subgroup map induced by the ambient pullback projection. -/
def ambientTripleNormalProjection :
    (restrictedAmbientTriple L χ).normalSubgroup →*
      (EquivariantLocalCorrespondence.ambientTriple
        (P := S) χ).normalSubgroup :=
  (semidirectNormalEquiv
      (PPrimeCharacterStabilizer.ambientAction
        (P := S) (χ := χ))).symm.toMonoidHom.comp
    (E.projection.comp
      (restrictedAmbientNormalEquiv L χ).toMonoidHom)

/-- The normal-subgroup map induced by the intermediate pullback
projection. -/
def intermediateTripleNormalProjection :
    (restrictedIntermediateTriple L d χ).normalSubgroup →*
      ((L.quotientEquivariantLocalCorrespondence d
        |>.intermediateTriple χ).normalSubgroup) :=
  (semidirectNormalEquiv
      (projectedIntermediateAction L d χ)).symm.toMonoidHom.comp
    ((d.intermediateProjection E.projection).comp
      (restrictedIntermediateNormalEquiv L d χ).toMonoidHom)

@[simp]
theorem ambientTripleNormalProjection_apply_left
    (x : (restrictedAmbientTriple L χ).normalSubgroup) :
    (ambientTripleNormalProjection L χ x).1.left =
      E.projection (restrictedAmbientNormalEquiv L χ x) :=
  rfl

@[simp]
theorem intermediateTripleNormalProjection_apply_left
    (x : (restrictedIntermediateTriple L d χ).normalSubgroup) :
    (intermediateTripleNormalProjection L d χ x).1.left =
      d.intermediateProjection E.projection
        (restrictedIntermediateNormalEquiv L d χ x) :=
  rfl

/-- The ambient normal projection is literally the restriction of the
ambient pullback projection. -/
theorem ambientTripleNormalProjection_coe
    (x : (restrictedAmbientTriple L χ).normalSubgroup) :
    ((ambientTripleNormalProjection L χ x :
        (EquivariantLocalCorrespondence.ambientTriple
          (P := S) χ).normalSubgroup) :
      Q ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer S χ) =
      ambientPullbackProjection L χ x.1 := by
  apply SemidirectProduct.ext
  · rw [ambientPullbackProjection_left]
    rfl
  · have hxRight : x.1.1.right = 1 := by
      obtain ⟨a, ha⟩ := x.property
      have hright := congrArg SemidirectProduct.right ha
      simpa using hright.symm
    rw [ambientPullbackProjection_right]
    change
      (1 : PPrimeCharacterStabilizer S χ) =
        ambientPullbackStabilizer L χ x.1
    apply L.characterStabilizerLift_injective χ
    rw [map_one,
      characterStabilizerLift_ambientPullbackStabilizer,
      hxRight]

/-- The intermediate normal projection is literally the restriction of
the intermediate pullback projection. -/
theorem intermediateTripleNormalProjection_coe
    (x : (restrictedIntermediateTriple L d χ).normalSubgroup) :
    ((intermediateTripleNormalProjection L d χ x :
        (L.quotientEquivariantLocalCorrespondence d
          |>.intermediateTriple χ).normalSubgroup) :
      (L.quotientEquivariantLocalCorrespondence d).intermediate ⋊[
        projectedIntermediateAction L d χ]
        PPrimeCharacterStabilizer S χ) =
      intermediatePullbackProjection L d χ x.1 := by
  apply SemidirectProduct.ext
  · rw [intermediatePullbackProjection_left]
    rfl
  · have hxRight : x.1.1.right = 1 := by
      obtain ⟨a, ha⟩ := x.property
      have hright := congrArg SemidirectProduct.right ha
      simpa using hright.symm
    rw [intermediatePullbackProjection_right]
    change
      (1 : PPrimeCharacterStabilizer S χ) =
        intermediatePullbackStabilizer L d χ x.1
    apply L.characterStabilizerLift_injective χ
    rw [map_one,
      characterStabilizerLift_intermediatePullbackStabilizer,
      hxRight]

/-- The ambient normal-subgroup projection is onto. -/
theorem ambientTripleNormalProjection_surjective :
    Function.Surjective (ambientTripleNormalProjection L χ) := by
  intro y
  let qy :=
    semidirectNormalEquiv
      (PPrimeCharacterStabilizer.ambientAction
        (P := S) (χ := χ)) y
  obtain ⟨a, ha⟩ := E.surjective qy
  let x :=
    (restrictedAmbientNormalEquiv L χ).symm a
  refine ⟨x, ?_⟩
  apply
    (semidirectNormalEquiv
      (PPrimeCharacterStabilizer.ambientAction
        (P := S) (χ := χ))).injective
  change E.projection a = qy
  exact ha

/-- The intermediate normal-subgroup projection is onto. -/
theorem intermediateTripleNormalProjection_surjective :
    Function.Surjective
      (intermediateTripleNormalProjection L d χ) := by
  intro y
  let qy :=
    semidirectNormalEquiv
      (projectedIntermediateAction L d χ) y
  obtain ⟨a, ha⟩ :=
    d.intermediateProjection_surjective E.projection qy
  let x :=
    (restrictedIntermediateNormalEquiv L d χ).symm a
  refine ⟨x, ?_⟩
  apply
    (semidirectNormalEquiv
      (projectedIntermediateAction L d χ)).injective
  change d.intermediateProjection E.projection a = qy
  exact ha

/-- The restricted ambient normal character is the exact inflation of the
downstairs ambient normal character. -/
theorem restrictedAmbient_character_values_projection
    (x : (restrictedAmbientTriple L χ).normalSubgroup) :
    (restrictedAmbientTriple L χ).character.values x =
      (EquivariantLocalCorrespondence.ambientTriple
        (P := S) χ).character.values
        (ambientTripleNormalProjection L χ x) := by
  change
    (inflatedCharacter E χ).1.values
        (restrictedAmbientNormalEquiv L χ x) =
      χ.1.values
        (E.projection
          (restrictedAmbientNormalEquiv L χ x))
  exact
    E.pPrimeInflationEquiv_apply_values
      p χ (restrictedAmbientNormalEquiv L χ x)

/-- The restricted intermediate normal character is the exact inflation
of the downstairs intermediate normal character. -/
theorem restrictedIntermediate_character_values_projection
    (x : (restrictedIntermediateTriple L d χ).normalSubgroup) :
    (restrictedIntermediateTriple L d χ).character.values x =
      (L.quotientEquivariantLocalCorrespondence d
        |>.intermediateTriple χ).character.values
          (intermediateTripleNormalProjection L d χ x) := by
  change
    (d.correspondence (inflatedCharacter E χ)).1.values
        (restrictedIntermediateNormalEquiv L d χ x) =
      (d.projectedCorrespondence E S χ).1.values
        (d.intermediateProjection E.projection
          (restrictedIntermediateNormalEquiv L d χ x))
  exact
    (d.projectedCorrespondence_values_projection
      E S χ (restrictedIntermediateNormalEquiv L d χ x)).symm

/-- The ambient pullback projection is a quotient map of the two ambient
character triples. -/
def ambientTripleQuotientData :
    CharacterTriple.QuotientData
      (restrictedAmbientTriple L χ)
      (EquivariantLocalCorrespondence.ambientTriple
        (P := S) χ)
      (ambientPullbackProjection L χ) where
  surjective := ambientPullbackProjection_surjective L χ
  normalProjection := ambientTripleNormalProjection L χ
  normalProjection_coe :=
    ambientTripleNormalProjection_coe L χ
  normal_surjective :=
    ambientTripleNormalProjection_surjective L χ
  character_values :=
    restrictedAmbient_character_values_projection L χ
  ker_le_normal := by
    intro x hx
    rw [ambientPullbackProjection_ker] at hx
    obtain ⟨a, ha, hax⟩ := hx
    change x.1 ∈
      (EquivariantLocalCorrespondence.ambientTriple
        (inflatedCharacter E χ)).normalSubgroup
    rw [← hax]
    refine ⟨a, ?_⟩
    apply SemidirectProduct.ext
    · exact
        (ambientPullbackNormalInclusion_left L χ a).symm
    · exact
        (ambientPullbackNormalInclusion_right L χ a).symm

/-- The intermediate pullback projection is a quotient map of the two
intermediate character triples. -/
def intermediateTripleQuotientData :
    CharacterTriple.QuotientData
      (restrictedIntermediateTriple L d χ)
      (L.quotientEquivariantLocalCorrespondence d
        |>.intermediateTriple χ)
      (intermediatePullbackProjection L d χ) where
  surjective :=
    intermediatePullbackProjection_surjective L d χ
  normalProjection :=
    intermediateTripleNormalProjection L d χ
  normalProjection_coe :=
    intermediateTripleNormalProjection_coe L d χ
  normal_surjective :=
    intermediateTripleNormalProjection_surjective L d χ
  character_values :=
    restrictedIntermediate_character_values_projection L d χ
  ker_le_normal := by
    intro x hx
    rw [intermediatePullbackProjection_ker] at hx
    obtain ⟨a, ha, hax⟩ := hx
    change x.1 ∈
      (d.toEquivariant.intermediateTriple
        (inflatedCharacter E χ)).normalSubgroup
    rw [← hax]
    refine ⟨a, ?_⟩
    apply SemidirectProduct.ext
    · exact
        (intermediatePullbackNormalInclusion_left
          L d χ a).symm
    · exact
        (intermediatePullbackNormalInclusion_right
          L d χ a).symm

end SylowAutomorphismLift
end InductiveMcKay
end McKayConjecture
