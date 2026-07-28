/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralExtensionRestrictedTripleWitness

/-!
# Quotient geometry for a restricted central-extension triple

After restricting an upstairs character-triple witness to the chosen lifts
of the downstairs character stabilizer, both ambient groups are honest
pullbacks.  This file identifies those pullbacks with semidirect products
using the downstairs stabilizer, constructs the two quotient projections,
computes their kernels, and proves that the canonical intermediate
embedding commutes with projection.

This is the group-theoretic part of triple descent.  It isolates the
remaining representation-theoretic construction: descending the associated
projective representations through these two kernels.
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

/-- A coherent automorphism lift is injective because the central
projection is surjective. -/
theorem lift_injective :
    Function.Injective L.lift := by
  intro α β hαβ
  apply Subtype.ext
  apply MulEquiv.ext
  intro q
  obtain ⟨a, rfl⟩ := E.surjective q
  calc
    α.1 (E.projection a) =
        E.projection ((L.lift α).1 a) :=
      (L.projection_commutes α a).symm
    _ = E.projection ((L.lift β).1 a) := by
      rw [hαβ]
    _ = β.1 (E.projection a) :=
      L.projection_commutes β a

/-- The induced map between character stabilizers is injective. -/
theorem characterStabilizerLift_injective :
    Function.Injective (L.characterStabilizerLift χ) := by
  intro α β hαβ
  apply Subtype.ext
  apply L.lift_injective
  exact congrArg Subtype.val hαβ

/-- The action of the downstairs character stabilizer on the upstairs
intermediate subgroup through the chosen lift. -/
def liftedIntermediateAction :
    PPrimeCharacterStabilizer S χ →*
      MulAut d.intermediate :=
  (d.toEquivariant.stabilizerIntermediateAction
      (inflatedCharacter E χ)).comp
    (L.characterStabilizerLift χ)

@[simp]
theorem liftedIntermediateAction_apply_coe
    (α : PPrimeCharacterStabilizer S χ)
    (a : d.intermediate) :
    ((liftedIntermediateAction L d χ α a :
        d.intermediate) : A) =
      (L.lift α.1).1 (a : A) :=
  rfl

/-- The action of the downstairs character stabilizer on the projected
intermediate subgroup. -/
abbrev projectedIntermediateAction :
    PPrimeCharacterStabilizer S χ →*
      MulAut
        (L.quotientEquivariantLocalCorrespondence d).intermediate :=
  (L.quotientEquivariantLocalCorrespondence d
    |>.stabilizerIntermediateAction χ)

/-- The direct lifted ambient semidirect product maps onto the ambient
pullback subgroup. -/
def ambientLiftPullbackHom :
    (A ⋊[L.liftedAmbientAction χ]
        PPrimeCharacterStabilizer S χ) →*
      ambientLiftPullback L χ :=
  (SemidirectProduct.map
      (MonoidHom.id A)
      (L.characterStabilizerLift χ)
      (by
        intro α
        ext a
        rfl)).codRestrict
    (ambientLiftPullback L χ)
    (by
      intro x
      exact ⟨x.right, rfl⟩)

@[simp]
theorem ambientLiftPullbackHom_left
    (x :
      A ⋊[L.liftedAmbientAction χ]
        PPrimeCharacterStabilizer S χ) :
    ((ambientLiftPullbackHom L χ x :
        ambientLiftPullback L χ) :
      A ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer
          (E.sylowLift S) (inflatedCharacter E χ)).left =
      x.left :=
  rfl

@[simp]
theorem ambientLiftPullbackHom_right
    (x :
      A ⋊[L.liftedAmbientAction χ]
        PPrimeCharacterStabilizer S χ) :
    ((ambientLiftPullbackHom L χ x :
        ambientLiftPullback L χ) :
      A ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer
          (E.sylowLift S) (inflatedCharacter E χ)).right =
      L.characterStabilizerLift χ x.right :=
  rfl

/-- The direct lifted ambient semidirect product is isomorphic to the
ambient pullback. -/
def ambientLiftPullbackEquiv :
    (A ⋊[L.liftedAmbientAction χ]
        PPrimeCharacterStabilizer S χ) ≃*
      ambientLiftPullback L χ :=
  MulEquiv.ofBijective
    (ambientLiftPullbackHom L χ)
    ⟨by
      intro x y hxy
      apply SemidirectProduct.ext
      · exact congrArg
          (fun z =>
            (((z : ambientLiftPullback L χ) :
              A ⋊[PPrimeCharacterStabilizer.ambientAction]
                PPrimeCharacterStabilizer
                  (E.sylowLift S) (inflatedCharacter E χ))).left)
          hxy
      · apply L.characterStabilizerLift_injective χ
        exact congrArg
          (fun z =>
            (((z : ambientLiftPullback L χ) :
              A ⋊[PPrimeCharacterStabilizer.ambientAction]
                PPrimeCharacterStabilizer
                  (E.sylowLift S) (inflatedCharacter E χ))).right)
          hxy,
    by
      intro x
      obtain ⟨α, hα⟩ := x.property
      refine ⟨⟨x.1.left, α⟩, ?_⟩
      apply Subtype.ext
      apply SemidirectProduct.ext
      · rfl
      · exact hα⟩

/-- The direct lifted intermediate semidirect product maps onto the
intermediate pullback subgroup. -/
def intermediateLiftPullbackHom :
    (d.intermediate ⋊[liftedIntermediateAction L d χ]
        PPrimeCharacterStabilizer S χ) →*
      intermediateLiftPullback L d χ :=
  (SemidirectProduct.map
      (MonoidHom.id d.intermediate)
      (L.characterStabilizerLift χ)
      (by
        intro α
        ext a
        rfl)).codRestrict
    (intermediateLiftPullback L d χ)
    (by
      intro x
      exact ⟨x.right, rfl⟩)

@[simp]
theorem intermediateLiftPullbackHom_left
    (x :
      d.intermediate ⋊[liftedIntermediateAction L d χ]
        PPrimeCharacterStabilizer S χ) :
    ((intermediateLiftPullbackHom L d χ x :
        intermediateLiftPullback L d χ) :
      d.toEquivariant.intermediate ⋊[
        d.toEquivariant.stabilizerIntermediateAction
          (inflatedCharacter E χ)]
        PPrimeCharacterStabilizer
          (E.sylowLift S) (inflatedCharacter E χ)).left =
      x.left :=
  rfl

@[simp]
theorem intermediateLiftPullbackHom_right
    (x :
      d.intermediate ⋊[liftedIntermediateAction L d χ]
        PPrimeCharacterStabilizer S χ) :
    ((intermediateLiftPullbackHom L d χ x :
        intermediateLiftPullback L d χ) :
      d.toEquivariant.intermediate ⋊[
        d.toEquivariant.stabilizerIntermediateAction
          (inflatedCharacter E χ)]
        PPrimeCharacterStabilizer
          (E.sylowLift S) (inflatedCharacter E χ)).right =
      L.characterStabilizerLift χ x.right :=
  rfl

/-- The direct lifted intermediate semidirect product is isomorphic to the
intermediate pullback. -/
def intermediateLiftPullbackEquiv :
    (d.intermediate ⋊[liftedIntermediateAction L d χ]
        PPrimeCharacterStabilizer S χ) ≃*
      intermediateLiftPullback L d χ :=
  MulEquiv.ofBijective
    (intermediateLiftPullbackHom L d χ)
    ⟨by
      intro x y hxy
      apply SemidirectProduct.ext
      · exact congrArg
          (fun z =>
            (((z : intermediateLiftPullback L d χ) :
              d.toEquivariant.intermediate ⋊[
                d.toEquivariant.stabilizerIntermediateAction
                  (inflatedCharacter E χ)]
                PPrimeCharacterStabilizer
                  (E.sylowLift S)
                  (inflatedCharacter E χ))).left)
          hxy
      · apply L.characterStabilizerLift_injective χ
        exact congrArg
          (fun z =>
            (((z : intermediateLiftPullback L d χ) :
              d.toEquivariant.intermediate ⋊[
                d.toEquivariant.stabilizerIntermediateAction
                  (inflatedCharacter E χ)]
                PPrimeCharacterStabilizer
                  (E.sylowLift S)
                  (inflatedCharacter E χ))).right)
          hxy,
    by
      intro x
      obtain ⟨α, hα⟩ := x.property
      refine ⟨⟨x.1.left, α⟩, ?_⟩
      apply Subtype.ext
      apply SemidirectProduct.ext
      · rfl
      · exact hα⟩

/-- The intermediate projection intertwines the lifted action with the
action on the projected intermediate subgroup. -/
theorem intermediateProjection_equivariant
    (α : PPrimeCharacterStabilizer S χ)
    (a : d.intermediate) :
    d.intermediateProjection E.projection
        (liftedIntermediateAction L d χ α a) =
      projectedIntermediateAction L d χ
        α (d.intermediateProjection E.projection a) := by
  apply Subtype.ext
  exact L.projection_commutes α.1 (a : A)

/-- Projection of the direct lifted intermediate semidirect product. -/
def intermediateSemidirectProjection :
    (d.intermediate ⋊[liftedIntermediateAction L d χ]
        PPrimeCharacterStabilizer S χ) →*
      ((L.quotientEquivariantLocalCorrespondence d).intermediate ⋊[
        projectedIntermediateAction L d χ]
        PPrimeCharacterStabilizer S χ) :=
  SemidirectProduct.map
    (d.intermediateProjection E.projection)
    (MonoidHom.id (PPrimeCharacterStabilizer S χ))
    (by
      intro α
      ext a
      exact congrArg Subtype.val
        (L.intermediateProjection_equivariant d χ α a))

@[simp]
theorem intermediateSemidirectProjection_left
    (x :
      d.intermediate ⋊[liftedIntermediateAction L d χ]
        PPrimeCharacterStabilizer S χ) :
    (intermediateSemidirectProjection L d χ x).left =
      d.intermediateProjection E.projection x.left :=
  rfl

@[simp]
theorem intermediateSemidirectProjection_right
    (x :
      d.intermediate ⋊[liftedIntermediateAction L d χ]
        PPrimeCharacterStabilizer S χ) :
    (intermediateSemidirectProjection L d χ x).right =
      x.right :=
  rfl

/-- The direct intermediate semidirect projection is surjective. -/
theorem intermediateSemidirectProjection_surjective :
    Function.Surjective
      (intermediateSemidirectProjection L d χ) := by
  intro x
  obtain ⟨a, ha⟩ :=
    LocalInductiveMcKayData.intermediateProjection_surjective
      d E.projection x.left
  refine ⟨⟨a, x.right⟩, ?_⟩
  apply SemidirectProduct.ext
  · exact ha
  · rfl

/-- The selected downstairs stabilizer coordinate of an element of the
ambient pullback. -/
abbrev ambientPullbackStabilizer
    (x : ambientLiftPullback L χ) :
    PPrimeCharacterStabilizer S χ :=
  (ambientLiftPullbackEquiv L χ).symm x |>.right

/-- The selected downstairs stabilizer coordinate of an element of the
intermediate pullback. -/
abbrev intermediatePullbackStabilizer
    (x : intermediateLiftPullback L d χ) :
    PPrimeCharacterStabilizer S χ :=
  (intermediateLiftPullbackEquiv L d χ).symm x |>.right

@[simp]
theorem characterStabilizerLift_ambientPullbackStabilizer
    (x : ambientLiftPullback L χ) :
    L.characterStabilizerLift χ
        (ambientPullbackStabilizer L χ x) =
      x.1.right := by
  have h :=
    congrArg
      (fun z : ambientLiftPullback L χ =>
        ((z :
          A ⋊[PPrimeCharacterStabilizer.ambientAction]
            PPrimeCharacterStabilizer
              (E.sylowLift S) (inflatedCharacter E χ))).right)
      ((ambientLiftPullbackEquiv L χ).apply_symm_apply x)
  exact h

@[simp]
theorem ambientLiftPullbackEquiv_symm_left
    (x : ambientLiftPullback L χ) :
    ((ambientLiftPullbackEquiv L χ).symm x).left =
      x.1.left := by
  have h :=
    congrArg
      (fun z : ambientLiftPullback L χ =>
        ((z :
          A ⋊[PPrimeCharacterStabilizer.ambientAction]
            PPrimeCharacterStabilizer
              (E.sylowLift S) (inflatedCharacter E χ))).left)
      ((ambientLiftPullbackEquiv L χ).apply_symm_apply x)
  exact h

@[simp]
theorem characterStabilizerLift_intermediatePullbackStabilizer
    (x : intermediateLiftPullback L d χ) :
    L.characterStabilizerLift χ
        (intermediatePullbackStabilizer L d χ x) =
      x.1.right := by
  have h :=
    congrArg
      (fun z : intermediateLiftPullback L d χ =>
        ((z :
          d.toEquivariant.intermediate ⋊[
            d.toEquivariant.stabilizerIntermediateAction
              (inflatedCharacter E χ)]
            PPrimeCharacterStabilizer
              (E.sylowLift S)
              (inflatedCharacter E χ))).right)
      ((intermediateLiftPullbackEquiv L d χ).apply_symm_apply x)
  exact h

@[simp]
theorem intermediateLiftPullbackEquiv_symm_left
    (x : intermediateLiftPullback L d χ) :
    ((intermediateLiftPullbackEquiv L d χ).symm x).left =
      x.1.left := by
  have h :=
    congrArg
      (fun z : intermediateLiftPullback L d χ =>
        ((z :
          d.toEquivariant.intermediate ⋊[
            d.toEquivariant.stabilizerIntermediateAction
              (inflatedCharacter E χ)]
            PPrimeCharacterStabilizer
              (E.sylowLift S)
              (inflatedCharacter E χ))).left)
      ((intermediateLiftPullbackEquiv L d χ).apply_symm_apply x)
  exact h

/-- Projection from the ambient pullback to the actual downstairs ambient
semidirect product. -/
def ambientPullbackProjection :
    ambientLiftPullback L χ →*
      (Q ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer S χ) :=
  (L.ambientSemidirectProjection χ).comp
    (ambientLiftPullbackEquiv L χ).symm.toMonoidHom

@[simp]
theorem ambientPullbackProjection_left
    (x : ambientLiftPullback L χ) :
    (ambientPullbackProjection L χ x).left =
      E.projection x.1.left := by
  exact congrArg E.projection
    (ambientLiftPullbackEquiv_symm_left L χ x)

@[simp]
theorem ambientPullbackProjection_right
    (x : ambientLiftPullback L χ) :
    (ambientPullbackProjection L χ x).right =
      ambientPullbackStabilizer L χ x :=
  rfl

/-- Projection from the intermediate pullback to the actual downstairs
intermediate semidirect product. -/
def intermediatePullbackProjection :
    intermediateLiftPullback L d χ →*
      ((L.quotientEquivariantLocalCorrespondence d).intermediate ⋊[
        projectedIntermediateAction L d χ]
        PPrimeCharacterStabilizer S χ) :=
  (intermediateSemidirectProjection L d χ).comp
    (intermediateLiftPullbackEquiv L d χ).symm.toMonoidHom

@[simp]
theorem intermediatePullbackProjection_left
    (x : intermediateLiftPullback L d χ) :
    (intermediatePullbackProjection L d χ x).left =
      d.intermediateProjection E.projection x.1.left := by
  exact congrArg (d.intermediateProjection E.projection)
    (intermediateLiftPullbackEquiv_symm_left L d χ x)

@[simp]
theorem intermediatePullbackProjection_right
    (x : intermediateLiftPullback L d χ) :
    (intermediatePullbackProjection L d χ x).right =
      intermediatePullbackStabilizer L d χ x :=
  rfl

/-- The ambient pullback projection is surjective. -/
theorem ambientPullbackProjection_surjective :
    Function.Surjective (ambientPullbackProjection L χ) :=
  (L.ambientSemidirectProjection_surjective χ).comp
    (ambientLiftPullbackEquiv L χ).symm.surjective

/-- The intermediate pullback projection is surjective. -/
theorem intermediatePullbackProjection_surjective :
    Function.Surjective
      (intermediatePullbackProjection L d χ) :=
  (intermediateSemidirectProjection_surjective L d χ).comp
    (intermediateLiftPullbackEquiv L d χ).symm.surjective

/-- The normal-coordinate inclusion into the ambient pullback. -/
def ambientPullbackNormalInclusion :
    A →* ambientLiftPullback L χ :=
  (ambientLiftPullbackEquiv L χ).toMonoidHom.comp
    (SemidirectProduct.inl :
      A →*
        A ⋊[L.liftedAmbientAction χ]
          PPrimeCharacterStabilizer S χ)

/-- The normal-coordinate inclusion into the intermediate pullback. -/
def intermediatePullbackNormalInclusion :
    d.intermediate →* intermediateLiftPullback L d χ :=
  (intermediateLiftPullbackEquiv L d χ).toMonoidHom.comp
    (SemidirectProduct.inl :
      d.intermediate →*
        d.intermediate ⋊[liftedIntermediateAction L d χ]
          PPrimeCharacterStabilizer S χ)

@[simp]
theorem ambientPullbackNormalInclusion_left
    (a : A) :
    (ambientPullbackNormalInclusion L χ a).1.left =
      a :=
  rfl

@[simp]
theorem ambientPullbackNormalInclusion_right
    (a : A) :
    (ambientPullbackNormalInclusion L χ a).1.right =
      1 := by
  change L.characterStabilizerLift χ 1 = 1
  exact map_one _

@[simp]
theorem intermediatePullbackNormalInclusion_left
    (a : d.intermediate) :
    (intermediatePullbackNormalInclusion L d χ a).1.left =
      a :=
  rfl

@[simp]
theorem intermediatePullbackNormalInclusion_right
    (a : d.intermediate) :
    (intermediatePullbackNormalInclusion L d χ a).1.right =
      1 := by
  change L.characterStabilizerLift χ 1 = 1
  exact map_one _

@[simp]
theorem ambientLiftPullbackEquiv_symm_normalInclusion
    (a : A) :
    (ambientLiftPullbackEquiv L χ).symm
        (ambientPullbackNormalInclusion L χ a) =
      (SemidirectProduct.inl a :
        A ⋊[L.liftedAmbientAction χ]
          PPrimeCharacterStabilizer S χ) := by
  change
    (ambientLiftPullbackEquiv L χ).symm
        (ambientLiftPullbackEquiv L χ
          (SemidirectProduct.inl a)) =
      SemidirectProduct.inl a
  exact (ambientLiftPullbackEquiv L χ).symm_apply_apply _

@[simp]
theorem intermediateLiftPullbackEquiv_symm_normalInclusion
    (a : d.intermediate) :
    (intermediateLiftPullbackEquiv L d χ).symm
        (intermediatePullbackNormalInclusion L d χ a) =
      (SemidirectProduct.inl a :
        d.intermediate ⋊[liftedIntermediateAction L d χ]
          PPrimeCharacterStabilizer S χ) := by
  change
    (intermediateLiftPullbackEquiv L d χ).symm
        (intermediateLiftPullbackEquiv L d χ
          (SemidirectProduct.inl a)) =
      SemidirectProduct.inl a
  exact (intermediateLiftPullbackEquiv L d χ).symm_apply_apply _

@[simp]
theorem ambientPullbackProjection_normalInclusion
    (a : A) :
    ambientPullbackProjection L χ
        (ambientPullbackNormalInclusion L χ a) =
      (SemidirectProduct.inl (E.projection a) :
        Q ⋊[PPrimeCharacterStabilizer.ambientAction]
          PPrimeCharacterStabilizer S χ) := by
  change
    L.ambientSemidirectProjection χ
        ((ambientLiftPullbackEquiv L χ).symm
          (ambientPullbackNormalInclusion L χ a)) =
      _
  rw [ambientLiftPullbackEquiv_symm_normalInclusion]
  rfl

@[simp]
theorem intermediatePullbackProjection_normalInclusion
    (a : d.intermediate) :
    intermediatePullbackProjection L d χ
        (intermediatePullbackNormalInclusion L d χ a) =
      (SemidirectProduct.inl
        (d.intermediateProjection E.projection a) :
        (L.quotientEquivariantLocalCorrespondence d).intermediate ⋊[
          projectedIntermediateAction L d χ]
          PPrimeCharacterStabilizer S χ) := by
  change
    intermediateSemidirectProjection L d χ
        ((intermediateLiftPullbackEquiv L d χ).symm
          (intermediatePullbackNormalInclusion L d χ a)) =
      _
  rw [intermediateLiftPullbackEquiv_symm_normalInclusion]
  rfl

/-- The ambient quotient kernel is exactly the copy of the original
central-extension kernel in the normal coordinate. -/
@[simp]
theorem ambientPullbackProjection_ker :
    (ambientPullbackProjection L χ).ker =
      E.projection.ker.map
        (ambientPullbackNormalInclusion L χ) := by
  ext x
  constructor
  · intro hx
    have hxOne :
        ambientPullbackProjection L χ x = 1 :=
      MonoidHom.mem_ker.mp hx
    have hxLeft : E.projection x.1.left = 1 := by
      simpa using congrArg SemidirectProduct.left hxOne
    have hxSelected :
        ambientPullbackStabilizer L χ x = 1 := by
      simpa using congrArg SemidirectProduct.right hxOne
    have hxRight : x.1.right = 1 := by
      rw [← characterStabilizerLift_ambientPullbackStabilizer
        L χ x, hxSelected, map_one]
    refine
      ⟨x.1.left, MonoidHom.mem_ker.mpr hxLeft, ?_⟩
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rw [ambientPullbackNormalInclusion_left]
    · rw [ambientPullbackNormalInclusion_right]
      exact hxRight.symm
  · rintro ⟨a, ha, rfl⟩
    apply MonoidHom.mem_ker.mpr
    rw [ambientPullbackProjection_normalInclusion]
    apply SemidirectProduct.ext
    · exact MonoidHom.mem_ker.mp ha
    · rfl

/-- The intermediate quotient kernel is exactly the copy of the restricted
central-extension kernel in the normal coordinate. -/
@[simp]
theorem intermediatePullbackProjection_ker :
    (intermediatePullbackProjection L d χ).ker =
      (d.intermediateProjection E.projection).ker.map
        (intermediatePullbackNormalInclusion L d χ) := by
  ext x
  constructor
  · intro hx
    have hxOne :
        intermediatePullbackProjection L d χ x = 1 :=
      MonoidHom.mem_ker.mp hx
    have hxLeft :
        (intermediatePullbackProjection L d χ x).left = 1 :=
      congrArg SemidirectProduct.left hxOne
    have hxSelected :
        intermediatePullbackStabilizer L d χ x = 1 := by
      simpa using congrArg SemidirectProduct.right hxOne
    have hxRight : x.1.right = 1 := by
      rw [←
        characterStabilizerLift_intermediatePullbackStabilizer
          L d χ x, hxSelected, map_one]
    let a : d.intermediate :=
      ⟨x.1.left.1, x.1.left.2⟩
    have ha :
        d.intermediateProjection E.projection a = 1 := by
      apply Subtype.ext
      have hval :=
        congrArg
          (fun z :
            (L.quotientEquivariantLocalCorrespondence d).intermediate =>
              (z : Q))
          hxLeft
      rw [intermediatePullbackProjection_left] at hval
      change E.projection (x.1.left : A) = 1 at hval
      exact hval
    refine
      ⟨a, MonoidHom.mem_ker.mpr ha, ?_⟩
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply Subtype.ext
      rfl
    · calc
        (intermediatePullbackNormalInclusion L d χ a).1.right =
            1 :=
          intermediatePullbackNormalInclusion_right L d χ a
        _ = x.1.right := hxRight.symm
  · rintro ⟨a, ha, rfl⟩
    apply MonoidHom.mem_ker.mpr
    rw [intermediatePullbackProjection_normalInclusion]
    apply SemidirectProduct.ext
    · exact MonoidHom.mem_ker.mp ha
    · rfl

/-- First-isomorphism identification of the ambient pullback quotient with
the actual downstairs ambient semidirect product. -/
def ambientPullbackQuotientEquiv :
    (ambientLiftPullback L χ ⧸
      (ambientPullbackProjection L χ).ker) ≃*
        (Q ⋊[PPrimeCharacterStabilizer.ambientAction]
          PPrimeCharacterStabilizer S χ) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (ambientPullbackProjection L χ)
    (ambientPullbackProjection_surjective L χ)

/-- First-isomorphism identification of the intermediate pullback quotient
with the actual downstairs intermediate semidirect product. -/
def intermediatePullbackQuotientEquiv :
    (intermediateLiftPullback L d χ ⧸
      (intermediatePullbackProjection L d χ).ker) ≃*
        ((L.quotientEquivariantLocalCorrespondence d).intermediate ⋊[
          projectedIntermediateAction L d χ]
          PPrimeCharacterStabilizer S χ) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (intermediatePullbackProjection L d χ)
    (intermediatePullbackProjection_surjective L d χ)

/-- The two chosen downstairs stabilizer coordinates agree under the
restricted canonical embedding. -/
theorem ambientPullbackStabilizer_restrictedSemidirectEmbedding
    (b : intermediateLiftPullback L d χ) :
    ambientPullbackStabilizer L χ
        (restrictedSemidirectEmbedding L d χ b) =
      intermediatePullbackStabilizer L d χ b := by
  apply L.characterStabilizerLift_injective χ
  rw [characterStabilizerLift_ambientPullbackStabilizer,
    characterStabilizerLift_intermediatePullbackStabilizer]
  rfl

/-- Projection commutes with the canonical intermediate embedding. -/
theorem pullbackProjection_restrictedSemidirectEmbedding
    (b : intermediateLiftPullback L d χ) :
    ambientPullbackProjection L χ
        (restrictedSemidirectEmbedding L d χ b) =
      (L.quotientEquivariantLocalCorrespondence d
          |>.semidirectEmbedding χ)
        (intermediatePullbackProjection L d χ b) := by
  apply SemidirectProduct.ext
  · rw [ambientPullbackProjection_left,
      EquivariantLocalCorrespondence.semidirectEmbedding_left,
      intermediatePullbackProjection_left]
    rfl
  · exact
      ambientPullbackStabilizer_restrictedSemidirectEmbedding
        L d χ b

end SylowAutomorphismLift
end InductiveMcKay
end McKayConjecture
