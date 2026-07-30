/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetSquarefreeOrderVanishing
import McKayConjecture.GroupTheory.CentralKernelAbelianSylowSection

/-!
# Gluing Sylow-local splittings of a factor set

Let `α` be a normalized factor set on a finite abelian group `G`.  The
central extension attached to the pullback of `α` to a Sylow subgroup maps
coordinatewise to the central extension attached to `α`.  Consequently,
homomorphic sections of all Sylow-restricted factor-set extensions give
Sylow-local sections of the ambient projection.

The elementary central-kernel gluing theorem then produces a global
homomorphic section.  Reading its coefficient coordinate gives a normalized
gauge which makes `α` trivial.

This is a cochain-level local--global theorem.  It avoids any appeal to a
restriction--corestriction map in group cohomology.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

universe u v w

variable {G : Type u} {H : Type v} {A : Type w}
variable [CommGroup A]

namespace CentralExtensionGroup

variable [Group G] [Group H]

/-- A gauge trivialization of a normalized factor set is automatically
normalized at the identity. -/
theorem gaugeCochain_one
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (c : G → A)
    (hc : alpha.gauge c = FactorSet.one) :
    c 1 = 1 := by
  have hvalue :=
    congrArg
      (fun beta : FactorSet G A => beta 1 1)
      hc
  simpa [halpha.1 1] using hvalue

/-- A trivializing gauge gives the corresponding multiplicative section
of the concrete factor-set central extension. -/
def sectionOfGauge
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (c : G → A)
    (hc : alpha.gauge c = FactorSet.one) :
    G →* CentralExtensionGroup alpha halpha where
  toFun g := mk alpha halpha g (c g)
  map_one' := by
    apply ext alpha halpha
    · rfl
    · exact gaugeCochain_one alpha halpha c hc
  map_mul' g h := by
    apply ext alpha halpha
    · rfl
    · change
        c (g * h) =
          alpha g h * c g * c h
      symm
      have hvalue :=
        congrArg
          (fun beta : FactorSet G A => beta g h)
          hc
      simp only [gauge_apply, one_apply] at hvalue
      have hmul :=
        congrArg (fun z : A => z * c (g * h)) hvalue
      simpa [
        div_eq_mul_inv,
        mul_assoc,
        mul_comm,
        mul_left_comm
      ] using hmul

@[simp]
theorem sectionOfGauge_base
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (c : G → A)
    (hc : alpha.gauge c = FactorSet.one)
    (g : G) :
    base alpha halpha
        (sectionOfGauge alpha halpha c hc g) =
      g :=
  rfl

@[simp]
theorem sectionOfGauge_coefficient
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (c : G → A)
    (hc : alpha.gauge c = FactorSet.one)
    (g : G) :
    coefficient alpha halpha
        (sectionOfGauge alpha halpha c hc g) =
      c g :=
  rfl

/-- The section constructed from a gauge is a right inverse to the base
projection. -/
theorem projection_comp_sectionOfGauge
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (c : G → A)
    (hc : alpha.gauge c = FactorSet.one) :
    (projection alpha halpha).comp
        (sectionOfGauge alpha halpha c hc) =
      MonoidHom.id G := by
  rfl

/-- A normalized factor set is cohomologous to the constant-one factor set
exactly when its concrete central extension admits a multiplicative section.

This packages both directions of the cochain/section dictionary in the
orientation used by `FactorSet.Cohomologous`. -/
theorem cohomologous_one_iff_exists_section
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized) :
    alpha.Cohomologous FactorSet.one ↔
      ∃ s : G →* CentralExtensionGroup alpha halpha,
        (projection alpha halpha).comp s =
          MonoidHom.id G := by
  constructor
  · rintro ⟨c, hc⟩
    exact
      ⟨sectionOfGauge alpha halpha c hc.symm,
        projection_comp_sectionOfGauge
          alpha halpha c hc.symm⟩
  · rintro ⟨s, hs⟩
    refine
      ⟨fun g ↦ coefficient alpha halpha (s g), ?_⟩
    exact
      (gauge_coefficient_section_eq_one
        alpha halpha s hs).symm

/-- Pulling a normalized factor set back along `f : H →* G` induces the
coordinatewise homomorphism between the corresponding concrete central
extensions. -/
def comapHom
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (f : H →* G) :
    CentralExtensionGroup
        (alpha.comap f)
        (alpha.comap_isNormalized f halpha) →*
      CentralExtensionGroup alpha halpha where
  toFun x :=
    mk alpha halpha
      (f
        (base
          (alpha.comap f)
          (alpha.comap_isNormalized f halpha)
          x))
      (coefficient
        (alpha.comap f)
        (alpha.comap_isNormalized f halpha)
        x)
  map_one' := by
    apply ext alpha halpha
    · simp
    · rfl
  map_mul' x y := by
    apply ext alpha halpha
    · simp
    · rfl

@[simp]
theorem comapHom_base
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (f : H →* G)
    (x :
      CentralExtensionGroup
        (alpha.comap f)
        (alpha.comap_isNormalized f halpha)) :
    base alpha halpha (comapHom alpha halpha f x) =
      f
        (base
          (alpha.comap f)
          (alpha.comap_isNormalized f halpha)
          x) :=
  rfl

@[simp]
theorem comapHom_coefficient
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (f : H →* G)
    (x :
      CentralExtensionGroup
        (alpha.comap f)
        (alpha.comap_isNormalized f halpha)) :
    coefficient alpha halpha (comapHom alpha halpha f x) =
      coefficient
        (alpha.comap f)
        (alpha.comap_isNormalized f halpha)
        x :=
  rfl

/-- The coordinatewise map between central extensions commutes with their
base projections. -/
theorem projection_comp_comapHom
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (f : H →* G) :
    (projection alpha halpha).comp
        (comapHom alpha halpha f) =
      f.comp
        (projection
          (alpha.comap f)
          (alpha.comap_isNormalized f halpha)) := by
  rfl

end CentralExtensionGroup

variable [CommGroup G]

/-- Every Sylow restriction of a normalized factor set has a homomorphically
split concrete central extension. -/
def HasSylowRestrictionSections
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized) : Prop :=
  ∀ (r : ℕ) (hr : r.Prime),
    letI : Fact r.Prime := ⟨hr⟩
    ∀ R : Sylow r G,
      ∃ s :
          R →*
            CentralExtensionGroup
              (alpha.comap (R : Subgroup G).subtype)
              (alpha.comap_isNormalized
                (R : Subgroup G).subtype halpha),
        (CentralExtensionGroup.projection
            (alpha.comap (R : Subgroup G).subtype)
            (alpha.comap_isNormalized
              (R : Subgroup G).subtype halpha)).comp s =
          MonoidHom.id R

/-- Sections of the actual Sylow-restricted factor-set extensions induce
the ambient Sylow-local sections required by the elementary gluing theorem. -/
theorem hasSylowSections_of_hasSylowRestrictionSections
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (hlocal :
      HasSylowRestrictionSections alpha halpha) :
    GroupTheory.HasSylowSections
      (CentralExtensionGroup.projection alpha halpha) := by
  intro r hr
  letI : Fact r.Prime := ⟨hr⟩
  intro R
  obtain ⟨s, hs⟩ := hlocal r hr R
  refine
    ⟨(CentralExtensionGroup.comapHom
        alpha halpha (R : Subgroup G).subtype).comp s,
      ?_⟩
  apply MonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun hs x
  have hx' :
      CentralExtensionGroup.projection
          (alpha.comap (R : Subgroup G).subtype)
          (alpha.comap_isNormalized
            (R : Subgroup G).subtype halpha)
          (s x) =
        x := by
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using hx
  change
    CentralExtensionGroup.projection alpha halpha
        (CentralExtensionGroup.comapHom
          alpha halpha (R : Subgroup G).subtype (s x)) =
      (x : G)
  change
    ((R : Subgroup G).subtype)
        (CentralExtensionGroup.projection
          (alpha.comap (R : Subgroup G).subtype)
          (alpha.comap_isNormalized
            (R : Subgroup G).subtype halpha)
          (s x)) =
      (x : G)
  rw [hx']
  rfl

variable [Finite G]

/-- The explicit global section obtained by gluing sections of all Sylow
restrictions of a normalized factor set on a finite abelian group. -/
def gluedAbelianSylowFactorSetSection
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (hlocal :
      HasSylowRestrictionSections alpha halpha) :
    G →* CentralExtensionGroup alpha halpha :=
  GroupTheory.gluedAbelianSylowSection
    (CentralExtensionGroup.projection alpha halpha)
    (CentralExtensionGroup.projection_ker_le_center
      alpha halpha)
    (hasSylowSections_of_hasSylowRestrictionSections
      alpha halpha hlocal)

/-- The glued section is a right inverse to the factor-set central-extension
projection. -/
theorem projection_comp_gluedAbelianSylowFactorSetSection
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (hlocal :
      HasSylowRestrictionSections alpha halpha) :
    (CentralExtensionGroup.projection alpha halpha).comp
        (gluedAbelianSylowFactorSetSection
          alpha halpha hlocal) =
      MonoidHom.id G :=
  GroupTheory.projection_comp_gluedAbelianSylowSection
    (CentralExtensionGroup.projection alpha halpha)
    (CentralExtensionGroup.projection_ker_le_center
      alpha halpha)
    (hasSylowSections_of_hasSylowRestrictionSections
      alpha halpha hlocal)

/-- Existence form of the Sylow-local to global splitting theorem for
normalized factor sets on finite abelian groups. -/
theorem exists_centralExtensionGroup_section_of_hasSylowRestrictionSections
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (hlocal :
      HasSylowRestrictionSections alpha halpha) :
    ∃ s : G →* CentralExtensionGroup alpha halpha,
      (CentralExtensionGroup.projection alpha halpha).comp s =
        MonoidHom.id G :=
  ⟨gluedAbelianSylowFactorSetSection alpha halpha hlocal,
    projection_comp_gluedAbelianSylowFactorSetSection
      alpha halpha hlocal⟩

/-- Sylow-local splitting trivializes the ambient factor set by a gauge. -/
theorem exists_gauge_eq_one_of_hasSylowRestrictionSections
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (hlocal :
      HasSylowRestrictionSections alpha halpha) :
    ∃ c : G → A,
      alpha.gauge c = FactorSet.one := by
  let s :=
    gluedAbelianSylowFactorSetSection
      alpha halpha hlocal
  refine
    ⟨fun g ↦
        CentralExtensionGroup.coefficient
          alpha halpha (s g),
      ?_⟩
  exact
    CentralExtensionGroup.gauge_coefficient_section_eq_one
      alpha halpha s
      (projection_comp_gluedAbelianSylowFactorSetSection
        alpha halpha hlocal)

/-- The gauge trivializing the ambient factor set can be chosen normalized at
the identity. -/
theorem exists_normalized_gauge_eq_one_of_hasSylowRestrictionSections
    (alpha : FactorSet G A)
    (halpha : alpha.IsNormalized)
    (hlocal :
      HasSylowRestrictionSections alpha halpha) :
    ∃ c : G → A,
      c 1 = 1 ∧
        alpha.gauge c = FactorSet.one := by
  let s :=
    gluedAbelianSylowFactorSetSection
      alpha halpha hlocal
  refine
    ⟨fun g ↦
        CentralExtensionGroup.coefficient
          alpha halpha (s g),
      ?_,
      ?_⟩
  · simp [s]
  · exact
      CentralExtensionGroup.gauge_coefficient_section_eq_one
        alpha halpha s
        (projection_comp_gluedAbelianSylowFactorSetSection
          alpha halpha hlocal)

end FactorSet
end CharacterTriple
end McKayConjecture
