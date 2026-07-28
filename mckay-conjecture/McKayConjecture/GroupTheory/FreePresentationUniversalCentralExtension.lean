/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.FreePresentationCoverPerfect

/-!
# Universality of the free-presentation central cover

For a perfect group `S`, the central extension

`[F,F]/[F,R] → S`

is universal.  A lift to an arbitrary central extension is constructed by
choosing lifts of the free generators.  Elements of `R` then map to the
central kernel, so `[F,R]` is killed.  Uniqueness follows from perfectness
of the source.
-/

noncomputable section

open scoped commutatorElement

universe u

namespace McKayConjecture
namespace GroupTheory
namespace FreePresentation

variable {S : Type u} [Group S]
variable {V : Type u} [Group V]

/-- A chosen set-theoretic section of a central extension. -/
def targetSection
    (E : CentralExtension V S) :
    S → V :=
  fun s => Classical.choose (E.surjective s)

@[simp]
theorem projection_targetSection
    (E : CentralExtension V S)
    (s : S) :
    E.projection (targetSection E s) = s :=
  Classical.choose_spec (E.surjective s)

/-- The homomorphism from the free group obtained from the chosen lifts
of the generators. -/
def freeLift
    (E : CentralExtension V S) :
    Free S →* V :=
  FreeGroup.lift (targetSection E)

/-- The free lift commutes with evaluation. -/
theorem projection_comp_freeLift
    (E : CentralExtension V S) :
    E.projection.comp (freeLift E) =
      evaluation S := by
  apply FreeGroup.ext_hom
  intro s
  simp [freeLift]

/-- Relation words map into the central kernel of the target
extension. -/
theorem freeLift_mem_center_of_mem_relations
    (E : CentralExtension V S)
    {r : Free S}
    (hr : r ∈ relations S) :
    freeLift E r ∈ Subgroup.center V := by
  apply E.ker_le_center
  apply MonoidHom.mem_ker.mpr
  have h :=
    DFunLike.congr_fun
      (projection_comp_freeLift E) r
  change
    E.projection (freeLift E r) =
      evaluation S r at h
  exact h.trans (MonoidHom.mem_ker.mp hr)

/-- The free lift kills `[F,R]`. -/
theorem centralRelators_le_freeLift_ker
    (E : CentralExtension V S) :
    centralRelators S ≤
      (freeLift E).ker := by
  rw [centralRelators, Subgroup.commutator_le]
  intro f _ r hr
  apply MonoidHom.mem_ker.mpr
  rw [map_commutatorElement]
  apply
    commutatorElement_eq_one_iff_mul_comm.mpr
  exact
    Subgroup.mem_center_iff.mp
      (freeLift_mem_center_of_mem_relations E hr)
      (freeLift E f)

/-- The free lift restricted to `[F,F]`. -/
def derivedLift
    (E : CentralExtension V S) :
    derived S →* V :=
  (freeLift E).comp (derived S).subtype

/-- The subgroup `[F,R]` inside `[F,F]` is killed by the restricted
free lift. -/
theorem centralRelatorsInDerived_le_derivedLift_ker
    (E : CentralExtension V S) :
    centralRelatorsInDerived S ≤
      (derivedLift E).ker := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  exact
    MonoidHom.mem_ker.mp
      (centralRelators_le_freeLift_ker E hx)

/-- The canonical lift from the free-presentation cover to an arbitrary
central extension. -/
def coverLift
    (E : CentralExtension V S) :
    Cover S →* V :=
  QuotientGroup.lift
    (centralRelatorsInDerived S)
    (derivedLift E)
    (centralRelatorsInDerived_le_derivedLift_ker E)

/-- The canonical lift commutes with the projections to `S`. -/
theorem projection_comp_coverLift
    (E : CentralExtension V S) :
    E.projection.comp (coverLift E) =
      coverProjection S := by
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro d
  exact
    DFunLike.congr_fun
      (projection_comp_freeLift E) d.1

/-- The canonical lift is the unique homomorphism from the
free-presentation cover which commutes with the projections. -/
theorem coverLift_unique
    (E : CentralExtension V S)
    (hperfect : Group.IsPerfect S)
    (f : Cover S →* V)
    (hf :
      E.projection.comp f =
        coverProjection S) :
    f = coverLift E :=
  E.hom_ext_of_domain_perfect
    (cover_isPerfect S hperfect)
    f (coverLift E)
    (hf.trans (projection_comp_coverLift E).symm)

/-- The classical free-presentation construction of a universal central
extension of a perfect group. -/
def universalCentralExtension
    (hperfect : Group.IsPerfect S) :
    UniversalCentralExtension (Cover S) S where
  toCentralExtension :=
    centralExtension S hperfect
  sourcePerfect :=
    cover_isPerfect S hperfect
  lift V _ E := by
    refine
      ⟨coverLift E,
        projection_comp_coverLift E, ?_⟩
    intro f hf
    exact coverLift_unique E hperfect f hf

end FreePresentation
end GroupTheory
end McKayConjecture
