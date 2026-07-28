/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.UniversalCoverDominatesPerfectCover

/-!
# Uniqueness of the source of a universal central extension

Two universal central extensions of the same group have canonically
isomorphic source groups.  The isomorphism is the unique map over the
common target supplied by either universal property.

This is the transport bridge needed when a family verification chooses one
convenient universal cover, whereas the public inductive-McKay hypothesis
quantifies over every universal cover.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory
namespace UniversalCentralExtension

variable {U V S : Type u}
variable [Group U] [Group V] [Group S]

/-- The canonical endomorphism of the source of a universal central
extension is the identity. -/
theorem mapToSelf_eq_id
    (E : UniversalCentralExtension U S) :
    E.mapToCentralExtension E.toCentralExtension =
      MonoidHom.id U := by
  symm
  apply E.mapToCentralExtension_unique E.toCentralExtension
  rfl

/-- The canonical maps between two universal covers of the same target are
mutual inverses, in the direction starting at the first cover. -/
theorem reverseMap_comp_map_eq_id
    (E : UniversalCentralExtension U S)
    (F : UniversalCentralExtension V S) :
    (F.mapToCentralExtension E.toCentralExtension).comp
        (E.mapToCentralExtension F.toCentralExtension) =
      MonoidHom.id U := by
  calc
    (F.mapToCentralExtension E.toCentralExtension).comp
          (E.mapToCentralExtension F.toCentralExtension) =
        E.mapToCentralExtension E.toCentralExtension := by
      apply E.mapToCentralExtension_unique E.toCentralExtension
      ext u
      have hFE :=
        DFunLike.congr_fun
          (F.mapToCentralExtension_commutes
            E.toCentralExtension)
          (E.mapToCentralExtension
            F.toCentralExtension u)
      have hEF :=
        DFunLike.congr_fun
          (E.mapToCentralExtension_commutes
            F.toCentralExtension)
          u
      exact hFE.trans hEF
    _ = MonoidHom.id U := E.mapToSelf_eq_id

/-- The canonical multiplicative equivalence between the sources of two
universal central extensions of the same target. -/
def sourceEquiv
    (E : UniversalCentralExtension U S)
    (F : UniversalCentralExtension V S) :
    U ≃* V where
  toFun :=
    E.mapToCentralExtension F.toCentralExtension
  invFun :=
    F.mapToCentralExtension E.toCentralExtension
  left_inv u := by
    have h :=
      DFunLike.congr_fun
        (E.reverseMap_comp_map_eq_id F) u
    simpa using h
  right_inv v := by
    have h :=
      DFunLike.congr_fun
        (F.reverseMap_comp_map_eq_id E) v
    simpa using h
  map_mul' x y :=
    map_mul
      (E.mapToCentralExtension F.toCentralExtension)
      x y

@[simp]
theorem sourceEquiv_apply
    (E : UniversalCentralExtension U S)
    (F : UniversalCentralExtension V S)
    (u : U) :
    E.sourceEquiv F u =
      E.mapToCentralExtension F.toCentralExtension u :=
  rfl

/-- The canonical source equivalence commutes with the projections to the
common target. -/
theorem sourceEquiv_commutes
    (E : UniversalCentralExtension U S)
    (F : UniversalCentralExtension V S) :
    F.toCentralExtension.projection.comp
        (E.sourceEquiv F).toMonoidHom =
      E.toCentralExtension.projection :=
  E.mapToCentralExtension_commutes F.toCentralExtension

@[simp]
theorem sourceEquiv_symm
    (E : UniversalCentralExtension U S)
    (F : UniversalCentralExtension V S) :
    (E.sourceEquiv F).symm =
      F.sourceEquiv E :=
  rfl

end UniversalCentralExtension
end GroupTheory
end McKayConjecture
