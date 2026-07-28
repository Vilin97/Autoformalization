/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveStableSubspace
import Mathlib.RepresentationTheory.Invariants

/-!
# Scalar summands as spaces of intertwining maps

Suppose the restriction of a projective operator family to a subgroup is
a nonzero scalar cochain times the ordinary conjugation action on a linear
Hom-space.  Its simultaneous scalar summand is then exactly the invariant
subspace of that ordinary Hom representation.  Mathlib's
`Representation.invariantsEquivIntertwiningMap` identifies this with the
corresponding space of intertwining maps.

This is the linear-algebra step used in the DGN comparison: it selects the
correct Sylow eigenspace inside a kernel Hom-space, without asserting that
the entire kernel Hom-space has the dimension of the final multiplicity
space.
-/

noncomputable section

universe u v w x

open CategoryTheory

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K : Type u} [Field K]
variable {G : Type v} [Group G]
variable {H : Type w} [Group H]
variable {M V W : Type x}
variable [AddCommGroup M] [Module K M]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- If a restricted projective operator is a nonzero scalar times an
honest representation, its scalar summand is exactly the invariant
subspace of that honest representation. -/
def scalarRestrictionSubmoduleEquivInvariants
    (P : ProjectiveRepresentation K G M)
    (j : H →* G)
    (mu : H → Kˣ)
    (R : Representation K H M)
    (hoperator :
      ∀ (h : H) (m : M),
        P.operator (j h) m =
          (mu h : K) •
            R h m) :
    scalarRestrictionSubmodule P j mu ≃ₗ[K]
      R.invariants where
  toFun m :=
    ⟨m, fun h ↦ by
      apply
        smul_right_injective
          M
          (show (mu h : K) ≠ 0 from Units.ne_zero (mu h))
      exact
        (hoperator h m).symm.trans
          (m.property h)⟩
  invFun m :=
    ⟨m, fun h ↦ by
      rw [hoperator h m]
      rw [m.property h]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem scalarRestrictionSubmoduleEquivInvariants_apply_coe
    (P : ProjectiveRepresentation K G M)
    (j : H →* G)
    (mu : H → Kˣ)
    (R : Representation K H M)
    (hoperator :
      ∀ (h : H) (m : M),
        P.operator (j h) m =
          (mu h : K) •
            R h m)
    (f : scalarRestrictionSubmodule P j mu) :
    ((scalarRestrictionSubmoduleEquivInvariants
      P j mu R hoperator f : R.invariants) : M) =
        (f : M) :=
  rfl

/-- Direct form of the selected-summand equivalence: the scalar summand
is the space of maps intertwining the two honest subgroup
representations. -/
def scalarRestrictionSubmoduleEquivIntertwiningMap
    (P : ProjectiveRepresentation K G (V →ₗ[K] W))
    (j : H →* G)
    (mu : H → Kˣ)
    (rho : Representation K H V)
    (sigma : Representation K H W)
    (hoperator :
      ∀ (h : H) (f : V →ₗ[K] W),
        P.operator (j h) f =
          (mu h : K) •
            Representation.linHom rho sigma h f) :
    scalarRestrictionSubmodule P j mu ≃ₗ[K]
      Representation.IntertwiningMap rho sigma :=
  (scalarRestrictionSubmoduleEquivInvariants
    P j mu (Representation.linHom rho sigma)
      hoperator).trans
      (Representation.invariantsEquivIntertwiningMap
        rho sigma)

/-- Categorical finite-dimensional form.  This is the version used for
character realizations in the DGN comparison. -/
def scalarRestrictionSubmoduleEquivFDRepHom
    (X Y : FDRep K H)
    (P :
      ProjectiveRepresentation K G
        (X.V →ₗ[K] Y.V))
    (j : H →* G)
    (mu : H → Kˣ)
    (hoperator :
      ∀ (h : H) (f : X.V →ₗ[K] Y.V),
        P.operator (j h) f =
          (mu h : K) •
            Representation.linHom X.ρ Y.ρ h f) :
    scalarRestrictionSubmodule P j mu ≃ₗ[K]
      (X ⟶ Y) :=
  (scalarRestrictionSubmoduleEquivInvariants
    P j mu (Representation.linHom X.ρ Y.ρ)
      hoperator).trans
    (Representation.linHom.invariantsEquivFDRepHom
      X Y)

@[simp]
theorem scalarRestrictionSubmoduleEquivIntertwiningMap_apply_coe
    (P : ProjectiveRepresentation K G (V →ₗ[K] W))
    (j : H →* G)
    (mu : H → Kˣ)
    (rho : Representation K H V)
    (sigma : Representation K H W)
    (hoperator :
      ∀ (h : H) (f : V →ₗ[K] W),
        P.operator (j h) f =
          (mu h : K) •
            Representation.linHom rho sigma h f)
    (f : scalarRestrictionSubmodule P j mu) :
    (scalarRestrictionSubmoduleEquivIntertwiningMap
      P j mu rho sigma hoperator f :
        V →ₗ[K] W) =
      (f : V →ₗ[K] W) :=
  rfl

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
