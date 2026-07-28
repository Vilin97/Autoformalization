/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedGeneralExistence
import McKayConjecture.CharacterTriple.InvariantExtensionIntertwinerComparison
import McKayConjecture.CharacterTriple.Inertia
import McKayConjecture.Character.OverAlongTransport

/-!
# Comparing kernel intertwiners with inertia-triple operators

An irreducible character of `N` which extends along `i : N → A` has a
canonical realization equivalence with the normal character in the inertia
triple of the extension character.  If an external group acts compatibly on
`N` and on that inertia triple, Schur uniqueness compares its canonical
kernel intertwiners with the canonical associated inertia operators.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedExistence

variable {G : Type} [Group G] [Finite G]
variable (A : Subgroup G) [A.Normal]
variable {N : Type} [Group N] [Finite N]
variable (chi : IrreducibleCharacter N)
variable (i : N →* A)
variable (psi : IrreducibleCharacter A)
variable (hpsi :
  IrreducibleCharacter.IsExtensionAlong i chi psi)

noncomputable local instance inertiaExtensionComparisonFintype :
    Fintype G :=
  Fintype.ofFinite G

/-- Include the extension source in the canonical normal copy inside the
inertia group of the extension character. -/
def extensionToInertiaNormalHom :
    N →* (ofInertia A psi).normalSubgroup :=
  (CliffordEquivalence.inertiaNormalCopyEquiv
    A psi).symm.toMonoidHom.comp i

/-- The extension-restriction equivalence, followed by transport to the
canonical normal-character realization in the inertia triple. -/
def extensionRestrictionEquivInertiaCopy :
    Representation.Equiv
      chi.realization.ρ
      ((ofInertia A psi).character.realization.ρ.comp
        (extensionToInertiaNormalHom A i psi)) := by
  let eExtension :=
    extensionRestrictionEquiv chi i psi hpsi
  let eCopy :=
    FDRep.representationEquivOfIso
      (CliffordEquivalence.inertiaCopyRealizationIso A psi)
  apply Representation.Equiv.mk
    (eExtension.toLinearEquiv.trans
      eCopy.toLinearEquiv.symm)
  intro n
  apply LinearMap.ext
  intro z
  have hExtension :=
    LinearMap.congr_fun
      (eExtension.isIntertwining' n) z
  have hCopy :=
    LinearMap.congr_fun
      (eCopy.symm.isIntertwining'
        (extensionToInertiaNormalHom A i psi n))
      (eExtension z)
  change
    eCopy.symm (eExtension (chi.realization.ρ n z)) =
    (CliffordEquivalence.inertiaCopyCharacter A psi).realization.ρ
          (extensionToInertiaNormalHom A i psi n)
        (eCopy.symm (eExtension z))
  change
    eExtension (chi.realization.ρ n z) =
      psi.realization.ρ (i n) (eExtension z)
      at hExtension
  change
    eCopy.symm
        (psi.realization.ρ
          (CliffordEquivalence.inertiaNormalCopyEquiv A psi
            (extensionToInertiaNormalHom A i psi n))
          (eExtension z)) =
      (CliffordEquivalence.inertiaCopyCharacter
          A psi).realization.ρ
        (extensionToInertiaNormalHom A i psi n)
        (eCopy.symm (eExtension z))
      at hCopy
  rw [hExtension]
  have hcoordinate :
      CliffordEquivalence.inertiaNormalCopyEquiv A psi
          (extensionToInertiaNormalHom A i psi n) =
        i n := by
    change
      CliffordEquivalence.inertiaNormalCopyEquiv A psi
          ((CliffordEquivalence.inertiaNormalCopyEquiv
            A psi).symm (i n)) =
        i n
    exact
      (CliffordEquivalence.inertiaNormalCopyEquiv
        A psi).apply_symm_apply (i n)
  rw [hcoordinate] at hCopy
  exact hCopy

variable {Γ : Type} [Group Γ] [Finite Γ]
variable (alpha : Γ →* MulAut N)
variable (hchi : IsInvariant alpha chi)

/-- Full-inertia Schur comparison.  The scalar is constructed, not assumed:
the only input is the equality of the two induced normal conjugations. -/
theorem exists_inertiaExtensionIntertwinerScalar
    (ambient :
      Γ → IrreducibleCharacter.inertia A psi)
    (hconj :
      ∀ (gamma : Γ) (n : N),
        extensionToInertiaNormalHom A i psi
            (alpha gamma n) =
          MulAut.conjNormal (ambient gamma)
            (extensionToInertiaNormalHom A i psi n))
    (gamma : Γ) :
    ∃ c : ℂˣ, ∀ z : chi.realization,
      extensionRestrictionEquivInertiaCopy
          A chi i psi hpsi
          (intertwiner alpha chi hchi gamma z) =
        (c : ℂ) •
          (AssociatedGeneralExistence.projectiveRepresentation
            (ofInertia A psi)).operator
              (ambient gamma)
              (extensionRestrictionEquivInertiaCopy
                A chi i psi hpsi z) := by
  exact
    exists_intertwiner_scalar_of_associated_along
      alpha chi hchi
      (AssociatedGeneralExistence.associated
        (ofInertia A psi))
      (extensionToInertiaNormalHom A i psi)
      (extensionRestrictionEquivInertiaCopy
        A chi i psi hpsi)
      ambient hconj gamma

end AssociatedExistence
end CharacterTriple
end McKayConjecture
