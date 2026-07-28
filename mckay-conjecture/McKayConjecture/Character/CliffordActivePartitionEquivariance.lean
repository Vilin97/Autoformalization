/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.Hom
import McKayConjecture.Character.CliffordActivePartition

/-!
# Equivariance of active Clifford-partition correspondences

An `ActivePPrimeOrbitwiseCorrespondence` is equivariant exactly when its
dependent-sum equivalence is equivariant after transporting the source
and target actions through their exact active Clifford partitions.

This is the active-orbit analogue of the all-orbit coordinate criterion.
Only active, hence nonempty, prime-to-`p` blocks occur.

The underlying character-partition API is Type-0, so the groups in this
module remain in `Type`.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordPartition
namespace ActivePPrimeOrbitwiseCorrespondence

variable {G₁ G₂ : Type}
variable [Group G₁] [Group G₂]
variable [Fintype G₁] [Fintype G₂]
variable {N₁ : Subgroup G₁} {N₂ : Subgroup G₂}
variable [N₁.Normal] [N₂.Normal]
variable {p : ℕ}

section Equivariance

variable {A : Type} [Group A]
variable [MulAction A (PPrimeIrreducibleCharacter G₁ p)]
variable [MulAction A (PPrimeIrreducibleCharacter G₂ p)]

/-- Equivariance expressed entirely in exact active Clifford sigma
coordinates. -/
def SigmaEquivariant
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p) :
    Prop :=
  ∀ (a : A)
    (x : Σ q : ActiveOrbit N₁ p,
      PPrimeOrbitBlock N₁ p q.1),
    d.sigmaEquiv
        (pPrimeActiveOrbitBlockSigmaEquiv N₁ p
          (a •
            (pPrimeActiveOrbitBlockSigmaEquiv
              N₁ p).symm x)) =
      pPrimeActiveOrbitBlockSigmaEquiv N₂ p
        (a •
          (pPrimeActiveOrbitBlockSigmaEquiv
            N₂ p).symm (d.sigmaEquiv x))

/-- The active sigma-coordinate criterion is equivalent to ordinary
equivariance of the assembled character correspondence. -/
theorem sigmaEquivariant_iff
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p) :
    d.SigmaEquivariant (A := A) ↔
      ∀ (a : A)
        (χ : PPrimeIrreducibleCharacter G₁ p),
        d.assemble (a • χ) =
          a • d.assemble χ := by
  constructor
  · intro h a χ
    apply
      (pPrimeActiveOrbitBlockSigmaEquiv
        N₂ p).injective
    simpa only [decompose_assemble, assemble_apply,
      Equiv.symm_apply_apply,
      Equiv.apply_symm_apply] using
      h a
        (pPrimeActiveOrbitBlockSigmaEquiv
          N₁ p χ)
  · intro h a x
    obtain ⟨χ, rfl⟩ :=
      (pPrimeActiveOrbitBlockSigmaEquiv
        N₁ p).surjective x
    simpa only [Equiv.symm_apply_apply,
      decompose_assemble, Equiv.apply_symm_apply,
      assemble_apply] using
      congrArg
        (pPrimeActiveOrbitBlockSigmaEquiv N₂ p)
        (h a χ)

/-- Package an active sigma-coordinate certificate as a bundled
equivariant map. -/
def toMulActionHom
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (h : d.SigmaEquivariant (A := A)) :
    PPrimeIrreducibleCharacter G₁ p →[A]
      PPrimeIrreducibleCharacter G₂ p where
  toFun := d.assemble
  map_smul' := d.sigmaEquivariant_iff.mp h

@[simp]
theorem toMulActionHom_apply
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (h : d.SigmaEquivariant (A := A))
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    d.toMulActionHom h χ =
      d.assemble χ :=
  rfl

end Equivariance

end ActivePPrimeOrbitwiseCorrespondence
end CliffordPartition
end McKayConjecture
