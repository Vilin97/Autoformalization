/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordActiveEquivalenceTransport

/-!
# Naturality of active Clifford-partition correspondences

This file gives a reusable commuting-square criterion for assembled
`ActivePPrimeOrbitwiseCorrespondence`s.  A square commutes when:

1. its active-orbit index equivalences commute; and
2. its block equivalences commute over those dependent indices.

The block condition is stated with heterogeneous equality, so clients do
not have to write transports between propositionally equal orbit fibres.
These two conditions imply commutativity first in exact active sigma
coordinates and then for the assembled equivalences of prime-to-`p`
characters.

The final theorem specializes the criterion to vertical transport along
commuting equivalences of ambient groups and normal subgroups.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordPartition
namespace ActivePPrimeOrbitwiseCorrespondence

variable {G₁ G₂ G₁' G₂' : Type}
variable [Group G₁] [Group G₂] [Group G₁'] [Group G₂']
variable [Fintype G₁] [Fintype G₂] [Fintype G₁'] [Fintype G₂']
variable {N₁ : Subgroup G₁} {N₂ : Subgroup G₂}
variable {N₁' : Subgroup G₁'} {N₂' : Subgroup G₂'}
variable [N₁.Normal] [N₂.Normal] [N₁'.Normal] [N₂'.Normal]
variable {p : ℕ}

/-- Indexwise and blockwise data certifying a commuting square of active
orbitwise correspondences.

The two routes around the square are `sourceTransport` followed by
`bottom`, and `top` followed by `targetTransport`. -/
structure NaturalitySquare
    (sourceTransport :
      ActivePPrimeOrbitwiseCorrespondence N₁ N₁' p)
    (targetTransport :
      ActivePPrimeOrbitwiseCorrespondence N₂ N₂' p)
    (top : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (bottom : ActivePPrimeOrbitwiseCorrespondence N₁' N₂' p) :
    Prop where
  /-- The two routes induce the same active orbit index. -/
  index_commutes :
    ∀ q : ActiveOrbit N₁ p,
      bottom.activeOrbitEquiv
          (sourceTransport.activeOrbitEquiv q) =
        targetTransport.activeOrbitEquiv
          (top.activeOrbitEquiv q)
  /-- The two routes induce the same block element over the equal target
  indices.  `HEq` avoids exposing a choice of dependent transport. -/
  block_commutes :
    ∀ (q : ActiveOrbit N₁ p)
      (χ : PPrimeOrbitBlock N₁ p q.1),
      HEq
        (bottom.blockEquiv
          (sourceTransport.activeOrbitEquiv q)
          (sourceTransport.blockEquiv q χ))
        (targetTransport.blockEquiv
          (top.activeOrbitEquiv q)
          (top.blockEquiv q χ))

omit [Fintype G₁] [Fintype G₂] [Fintype G₁'] [Fintype G₂'] in
/-- Indexwise and blockwise commutativity is exactly enough to make the
dependent-sum square commute. -/
theorem NaturalitySquare.sigmaEquiv_commutes
    {sourceTransport :
      ActivePPrimeOrbitwiseCorrespondence N₁ N₁' p}
    {targetTransport :
      ActivePPrimeOrbitwiseCorrespondence N₂ N₂' p}
    {top : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p}
    {bottom : ActivePPrimeOrbitwiseCorrespondence N₁' N₂' p}
    (h : NaturalitySquare
      sourceTransport targetTransport top bottom)
    (x : Σ q : ActiveOrbit N₁ p,
      PPrimeOrbitBlock N₁ p q.1) :
    bottom.sigmaEquiv (sourceTransport.sigmaEquiv x) =
      targetTransport.sigmaEquiv (top.sigmaEquiv x) := by
  rcases x with ⟨q, χ⟩
  exact Sigma.ext
    (h.index_commutes q)
    (h.block_commutes q χ)

omit [Fintype G₁] [Fintype G₂] [Fintype G₁'] [Fintype G₂'] in
/-- Equivalence-level form of commutativity in active sigma
coordinates. -/
theorem NaturalitySquare.sigmaEquiv_trans
    {sourceTransport :
      ActivePPrimeOrbitwiseCorrespondence N₁ N₁' p}
    {targetTransport :
      ActivePPrimeOrbitwiseCorrespondence N₂ N₂' p}
    {top : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p}
    {bottom : ActivePPrimeOrbitwiseCorrespondence N₁' N₂' p}
    (h : NaturalitySquare
      sourceTransport targetTransport top bottom) :
    sourceTransport.sigmaEquiv.trans bottom.sigmaEquiv =
      top.sigmaEquiv.trans targetTransport.sigmaEquiv :=
  Equiv.ext h.sigmaEquiv_commutes

/-- A commuting square in exact active sigma coordinates assembles to a
commuting square of equivalences of prime-to-`p` characters. -/
theorem assemble_comp_commutes_of_sigmaEquiv_commutes
    (sourceTransport :
      ActivePPrimeOrbitwiseCorrespondence N₁ N₁' p)
    (targetTransport :
      ActivePPrimeOrbitwiseCorrespondence N₂ N₂' p)
    (top : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (bottom : ActivePPrimeOrbitwiseCorrespondence N₁' N₂' p)
    (h :
      ∀ x : Σ q : ActiveOrbit N₁ p,
        PPrimeOrbitBlock N₁ p q.1,
        bottom.sigmaEquiv (sourceTransport.sigmaEquiv x) =
          targetTransport.sigmaEquiv (top.sigmaEquiv x)) :
    sourceTransport.assemble.trans bottom.assemble =
      top.assemble.trans targetTransport.assemble := by
  ext χ
  apply (pPrimeActiveOrbitBlockSigmaEquiv N₂' p).injective
  simpa only [Equiv.trans_apply, decompose_assemble] using
    h (pPrimeActiveOrbitBlockSigmaEquiv N₁ p χ)

/-- The assembled covariance theorem associated to an indexwise and
blockwise naturality certificate. -/
theorem NaturalitySquare.assemble_commutes
    {sourceTransport :
      ActivePPrimeOrbitwiseCorrespondence N₁ N₁' p}
    {targetTransport :
      ActivePPrimeOrbitwiseCorrespondence N₂ N₂' p}
    {top : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p}
    {bottom : ActivePPrimeOrbitwiseCorrespondence N₁' N₂' p}
    (h : NaturalitySquare
      sourceTransport targetTransport top bottom) :
    sourceTransport.assemble.trans bottom.assemble =
      top.assemble.trans targetTransport.assemble :=
  assemble_comp_commutes_of_sigmaEquiv_commutes
    sourceTransport targetTransport top bottom
    h.sigmaEquiv_commutes

section EquivalenceTransport

variable
  (eG₁ : G₁' ≃* G₁) (eG₂ : G₂' ≃* G₂)
  (eN₁ : N₁' ≃* N₁) (eN₂ : N₂' ≃* N₂)
variable
  (hcomm₁ :
    eG₁.toMonoidHom.comp N₁'.subtype =
      N₁.subtype.comp eN₁.toMonoidHom)
  (hcomm₂ :
    eG₂.toMonoidHom.comp N₂'.subtype =
      N₂.subtype.comp eN₂.toMonoidHom)

/-- Naturality specialized to vertical pullback along commuting
equivalences of ambient groups and normal subgroups. -/
theorem assemble_naturality_under_comap
    (top : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (bottom : ActivePPrimeOrbitwiseCorrespondence N₁' N₂' p)
    (h : NaturalitySquare
      (activePPrimeOrbitwiseComapCorrespondence
        N₁ N₁' p eG₁ eN₁ hcomm₁)
      (activePPrimeOrbitwiseComapCorrespondence
        N₂ N₂' p eG₂ eN₂ hcomm₂)
      top bottom) :
    (IrreducibleCharacter.pPrimeComapEquiv p eG₁).trans
        bottom.assemble =
      top.assemble.trans
        (IrreducibleCharacter.pPrimeComapEquiv p eG₂) := by
  rw [← activePPrimeOrbitwiseComapCorrespondence_assemble
    N₁ N₁' p eG₁ eN₁ hcomm₁]
  rw [← activePPrimeOrbitwiseComapCorrespondence_assemble
    N₂ N₂' p eG₂ eN₂ hcomm₂]
  exact h.assemble_commutes

end EquivalenceTransport

end ActivePPrimeOrbitwiseCorrespondence
end CliffordPartition
end McKayConjecture
