/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PPrimeCliffordOrbit

/-!
# Partitioning prime-to-`p` characters by active Clifford orbits

Prime-to-`p` ambient irreducible characters are partitioned exactly by
the active Clifford orbits of a normal subgroup.  Inactive orbits have
empty prime-to-`p` blocks and do not occur as indices.

This file packages the active partition with projection lemmas and
assembles a global prime-to-`p` character correspondence from:

1. an equivalence of active orbit spaces; and
2. an equivalence of the corresponding nonempty prime-to-`p` blocks.

The construction is functorial under identity and composition and
records the exact transport law for active Clifford-orbit indices.

The character and Clifford-partition APIs currently used here are
Type-0, so the ambient groups in this module remain in `Type`.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordPartition

variable {G G₁ G₂ G₃ : Type}
variable [Group G] [Group G₁] [Group G₂] [Group G₃]
variable [Fintype G] [Fintype G₁] [Fintype G₂] [Fintype G₃]
variable (N : Subgroup G)
variable (N₁ : Subgroup G₁) (N₂ : Subgroup G₂)
variable (N₃ : Subgroup G₃)
variable [N.Normal] [N₁.Normal] [N₂.Normal] [N₃.Normal]

/-! ## The exact active partition -/

/-- The exact partition of prime-to-`p` ambient characters by the active
Clifford orbits of `N`. -/
def pPrimeActiveOrbitBlockSigmaEquiv (p : ℕ) :
    PPrimeIrreducibleCharacter G p ≃
      Σ q : ActiveOrbit N p,
        PPrimeOrbitBlock N p q.1 :=
  activeOrbitBlockSigmaEquiv N p

/-- The active-orbit index assigned to a prime-to-`p` ambient
character. -/
def activeOrbitIndex
    {p : ℕ} (χ : PPrimeIrreducibleCharacter G p) :
    ActiveOrbit N p :=
  (pPrimeActiveOrbitBlockSigmaEquiv N p χ).1

@[simp]
theorem activeOrbitIndex_coe
    {p : ℕ} (χ : PPrimeIrreducibleCharacter G p) :
    (activeOrbitIndex N χ).1 =
      orbitOf N χ.1 :=
  rfl

@[simp]
theorem pPrimeActiveOrbitBlockSigmaEquiv_apply_fst
    {p : ℕ} (χ : PPrimeIrreducibleCharacter G p) :
    (pPrimeActiveOrbitBlockSigmaEquiv N p χ).1 =
      activeOrbitIndex N χ :=
  rfl

@[simp]
theorem pPrimeActiveOrbitBlockSigmaEquiv_apply_fst_coe
    {p : ℕ} (χ : PPrimeIrreducibleCharacter G p) :
    (pPrimeActiveOrbitBlockSigmaEquiv N p χ).1.1 =
      orbitOf N χ.1 :=
  rfl

@[simp]
theorem pPrimeActiveOrbitBlockSigmaEquiv_apply_character
    {p : ℕ} (χ : PPrimeIrreducibleCharacter G p) :
    (pPrimeActiveOrbitBlockSigmaEquiv N p χ).2.1.1 =
      χ.1 :=
  rfl

@[simp]
theorem pPrimeActiveOrbitBlockSigmaEquiv_symm_mk
    {p : ℕ} (q : ActiveOrbit N p)
    (χ : PPrimeOrbitBlock N p q.1) :
    (pPrimeActiveOrbitBlockSigmaEquiv N p).symm
        ⟨q, χ⟩ =
      ⟨χ.1.1, χ.2⟩ :=
  rfl

/-- The inverse partition map returns a character in precisely the
Clifford orbit indexing its input block. -/
@[simp]
theorem orbitOf_pPrimeActiveOrbitBlockSigmaEquiv_symm_mk
    {p : ℕ} (q : ActiveOrbit N p)
    (χ : PPrimeOrbitBlock N p q.1) :
    orbitOf N
        ((pPrimeActiveOrbitBlockSigmaEquiv N p).symm
          ⟨q, χ⟩).1 =
      q.1 := by
  simpa only [
    pPrimeActiveOrbitBlockSigmaEquiv_symm_mk] using
      orbitOf_eq_of_mem_orbitBlock N q.1 χ.1

/-! ## Active orbitwise correspondence data -/

/-- Orbitwise data on the exact active partitions.  Unlike an
all-orbit formulation, every indexed block is nonempty by construction. -/
structure ActivePPrimeOrbitwiseCorrespondence (p : ℕ) where
  /-- Matching of active Clifford-orbit indices. -/
  activeOrbitEquiv :
    ActiveOrbit N₁ p ≃ ActiveOrbit N₂ p
  /-- Matching of the prime-to-`p` blocks over corresponding active
  orbits. -/
  blockEquiv :
    ∀ q : ActiveOrbit N₁ p,
      PPrimeOrbitBlock N₁ p q.1 ≃
        PPrimeOrbitBlock N₂ p (activeOrbitEquiv q).1

namespace ActivePPrimeOrbitwiseCorrespondence

variable {N₁ N₂ N₃} {p : ℕ}

/-- The equivalence of active-orbit dependent sums induced by the
orbit-index and blockwise equivalences. -/
def sigmaEquiv
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p) :
    (Σ q : ActiveOrbit N₁ p,
        PPrimeOrbitBlock N₁ p q.1) ≃
      Σ q : ActiveOrbit N₂ p,
        PPrimeOrbitBlock N₂ p q.1 :=
  Equiv.sigmaCongr d.activeOrbitEquiv d.blockEquiv

omit [Fintype G₁] [Fintype G₂] in
@[simp]
theorem sigmaEquiv_mk
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (q : ActiveOrbit N₁ p)
    (χ : PPrimeOrbitBlock N₁ p q.1) :
    d.sigmaEquiv ⟨q, χ⟩ =
      ⟨d.activeOrbitEquiv q, d.blockEquiv q χ⟩ :=
  rfl

/-- Assemble active orbitwise data into a full equivalence of ambient
prime-to-`p` irreducible characters. -/
def assemble
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p) :
    PPrimeIrreducibleCharacter G₁ p ≃
      PPrimeIrreducibleCharacter G₂ p :=
  (pPrimeActiveOrbitBlockSigmaEquiv N₁ p).trans
    (d.sigmaEquiv.trans
      (pPrimeActiveOrbitBlockSigmaEquiv N₂ p).symm)

/-- The assembled forward map in active Clifford coordinates. -/
theorem assemble_apply
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    d.assemble χ =
      (pPrimeActiveOrbitBlockSigmaEquiv N₂ p).symm
        (d.sigmaEquiv
          (pPrimeActiveOrbitBlockSigmaEquiv N₁ p χ)) :=
  rfl

/-- The assembled inverse map in active Clifford coordinates. -/
theorem assemble_symm_apply
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (ψ : PPrimeIrreducibleCharacter G₂ p) :
    d.assemble.symm ψ =
      (pPrimeActiveOrbitBlockSigmaEquiv N₁ p).symm
        (d.sigmaEquiv.symm
          (pPrimeActiveOrbitBlockSigmaEquiv N₂ p ψ)) :=
  rfl

/-- Decomposition after forward assembly is exactly the active sigma
equivalence. -/
@[simp]
theorem decompose_assemble
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    pPrimeActiveOrbitBlockSigmaEquiv N₂ p
        (d.assemble χ) =
      d.sigmaEquiv
        (pPrimeActiveOrbitBlockSigmaEquiv N₁ p χ) := by
  rw [assemble_apply, Equiv.apply_symm_apply]

/-- Decomposition after inverse assembly is the inverse active sigma
equivalence. -/
@[simp]
theorem decompose_assemble_symm
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (ψ : PPrimeIrreducibleCharacter G₂ p) :
    pPrimeActiveOrbitBlockSigmaEquiv N₁ p
        (d.assemble.symm ψ) =
      d.sigmaEquiv.symm
        (pPrimeActiveOrbitBlockSigmaEquiv N₂ p ψ) := by
  rw [assemble_symm_apply, Equiv.apply_symm_apply]

/-- Assembly transports the exact active-orbit index by
`activeOrbitEquiv`. -/
@[simp]
theorem activeOrbitIndex_assemble
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    activeOrbitIndex N₂ (d.assemble χ) =
      d.activeOrbitEquiv (activeOrbitIndex N₁ χ) := by
  exact congrArg Sigma.fst (d.decompose_assemble χ)

/-- Inverse assembly transports the exact active-orbit index by the
inverse orbit equivalence. -/
@[simp]
theorem activeOrbitIndex_assemble_symm
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (ψ : PPrimeIrreducibleCharacter G₂ p) :
    activeOrbitIndex N₁ (d.assemble.symm ψ) =
      d.activeOrbitEquiv.symm
        (activeOrbitIndex N₂ ψ) := by
  exact congrArg Sigma.fst
    (d.decompose_assemble_symm ψ)

/-- Underlying Clifford-orbit transport for the assembled forward
correspondence. -/
@[simp]
theorem orbitOf_assemble
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    orbitOf N₂ (d.assemble χ).1 =
      (d.activeOrbitEquiv
        (activeOrbitIndex N₁ χ)).1 := by
  exact congrArg Subtype.val
    (d.activeOrbitIndex_assemble χ)

/-- Underlying Clifford-orbit transport for the inverse assembled
correspondence. -/
@[simp]
theorem orbitOf_assemble_symm
    (d : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (ψ : PPrimeIrreducibleCharacter G₂ p) :
    orbitOf N₁ (d.assemble.symm ψ).1 =
      (d.activeOrbitEquiv.symm
        (activeOrbitIndex N₂ ψ)).1 := by
  exact congrArg Subtype.val
    (d.activeOrbitIndex_assemble_symm ψ)

/-! ## Identity and composition -/

/-- The identity active orbitwise correspondence. -/
def refl (N : Subgroup G₁) [N.Normal] (p : ℕ) :
    ActivePPrimeOrbitwiseCorrespondence N N p where
  activeOrbitEquiv := Equiv.refl _
  blockEquiv _ := Equiv.refl _

omit [Fintype G₁] in
@[simp]
theorem refl_sigmaEquiv_apply
    (x : Σ q : ActiveOrbit N₁ p,
      PPrimeOrbitBlock N₁ p q.1) :
    (refl N₁ p).sigmaEquiv x = x := by
  rcases x with ⟨q, χ⟩
  rfl

@[simp]
theorem refl_assemble_apply
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    (refl N₁ p).assemble χ = χ := by
  apply (pPrimeActiveOrbitBlockSigmaEquiv N₁ p).injective
  rw [decompose_assemble, refl_sigmaEquiv_apply]

/-- Composition of active orbit-index and blockwise
correspondences. -/
def trans
    (d₁₂ : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (d₂₃ : ActivePPrimeOrbitwiseCorrespondence N₂ N₃ p) :
    ActivePPrimeOrbitwiseCorrespondence N₁ N₃ p where
  activeOrbitEquiv :=
    d₁₂.activeOrbitEquiv.trans d₂₃.activeOrbitEquiv
  blockEquiv q :=
    (d₁₂.blockEquiv q).trans
      (d₂₃.blockEquiv (d₁₂.activeOrbitEquiv q))

omit [Fintype G₁] [Fintype G₂] [Fintype G₃] in
@[simp]
theorem trans_sigmaEquiv_apply
    (d₁₂ : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (d₂₃ : ActivePPrimeOrbitwiseCorrespondence N₂ N₃ p)
    (x : Σ q : ActiveOrbit N₁ p,
      PPrimeOrbitBlock N₁ p q.1) :
    (d₁₂.trans d₂₃).sigmaEquiv x =
      d₂₃.sigmaEquiv (d₁₂.sigmaEquiv x) := by
  rcases x with ⟨q, χ⟩
  rfl

@[simp]
theorem trans_assemble_apply
    (d₁₂ : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (d₂₃ : ActivePPrimeOrbitwiseCorrespondence N₂ N₃ p)
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    (d₁₂.trans d₂₃).assemble χ =
      d₂₃.assemble (d₁₂.assemble χ) := by
  apply (pPrimeActiveOrbitBlockSigmaEquiv N₃ p).injective
  rw [decompose_assemble, trans_sigmaEquiv_apply,
    decompose_assemble, decompose_assemble]

/-- Assembly preserves identity equivalences. -/
theorem assemble_refl :
    (refl N₁ p).assemble =
      Equiv.refl (PPrimeIrreducibleCharacter G₁ p) :=
  Equiv.ext refl_assemble_apply

/-- Assembly preserves composition. -/
theorem assemble_trans
    (d₁₂ : ActivePPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (d₂₃ : ActivePPrimeOrbitwiseCorrespondence N₂ N₃ p) :
    (d₁₂.trans d₂₃).assemble =
      d₁₂.assemble.trans d₂₃.assemble :=
  Equiv.ext (d₁₂.trans_assemble_apply d₂₃)

end ActivePPrimeOrbitwiseCorrespondence

end CliffordPartition
end McKayConjecture
