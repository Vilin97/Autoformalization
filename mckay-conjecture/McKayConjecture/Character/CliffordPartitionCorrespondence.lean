/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.Hom
import McKayConjecture.Character.CliffordPartition

/-!
# Assembling correspondences from Clifford orbit blocks

For normal subgroups `N₁ ⫳ G₁` and `N₂ ⫳ G₂`, prime-to-`p`
irreducible characters of the two ambient groups decompose as dependent
sums of Clifford orbit blocks.  Consequently, the following two inputs
assemble into a full character correspondence:

1. an equivalence between the two orbit spaces; and
2. for every source orbit, an equivalence between its prime-to-`p` block
   and the block indexed by the corresponding target orbit.

This file packages those inputs, constructs the total equivalence with
`Equiv.sigmaCongr`, and proves its functorial and transport laws.  No
choice of orbit representatives beyond the one already encapsulated in
`CliffordPartition` is exposed.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordPartition

variable {G₁ G₂ G₃ : Type}
variable [Group G₁] [Group G₂] [Group G₃]
variable [Fintype G₁] [Fintype G₂] [Fintype G₃]
variable (N₁ : Subgroup G₁) (N₂ : Subgroup G₂) (N₃ : Subgroup G₃)
variable [N₁.Normal] [N₂.Normal] [N₃.Normal]

/-- Orbitwise data sufficient to construct a bijection between all
prime-to-`p` irreducible characters of two ambient groups. -/
structure PPrimeOrbitwiseCorrespondence (p : ℕ) where
  /-- The matching of Clifford-orbit indices. -/
  orbitEquiv : OrbitSpace N₁ ≃ OrbitSpace N₂
  /-- The matching of prime-to-`p` characters in every corresponding
  pair of Clifford blocks. -/
  blockEquiv :
    ∀ q : OrbitSpace N₁,
      PPrimeOrbitBlock N₁ p q ≃
        PPrimeOrbitBlock N₂ p (orbitEquiv q)

namespace PPrimeOrbitwiseCorrespondence

variable {N₁ N₂ N₃} {p : ℕ}

/-- The equivalence of dependent sums obtained from the orbit equivalence
and the family of block equivalences. -/
def sigmaEquiv
    (d : PPrimeOrbitwiseCorrespondence N₁ N₂ p) :
    (Σ q : OrbitSpace N₁, PPrimeOrbitBlock N₁ p q) ≃
      Σ q : OrbitSpace N₂, PPrimeOrbitBlock N₂ p q :=
  Equiv.sigmaCongr d.orbitEquiv d.blockEquiv

omit [Fintype G₁] [Fintype G₂] in
@[simp]
theorem sigmaEquiv_mk
    (d : PPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (q : OrbitSpace N₁) (χ : PPrimeOrbitBlock N₁ p q) :
    d.sigmaEquiv ⟨q, χ⟩ =
      ⟨d.orbitEquiv q, d.blockEquiv q χ⟩ :=
  rfl

/-- Assemble the orbitwise data into a full equivalence of prime-to-`p`
irreducible characters. -/
def assemble
    (d : PPrimeOrbitwiseCorrespondence N₁ N₂ p) :
    PPrimeIrreducibleCharacter G₁ p ≃
      PPrimeIrreducibleCharacter G₂ p :=
  (pPrimeOrbitBlockSigmaEquiv N₁ p).trans
    (d.sigmaEquiv.trans
      (pPrimeOrbitBlockSigmaEquiv N₂ p).symm)

/-- The assembled map, written explicitly in Clifford-block coordinates. -/
theorem assemble_apply
    (d : PPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    d.assemble χ =
      (pPrimeOrbitBlockSigmaEquiv N₂ p).symm
        (d.sigmaEquiv
          (pPrimeOrbitBlockSigmaEquiv N₁ p χ)) :=
  rfl

/-- The inverse assembled map, written explicitly in Clifford-block
coordinates. -/
theorem assemble_symm_apply
    (d : PPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (ψ : PPrimeIrreducibleCharacter G₂ p) :
    d.assemble.symm ψ =
      (pPrimeOrbitBlockSigmaEquiv N₁ p).symm
        (d.sigmaEquiv.symm
          (pPrimeOrbitBlockSigmaEquiv N₂ p ψ)) :=
  rfl

/-- Applying the target Clifford decomposition after assembly is exactly
transport by the orbitwise sigma equivalence. -/
@[simp]
theorem decompose_assemble
    (d : PPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    pPrimeOrbitBlockSigmaEquiv N₂ p (d.assemble χ) =
      d.sigmaEquiv (pPrimeOrbitBlockSigmaEquiv N₁ p χ) := by
  rw [assemble_apply, Equiv.apply_symm_apply]

/-- Inverse assembly satisfies the inverse Clifford-coordinate transport
law. -/
@[simp]
theorem decompose_assemble_symm
    (d : PPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (ψ : PPrimeIrreducibleCharacter G₂ p) :
    pPrimeOrbitBlockSigmaEquiv N₁ p (d.assemble.symm ψ) =
      d.sigmaEquiv.symm
        (pPrimeOrbitBlockSigmaEquiv N₂ p ψ) := by
  rw [assemble_symm_apply, Equiv.apply_symm_apply]

/-- The assembled correspondence sends the Clifford orbit of a character
to the orbit prescribed by `orbitEquiv`. -/
@[simp]
theorem orbitOf_assemble
    (d : PPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    orbitOf N₂ (d.assemble χ).1 =
      d.orbitEquiv (orbitOf N₁ χ.1) := by
  have h := congrArg Sigma.fst (d.decompose_assemble χ)
  exact h

/-- The inverse correspondence transports Clifford orbits by the inverse
orbit equivalence. -/
@[simp]
theorem orbitOf_assemble_symm
    (d : PPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (ψ : PPrimeIrreducibleCharacter G₂ p) :
    orbitOf N₁ (d.assemble.symm ψ).1 =
      d.orbitEquiv.symm (orbitOf N₂ ψ.1) := by
  have h := congrArg Sigma.fst (d.decompose_assemble_symm ψ)
  exact h

/-! ## Identity and composition -/

/-- The identity orbitwise correspondence. -/
def refl (N : Subgroup G₁) [N.Normal] (p : ℕ) :
    PPrimeOrbitwiseCorrespondence N N p where
  orbitEquiv := Equiv.refl _
  blockEquiv _ := Equiv.refl _

omit [Fintype G₁] in
@[simp]
theorem refl_sigmaEquiv_apply
    (x : Σ q : OrbitSpace N₁, PPrimeOrbitBlock N₁ p q) :
    (refl N₁ p).sigmaEquiv x = x := by
  rcases x with ⟨q, χ⟩
  rfl

@[simp]
theorem refl_assemble_apply
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    (refl N₁ p).assemble χ = χ := by
  apply (pPrimeOrbitBlockSigmaEquiv N₁ p).injective
  rw [decompose_assemble, refl_sigmaEquiv_apply]

/-- Composition of orbit-index and blockwise correspondences. -/
def trans
    (d₁₂ : PPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (d₂₃ : PPrimeOrbitwiseCorrespondence N₂ N₃ p) :
    PPrimeOrbitwiseCorrespondence N₁ N₃ p where
  orbitEquiv := d₁₂.orbitEquiv.trans d₂₃.orbitEquiv
  blockEquiv q :=
    (d₁₂.blockEquiv q).trans
      (d₂₃.blockEquiv (d₁₂.orbitEquiv q))

omit [Fintype G₁] [Fintype G₂] [Fintype G₃] in
@[simp]
theorem trans_sigmaEquiv_apply
    (d₁₂ : PPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (d₂₃ : PPrimeOrbitwiseCorrespondence N₂ N₃ p)
    (x : Σ q : OrbitSpace N₁, PPrimeOrbitBlock N₁ p q) :
    (d₁₂.trans d₂₃).sigmaEquiv x =
      d₂₃.sigmaEquiv (d₁₂.sigmaEquiv x) := by
  rcases x with ⟨q, χ⟩
  rfl

@[simp]
theorem trans_assemble_apply
    (d₁₂ : PPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (d₂₃ : PPrimeOrbitwiseCorrespondence N₂ N₃ p)
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    (d₁₂.trans d₂₃).assemble χ =
      d₂₃.assemble (d₁₂.assemble χ) := by
  apply (pPrimeOrbitBlockSigmaEquiv N₃ p).injective
  rw [decompose_assemble, trans_sigmaEquiv_apply,
    decompose_assemble, decompose_assemble]

/-- Assembly preserves identity equivalences. -/
theorem assemble_refl :
    (refl N₁ p).assemble =
      Equiv.refl (PPrimeIrreducibleCharacter G₁ p) :=
  Equiv.ext refl_assemble_apply

/-- Assembly preserves composition of orbitwise correspondences. -/
theorem assemble_trans
    (d₁₂ : PPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (d₂₃ : PPrimeOrbitwiseCorrespondence N₂ N₃ p) :
    (d₁₂.trans d₂₃).assemble =
      d₁₂.assemble.trans d₂₃.assemble :=
  Equiv.ext (d₁₂.trans_assemble_apply d₂₃)

/-! ## Same-ambient specialization -/

/-- Orbitwise correspondence data for two normal subgroups of the same
ambient group. -/
abbrev SameAmbientPPrimeOrbitwiseCorrespondence
    (N M : Subgroup G₁) [N.Normal] [M.Normal] (p : ℕ) :=
  PPrimeOrbitwiseCorrespondence N M p

/-- In the same-ambient case, assembly is a permutation of the one ambient
prime-to-`p` character set. -/
def assembleSameAmbient
    {N M : Subgroup G₁} [N.Normal] [M.Normal]
    (d : SameAmbientPPrimeOrbitwiseCorrespondence N M p) :
    Equiv.Perm (PPrimeIrreducibleCharacter G₁ p) :=
  d.assemble

@[simp]
theorem assembleSameAmbient_apply
    {N M : Subgroup G₁} [N.Normal] [M.Normal]
    (d : SameAmbientPPrimeOrbitwiseCorrespondence N M p)
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    d.assembleSameAmbient χ = d.assemble χ :=
  rfl

/-- Orbitwise permutations for a fixed normal subgroup of one ambient
group. -/
abbrev PPrimeOrbitwisePermutation
    (N : Subgroup G₁) [N.Normal] (p : ℕ) :=
  PPrimeOrbitwiseCorrespondence N N p

/-- A same-ambient orbitwise correspondence gives a permutation of the
ambient prime-to-`p` characters. -/
def toPermutation
    (d : PPrimeOrbitwisePermutation N₁ p) :
    Equiv.Perm (PPrimeIrreducibleCharacter G₁ p) :=
  d.assemble

@[simp]
theorem toPermutation_apply
    (d : PPrimeOrbitwisePermutation N₁ p)
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    d.toPermutation χ = d.assemble χ :=
  rfl

/-! ## Equivariance in Clifford coordinates -/

section Equivariance

variable {A : Type} [Group A]
variable [MulAction A (PPrimeIrreducibleCharacter G₁ p)]
variable [MulAction A (PPrimeIrreducibleCharacter G₂ p)]

/-- Equivariance expressed entirely after transporting both ambient
actions through the Clifford sigma decompositions.

This is often the convenient proof criterion: its two sides can be checked
by the action on orbit indices and by the action inside the corresponding
blocks. -/
def SigmaEquivariant
    (d : PPrimeOrbitwiseCorrespondence N₁ N₂ p) : Prop :=
  ∀ (a : A)
    (x : Σ q : OrbitSpace N₁, PPrimeOrbitBlock N₁ p q),
    d.sigmaEquiv
        (pPrimeOrbitBlockSigmaEquiv N₁ p
          (a • (pPrimeOrbitBlockSigmaEquiv N₁ p).symm x)) =
      pPrimeOrbitBlockSigmaEquiv N₂ p
        (a • (pPrimeOrbitBlockSigmaEquiv N₂ p).symm
          (d.sigmaEquiv x))

/-- The sigma-coordinate criterion is equivalent to ordinary equivariance
of the assembled character correspondence. -/
theorem sigmaEquivariant_iff
    (d : PPrimeOrbitwiseCorrespondence N₁ N₂ p) :
    d.SigmaEquivariant (A := A) ↔
      ∀ (a : A) (χ : PPrimeIrreducibleCharacter G₁ p),
        d.assemble (a • χ) = a • d.assemble χ := by
  constructor
  · intro h a χ
    apply (pPrimeOrbitBlockSigmaEquiv N₂ p).injective
    simpa only [decompose_assemble, assemble_apply,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
      h a (pPrimeOrbitBlockSigmaEquiv N₁ p χ)
  · intro h a x
    obtain ⟨χ, rfl⟩ :=
      (pPrimeOrbitBlockSigmaEquiv N₁ p).surjective x
    simpa only [Equiv.symm_apply_apply, decompose_assemble,
      Equiv.apply_symm_apply, assemble_apply] using
      congrArg (pPrimeOrbitBlockSigmaEquiv N₂ p) (h a χ)

/-- Package a proof of the sigma-coordinate criterion as a bundled
equivariant map.  Its underlying function is the assembled equivalence. -/
def toMulActionHom
    (d : PPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (h : d.SigmaEquivariant (A := A)) :
    PPrimeIrreducibleCharacter G₁ p →[A]
      PPrimeIrreducibleCharacter G₂ p where
  toFun := d.assemble
  map_smul' := d.sigmaEquivariant_iff.mp h

@[simp]
theorem toMulActionHom_apply
    (d : PPrimeOrbitwiseCorrespondence N₁ N₂ p)
    (h : d.SigmaEquivariant (A := A))
    (χ : PPrimeIrreducibleCharacter G₁ p) :
    d.toMulActionHom h χ = d.assemble χ :=
  rfl

end Equivariance

end PPrimeOrbitwiseCorrespondence

end CliffordPartition
end McKayConjecture
