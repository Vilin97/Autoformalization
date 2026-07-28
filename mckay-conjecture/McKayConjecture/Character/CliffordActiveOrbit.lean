/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordPartition
import McKayConjecture.Character.CliffordPPrimeCorrespondence

/-!
# Active prime-to-`p` Clifford orbits

A conjugacy orbit in `Irr(N)` is called active at `p` when some
prime-to-`p` irreducible character of the ambient group lies over it.
For an active orbit, the inertia index is automatically prime to `p`.
Consequently the prime-to-`p` Clifford correspondence applies on every
active orbit, and the global prime-to-`p` character set is a sigma of the
corresponding inertia-group character sets.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordPartition

open CliffordCorrespondence
open CliffordEquivalence

variable {G : Type} [Group G] [Fintype G]
variable (N : Subgroup G) [N.Normal]

/-- A sigma type is unchanged if its index is restricted to the indices
whose fibers are nonempty. -/
def sigmaNonemptyFiberEquiv
    {ι : Type} (F : ι → Type) :
    (Σ i, F i) ≃
      Σ i : {i : ι // Nonempty (F i)}, F i.1 where
  toFun x := ⟨⟨x.1, ⟨x.2⟩⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv := by
    rintro ⟨i, x⟩
    rfl
  right_inv := by
    rintro ⟨⟨i, hi⟩, x⟩
    rfl

/-- An orbit in `Irr(N)` carrying at least one prime-to-`p` ambient
character. -/
abbrev ActiveOrbit (p : ℕ) :=
  {q : OrbitSpace N // Nonempty (PPrimeOrbitBlock N p q)}

/-- Restrict the sigma decomposition of prime-to-`p` characters to its
active orbits. -/
def activeOrbitBlockSigmaEquiv (p : ℕ) :
    PPrimeIrreducibleCharacter G p ≃
      Σ q : ActiveOrbit N p,
        PPrimeOrbitBlock N p q.1 :=
  (pPrimeOrbitBlockSigmaEquiv N p).trans
    (sigmaNonemptyFiberEquiv
      (PPrimeOrbitBlock N p))

/-- A prime-to-`p` character lying over an orbit forces the inertia index
of that orbit to be prime to `p`. -/
theorem not_dvd_inertia_index_of_mem_pPrimeOrbitBlock
    {p : ℕ} (q : OrbitSpace N)
    (χ : PPrimeOrbitBlock N p q) :
    ¬p ∣ (IrreducibleCharacter.inertia N q.out).index := by
  let ψ :
      IrreducibleCharactersOverInertia N q.out :=
    (cliffordCorrespondenceEquiv N q.out).symm χ.1
  have hinduced :
      induceOverInertiaOrbit N q.out ψ = χ.1 :=
    (cliffordCorrespondenceEquiv N q.out).apply_symm_apply χ.1
  have hpInduced :
      (induceOverInertiaOrbit N q.out ψ).1.IsPPrimeDegree p := by
    rw [hinduced]
    exact χ.2
  have hproduct :
      ¬p ∣
        (IrreducibleCharacter.inertia N q.out).index *
          ψ.1.degree :=
    (induceOverInertiaOrbit_isPPrimeDegree_iff_index_mul_degree
      N q.out p ψ).mp hpInduced
  intro hindex
  exact hproduct (dvd_mul_of_dvd_left hindex ψ.1.degree)

/-- Every active orbit has prime-to-`p` inertia index. -/
theorem activeOrbit_inertia_index_isPPrime
    {p : ℕ} (q : ActiveOrbit N p) :
    ¬p ∣ (IrreducibleCharacter.inertia N q.1.out).index :=
  not_dvd_inertia_index_of_mem_pPrimeOrbitBlock
    N q.1 q.2.some

/-- On an active orbit, Clifford correspondence restricts to the usual
prime-to-`p` correspondence. -/
def activeOrbitCliffordEquiv
    {p : ℕ} (hp : p.Prime) (q : ActiveOrbit N p) :
    PPrimeIrreducibleCharactersOverInertia N q.1.out p ≃
      PPrimeOrbitBlock N p q.1 :=
  cliffordPPrimeCorrespondence N q.1.out hp
    (activeOrbit_inertia_index_isPPrime N q)

/-- Global prime-to-`p` Clifford parametrization: an ambient character is
equivalently an active orbit together with a prime-to-`p` irreducible
character of its inertia group lying over the orbit representative. -/
def activeOrbitInertiaSigmaEquiv
    {p : ℕ} (hp : p.Prime) :
    PPrimeIrreducibleCharacter G p ≃
      Σ q : ActiveOrbit N p,
        PPrimeIrreducibleCharactersOverInertia
          N q.1.out p :=
  (activeOrbitBlockSigmaEquiv N p).trans
    (Equiv.sigmaCongrRight fun q ↦
      (activeOrbitCliffordEquiv N hp q).symm)

end CliffordPartition
end McKayConjecture
