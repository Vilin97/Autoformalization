/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordBijection
import McKayConjecture.Character.CliffordPPrime

/-!
# Prime-to-`p` Clifford correspondence

The Clifford correspondence multiplies degrees by the index of the
inertia group.  This file first restricts the correspondence using the
exact, assumption-free degree predicate
`¬ p ∣ [G : I_G(θ)] * ψ.degree`.  For prime `p`, when the inertia index is
prime to `p`, this becomes an equivalence between the usual prime-to-`p`
characters on both sides.
-/

noncomputable section

namespace McKayConjecture

namespace CliffordCorrespondence

variable {G : Type} [Group G] [Fintype G]
variable (N : Subgroup G) [N.Normal]
variable (θ : IrreducibleCharacter N)

/-- Prime-to-`p` irreducible inertia-group characters lying over `θ`. -/
abbrev PPrimeIrreducibleCharactersOverInertia (p : ℕ) :=
  PPrimeIrreducibleCharactersOverAlong
    (inertiaInclusion N θ) θ p

/-- Prime-to-`p` irreducible ambient characters lying over the conjugacy
orbit of `θ`. -/
def PPrimeIrreducibleCharactersOverOrbit (p : ℕ) :=
  {χ : IrreducibleCharactersOverOrbit N θ //
    χ.1.IsPPrimeDegree p}

/-- The exact source of prime-to-`p` Clifford induction.  No primality
hypothesis on `p` is needed for this definition: the predicate records the
full index-times-degree formula. -/
def PPrimeInductionSourcesOverInertia (p : ℕ) :=
  {ψ : IrreducibleCharactersOverInertia N θ //
    ¬p ∣ (IrreducibleCharacter.inertia N θ).index * ψ.1.degree}

end CliffordCorrespondence

namespace CliffordEquivalence

open CliffordCorrespondence

variable {G : Type} [Group G] [Fintype G]
variable (N : Subgroup G) [N.Normal]
variable (θ : IrreducibleCharacter N)

/-- The prime-to-`p` predicate on a Clifford induction is exactly
nondivisibility of the inertia-index-times-source-degree product. -/
theorem induceOverInertiaOrbit_isPPrimeDegree_iff_index_mul_degree
    (p : ℕ) (ψ : IrreducibleCharactersOverInertia N θ) :
    (induceOverInertiaOrbit N θ ψ).1.IsPPrimeDegree p ↔
      ¬p ∣ (IrreducibleCharacter.inertia N θ).index * ψ.1.degree := by
  rw [IrreducibleCharacter.IsPPrimeDegree]
  rfl

/-- Clifford correspondence restricted by its exact degree formula.  This
version is valid for every natural number `p`, without a primality or index
hypothesis. -/
def cliffordCorrespondenceDegreeEquiv (p : ℕ) :
    PPrimeInductionSourcesOverInertia N θ p ≃
      PPrimeIrreducibleCharactersOverOrbit N θ p :=
  (cliffordCorrespondenceEquiv N θ).subtypeEquiv fun ψ ↦
    (induceOverInertiaOrbit_isPPrimeDegree_iff_index_mul_degree
      N θ p ψ).symm

/-- For prime `p`, prime-to-`p` degree of a Clifford induction is
equivalent to prime-to-`p` degree of its source, provided the inertia index
is prime to `p`. -/
theorem induceOverInertiaOrbit_isPPrimeDegree_iff_of_index
    {p : ℕ} (hp : p.Prime)
    (hindex : ¬p ∣ (IrreducibleCharacter.inertia N θ).index)
    (ψ : IrreducibleCharactersOverInertia N θ) :
    (induceOverInertiaOrbit N θ ψ).1.IsPPrimeDegree p ↔
      ψ.1.IsPPrimeDegree p := by
  simpa [induceOverInertiaOrbit, induceSimpleOverInertiaOrbit,
    induceSimpleOverInertia] using
    (CliffordCorrespondence.inducedIrreducibleCharacter_isPPrimeDegree_iff_of_index
        N θ hp hindex ψ.1
        (inertiaInduction_simple N θ ψ.1 ψ.2))

/-- The usual prime-to-`p` Clifford correspondence when the inertia index
is prime to `p`. -/
def cliffordPPrimeCorrespondence
    {p : ℕ} (hp : p.Prime)
    (hindex : ¬p ∣ (IrreducibleCharacter.inertia N θ).index) :
    PPrimeIrreducibleCharactersOverInertia N θ p ≃
      PPrimeIrreducibleCharactersOverOrbit N θ p :=
  (cliffordCorrespondenceEquiv N θ).subtypeEquiv fun ψ ↦
    (induceOverInertiaOrbit_isPPrimeDegree_iff_of_index
      N θ hp hindex ψ).symm

end CliffordEquivalence
end McKayConjecture
