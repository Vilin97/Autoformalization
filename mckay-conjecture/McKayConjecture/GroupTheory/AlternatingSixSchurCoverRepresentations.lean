/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverPresentation
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverRepresentationData

/-!
# Finite representations of the `A₆` Schur-cover presentation

Two corrected ATLAS representations give permutation actions on `F₉²`
and `F₄³`.  This file checks every defining relation of
`AlternatingSixSchurPresentedGroup` and descends the generator assignments
to homomorphisms from the presented group.

The first action detects an element of order two at `k₀`; the second detects
an element of order three.  These two facts provide the lower bound needed
to certify that `k₀` has order six in the abstract presentation.
-/

noncomputable section

open scoped commutatorElement

namespace McKayConjecture
namespace GroupTheory

/-- The six generator values in the double-cover permutation action. -/
def alternatingSixDoubleCoverGenerator :
    Fin 6 → Equiv.Perm AlternatingSixDoubleCoverSpace
  | 0 => alternatingSixDoubleCoverPermutationA
  | 1 => alternatingSixDoubleCoverPermutationB
  | 2 => alternatingSixDoubleCoverPermutationA ^ 2
  | 3 => alternatingSixDoubleCoverPermutationB ^ 4
  | 4 =>
      (alternatingSixDoubleCoverPermutationA *
        alternatingSixDoubleCoverPermutationB) ^ 5
  | 5 =>
      (alternatingSixDoubleCoverPermutationA *
        alternatingSixDoubleCoverPermutationB ^ 2) ^ 5

/-- All four central generator values in the double-cover action coincide. -/
theorem alternatingSixDoubleCoverGenerator_k_eq
    (i : Fin 4) :
    alternatingSixDoubleCoverGenerator
        ⟨i.val + 2, by omega⟩ =
      alternatingSixDoubleCoverGenerator 2 := by
  fin_cases i <;>
    apply Equiv.ext <;>
    intro x <;>
    fin_cases x <;>
    decide

/-- The common central value in the double-cover action has square one. -/
theorem alternatingSixDoubleCoverGenerator_k0_sq :
    alternatingSixDoubleCoverGenerator 2 ^ 2 = 1 := by
  decide

/-- The common central value commutes with every assigned generator. -/
theorem alternatingSixDoubleCoverGenerator_k0_commute
    (j : Fin 6) :
    Commute (alternatingSixDoubleCoverGenerator 2)
      (alternatingSixDoubleCoverGenerator j) := by
  fin_cases j
  · apply Equiv.ext
    intro x
    fin_cases x <;> decide
  · apply Equiv.ext
    intro x
    fin_cases x <;> decide
  · exact Commute.refl _
  · change Commute (alternatingSixDoubleCoverGenerator 2)
      (alternatingSixDoubleCoverGenerator 3)
    rw [show alternatingSixDoubleCoverGenerator 3 =
        alternatingSixDoubleCoverGenerator 2 by
          simpa using alternatingSixDoubleCoverGenerator_k_eq 1]
  · change Commute (alternatingSixDoubleCoverGenerator 2)
      (alternatingSixDoubleCoverGenerator 4)
    rw [show alternatingSixDoubleCoverGenerator 4 =
        alternatingSixDoubleCoverGenerator 2 by
          simpa using alternatingSixDoubleCoverGenerator_k_eq 2]
  · change Commute (alternatingSixDoubleCoverGenerator 2)
      (alternatingSixDoubleCoverGenerator 5)
    rw [show alternatingSixDoubleCoverGenerator 5 =
        alternatingSixDoubleCoverGenerator 2 by
          simpa using alternatingSixDoubleCoverGenerator_k_eq 3]

/-- Every assigned central generator commutes with every assigned
generator. -/
theorem alternatingSixDoubleCoverGenerator_k_commute
    (i : Fin 4) (j : Fin 6) :
    Commute
      (alternatingSixDoubleCoverGenerator
        ⟨i.val + 2, by omega⟩)
      (alternatingSixDoubleCoverGenerator j) := by
  rw [alternatingSixDoubleCoverGenerator_k_eq]
  exact alternatingSixDoubleCoverGenerator_k0_commute j

/-- The first relation-module row holds in the double-cover action. -/
theorem alternatingSixDoubleCoverGenerator_lattice_one :
    alternatingSixDoubleCoverGenerator 2 ^ 3 *
        alternatingSixDoubleCoverGenerator 4 ^ (-2 : ℤ) *
      alternatingSixDoubleCoverGenerator 5 = 1 := by
  rw [show alternatingSixDoubleCoverGenerator 4 =
      alternatingSixDoubleCoverGenerator 2 by
        simpa using alternatingSixDoubleCoverGenerator_k_eq 2,
    show alternatingSixDoubleCoverGenerator 5 =
      alternatingSixDoubleCoverGenerator 2 by
        simpa using alternatingSixDoubleCoverGenerator_k_eq 3]
  calc
    alternatingSixDoubleCoverGenerator 2 ^ 3 *
          alternatingSixDoubleCoverGenerator 2 ^ (-2 : ℤ) *
        alternatingSixDoubleCoverGenerator 2 =
        alternatingSixDoubleCoverGenerator 2 ^ 2 := by group
    _ = 1 := alternatingSixDoubleCoverGenerator_k0_sq

/-- The second relation-module row holds in the double-cover action. -/
theorem alternatingSixDoubleCoverGenerator_lattice_two :
    alternatingSixDoubleCoverGenerator 3 ^ 4 *
        alternatingSixDoubleCoverGenerator 4 ^ 3 *
      alternatingSixDoubleCoverGenerator 5 ^ (-3 : ℤ) = 1 := by
  rw [show alternatingSixDoubleCoverGenerator 3 =
      alternatingSixDoubleCoverGenerator 2 by
        simpa using alternatingSixDoubleCoverGenerator_k_eq 1,
    show alternatingSixDoubleCoverGenerator 4 =
      alternatingSixDoubleCoverGenerator 2 by
        simpa using alternatingSixDoubleCoverGenerator_k_eq 2,
    show alternatingSixDoubleCoverGenerator 5 =
      alternatingSixDoubleCoverGenerator 2 by
        simpa using alternatingSixDoubleCoverGenerator_k_eq 3]
  calc
    alternatingSixDoubleCoverGenerator 2 ^ 4 *
          alternatingSixDoubleCoverGenerator 2 ^ 3 *
        alternatingSixDoubleCoverGenerator 2 ^ (-3 : ℤ) =
        (alternatingSixDoubleCoverGenerator 2 ^ 2) ^ 2 := by group
    _ = 1 := by rw [alternatingSixDoubleCoverGenerator_k0_sq, one_pow]

/-- The double-cover generator assignment satisfies all presentation
relators. -/
theorem alternatingSixDoubleCoverGenerator_kills_relators :
    ∀ r ∈ alternatingSixSchurRelators,
      FreeGroup.lift alternatingSixDoubleCoverGenerator r = 1 := by
  intro r hr
  rcases hr with hr | hr
  · rcases hr with ⟨i, rfl⟩ | ⟨ij, rfl⟩
    · fin_cases i <;>
        simp [alternatingSixSchurDefinitionRelator,
          alternatingSixSchurBaseRelator,
          alternatingSixSchurFreeA,
          alternatingSixSchurFreeB,
          alternatingSixSchurFreeK,
          alternatingSixSchurGenerator,
          alternatingSixDoubleCoverGenerator]
    · rcases ij with ⟨i, j⟩
      simp [alternatingSixSchurCentralityRelator,
        alternatingSixSchurFreeK,
        alternatingSixSchurGenerator,
        map_commutatorElement]
      exact
        commutatorElement_eq_one_iff_commute.mpr
          (alternatingSixDoubleCoverGenerator_k_commute i j)
  · rcases hr with rfl | hr
    · simpa [alternatingSixSchurLatticeRelatorOne,
        alternatingSixSchurFreeK,
        alternatingSixSchurGenerator,
        alternatingSixDoubleCoverGenerator] using
          alternatingSixDoubleCoverGenerator_lattice_one
    · have hr' :
          r = alternatingSixSchurLatticeRelatorTwo := by
        simpa using hr
      subst r
      simpa [alternatingSixSchurLatticeRelatorTwo,
        alternatingSixSchurFreeK,
        alternatingSixSchurGenerator,
        alternatingSixDoubleCoverGenerator] using
          alternatingSixDoubleCoverGenerator_lattice_two

/-- The double-cover permutation representation of the presented group. -/
def alternatingSixDoubleCoverRepresentation :
    AlternatingSixSchurPresentedGroup →*
      Equiv.Perm AlternatingSixDoubleCoverSpace :=
  PresentedGroup.toGroup
    alternatingSixDoubleCoverGenerator_kills_relators

@[simp]
theorem alternatingSixDoubleCoverRepresentation_generator
    (i : Fin 6) :
    alternatingSixDoubleCoverRepresentation
        (alternatingSixSchurPresentedGenerator i) =
      alternatingSixDoubleCoverGenerator i := by
  simp [alternatingSixDoubleCoverRepresentation,
    alternatingSixSchurPresentedGenerator]

@[simp]
theorem alternatingSixDoubleCoverRepresentation_k
    (i : Fin 4) :
    alternatingSixDoubleCoverRepresentation
        (alternatingSixSchurPresentedK i) =
      alternatingSixDoubleCoverGenerator
        ⟨i.val + 2, by omega⟩ := by
  simp [alternatingSixSchurPresentedK]

/-- The image of `k₀` in the double-cover action has exact order two. -/
theorem alternatingSixDoubleCoverRepresentation_k0_order :
    orderOf
        (alternatingSixDoubleCoverRepresentation
          (alternatingSixSchurPresentedK 0)) = 2 := by
  rw [alternatingSixDoubleCoverRepresentation_k]
  apply orderOf_eq_prime
  · decide
  · decide

/-- The six generator values in the triple-cover permutation action. -/
def alternatingSixTripleCoverGenerator :
    Fin 6 → Equiv.Perm AlternatingSixTripleCoverSpace
  | 0 => alternatingSixTripleCoverPermutationA
  | 1 => alternatingSixTripleCoverPermutationB
  | 2 => alternatingSixTripleCoverPermutationA ^ 2
  | 3 => alternatingSixTripleCoverPermutationB ^ 4
  | 4 =>
      (alternatingSixTripleCoverPermutationA *
        alternatingSixTripleCoverPermutationB) ^ 5
  | 5 =>
      (alternatingSixTripleCoverPermutationA *
        alternatingSixTripleCoverPermutationB ^ 2) ^ 5

/-- Exponents of the four central values in terms of the triple-cover
image of `k₀`. -/
def alternatingSixTripleCoverKExponent : Fin 4 → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 1

/-- Every central generator value in the triple-cover action is a power
of the value at `k₀`. -/
theorem alternatingSixTripleCoverGenerator_k_eq
    (i : Fin 4) :
    alternatingSixTripleCoverGenerator
        ⟨i.val + 2, by omega⟩ =
      alternatingSixTripleCoverGenerator 2 ^
        alternatingSixTripleCoverKExponent i := by
  fin_cases i <;>
    apply Equiv.ext <;>
    intro x <;>
    fin_cases x <;>
    decide

/-- The value at `k₀` in the triple-cover action has cube one. -/
theorem alternatingSixTripleCoverGenerator_k0_cube :
    alternatingSixTripleCoverGenerator 2 ^ 3 = 1 := by
  decide

/-- The value at `k₀` commutes with every assigned generator. -/
theorem alternatingSixTripleCoverGenerator_k0_commute
    (j : Fin 6) :
    Commute (alternatingSixTripleCoverGenerator 2)
      (alternatingSixTripleCoverGenerator j) := by
  fin_cases j
  · apply Equiv.ext
    intro x
    fin_cases x <;> decide
  · apply Equiv.ext
    intro x
    fin_cases x <;> decide
  · exact Commute.refl _
  · change Commute (alternatingSixTripleCoverGenerator 2)
      (alternatingSixTripleCoverGenerator 3)
    rw [show alternatingSixTripleCoverGenerator 3 = 1 by
        simpa [alternatingSixTripleCoverKExponent] using
          alternatingSixTripleCoverGenerator_k_eq 1]
    exact Commute.one_right _
  · change Commute (alternatingSixTripleCoverGenerator 2)
      (alternatingSixTripleCoverGenerator 4)
    rw [show alternatingSixTripleCoverGenerator 4 =
        alternatingSixTripleCoverGenerator 2 ^ 2 by
          simpa [alternatingSixTripleCoverKExponent] using
            alternatingSixTripleCoverGenerator_k_eq 2]
    exact (Commute.refl _).pow_right 2
  · change Commute (alternatingSixTripleCoverGenerator 2)
      (alternatingSixTripleCoverGenerator 5)
    rw [show alternatingSixTripleCoverGenerator 5 =
        alternatingSixTripleCoverGenerator 2 by
          simpa [alternatingSixTripleCoverKExponent] using
            alternatingSixTripleCoverGenerator_k_eq 3]

/-- Every assigned central generator commutes with every assigned
generator. -/
theorem alternatingSixTripleCoverGenerator_k_commute
    (i : Fin 4) (j : Fin 6) :
    Commute
      (alternatingSixTripleCoverGenerator
        ⟨i.val + 2, by omega⟩)
      (alternatingSixTripleCoverGenerator j) := by
  rw [alternatingSixTripleCoverGenerator_k_eq]
  exact
    (alternatingSixTripleCoverGenerator_k0_commute j).pow_left _

/-- The first relation-module row holds in the triple-cover action. -/
theorem alternatingSixTripleCoverGenerator_lattice_one :
    alternatingSixTripleCoverGenerator 2 ^ 3 *
        alternatingSixTripleCoverGenerator 4 ^ (-2 : ℤ) *
      alternatingSixTripleCoverGenerator 5 = 1 := by
  rw [show alternatingSixTripleCoverGenerator 4 =
      alternatingSixTripleCoverGenerator 2 ^ 2 by
        simpa [alternatingSixTripleCoverKExponent] using
          alternatingSixTripleCoverGenerator_k_eq 2,
    show alternatingSixTripleCoverGenerator 5 =
      alternatingSixTripleCoverGenerator 2 by
        simpa [alternatingSixTripleCoverKExponent] using
          alternatingSixTripleCoverGenerator_k_eq 3]
  group

/-- The second relation-module row holds in the triple-cover action. -/
theorem alternatingSixTripleCoverGenerator_lattice_two :
    alternatingSixTripleCoverGenerator 3 ^ 4 *
        alternatingSixTripleCoverGenerator 4 ^ 3 *
      alternatingSixTripleCoverGenerator 5 ^ (-3 : ℤ) = 1 := by
  rw [show alternatingSixTripleCoverGenerator 3 = 1 by
        simpa [alternatingSixTripleCoverKExponent] using
          alternatingSixTripleCoverGenerator_k_eq 1,
    show alternatingSixTripleCoverGenerator 4 =
      alternatingSixTripleCoverGenerator 2 ^ 2 by
        simpa [alternatingSixTripleCoverKExponent] using
          alternatingSixTripleCoverGenerator_k_eq 2,
    show alternatingSixTripleCoverGenerator 5 =
      alternatingSixTripleCoverGenerator 2 by
        simpa [alternatingSixTripleCoverKExponent] using
          alternatingSixTripleCoverGenerator_k_eq 3]
  calc
    1 ^ 4 * (alternatingSixTripleCoverGenerator 2 ^ 2) ^ 3 *
          alternatingSixTripleCoverGenerator 2 ^ (-3 : ℤ) =
        alternatingSixTripleCoverGenerator 2 ^ 3 := by group
    _ = 1 := alternatingSixTripleCoverGenerator_k0_cube

/-- The triple-cover generator assignment satisfies all presentation
relators. -/
theorem alternatingSixTripleCoverGenerator_kills_relators :
    ∀ r ∈ alternatingSixSchurRelators,
      FreeGroup.lift alternatingSixTripleCoverGenerator r = 1 := by
  intro r hr
  rcases hr with hr | hr
  · rcases hr with ⟨i, rfl⟩ | ⟨ij, rfl⟩
    · fin_cases i <;>
        simp [alternatingSixSchurDefinitionRelator,
          alternatingSixSchurBaseRelator,
          alternatingSixSchurFreeA,
          alternatingSixSchurFreeB,
          alternatingSixSchurFreeK,
          alternatingSixSchurGenerator,
          alternatingSixTripleCoverGenerator]
    · rcases ij with ⟨i, j⟩
      simp [alternatingSixSchurCentralityRelator,
        alternatingSixSchurFreeK,
        alternatingSixSchurGenerator,
        map_commutatorElement]
      exact
        commutatorElement_eq_one_iff_commute.mpr
          (alternatingSixTripleCoverGenerator_k_commute i j)
  · rcases hr with rfl | hr
    · simpa [alternatingSixSchurLatticeRelatorOne,
        alternatingSixSchurFreeK,
        alternatingSixSchurGenerator,
        alternatingSixTripleCoverGenerator] using
          alternatingSixTripleCoverGenerator_lattice_one
    · have hr' :
          r = alternatingSixSchurLatticeRelatorTwo := by
        simpa using hr
      subst r
      simpa [alternatingSixSchurLatticeRelatorTwo,
        alternatingSixSchurFreeK,
        alternatingSixSchurGenerator,
        alternatingSixTripleCoverGenerator] using
          alternatingSixTripleCoverGenerator_lattice_two

/-- The triple-cover permutation representation of the presented group. -/
def alternatingSixTripleCoverRepresentation :
    AlternatingSixSchurPresentedGroup →*
      Equiv.Perm AlternatingSixTripleCoverSpace :=
  PresentedGroup.toGroup
    alternatingSixTripleCoverGenerator_kills_relators

@[simp]
theorem alternatingSixTripleCoverRepresentation_generator
    (i : Fin 6) :
    alternatingSixTripleCoverRepresentation
        (alternatingSixSchurPresentedGenerator i) =
      alternatingSixTripleCoverGenerator i := by
  simp [alternatingSixTripleCoverRepresentation,
    alternatingSixSchurPresentedGenerator]

@[simp]
theorem alternatingSixTripleCoverRepresentation_k
    (i : Fin 4) :
    alternatingSixTripleCoverRepresentation
        (alternatingSixSchurPresentedK i) =
      alternatingSixTripleCoverGenerator
        ⟨i.val + 2, by omega⟩ := by
  simp [alternatingSixSchurPresentedK]

/-- The image of `k₀` in the triple-cover action has exact order three. -/
theorem alternatingSixTripleCoverRepresentation_k0_order :
    orderOf
        (alternatingSixTripleCoverRepresentation
          (alternatingSixSchurPresentedK 0)) = 3 := by
  rw [alternatingSixTripleCoverRepresentation_k]
  apply orderOf_eq_prime
  · decide
  · decide

end GroupTheory
end McKayConjecture
