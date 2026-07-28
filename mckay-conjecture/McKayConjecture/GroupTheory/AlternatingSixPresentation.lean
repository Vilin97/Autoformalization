/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.PresentedGroup
import McKayConjecture.GroupTheory.AlternatingSix

/-!
# A two-generator presentation mapping to `A₆`

This file records the standard ATLAS generators

`a = (0 1)(2 3)` and `b = (0 1 2 4)(3 5)`

and the four relations

`a² = b⁴ = (ab)⁵ = (ab²)⁵ = 1`.

The finite normal-form argument proving that these relations present all of
`A₆` is kept separate from the concrete map constructed here.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- The standard double transposition used as the first generator of `A₆`. -/
def alternatingSixPresentationPermA :
    Equiv.Perm (Fin 6) :=
  ⟨![1, 0, 3, 2, 4, 5], ![1, 0, 3, 2, 4, 5], by decide, by decide⟩

/-- The standard product `(0 1 2 4)(3 5)` used as the second generator. -/
def alternatingSixPresentationPermB :
    Equiv.Perm (Fin 6) :=
  ⟨![1, 2, 4, 5, 0, 3], ![4, 0, 1, 5, 2, 3], by decide, by decide⟩

/-- The first standard generator, regarded as an element of `A₆`. -/
def alternatingSixPresentationA : AlternatingSix :=
  ⟨alternatingSixPresentationPermA, by
    rw [Equiv.Perm.mem_alternatingGroup]
    have h :
        alternatingSixPresentationPermA =
          Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3 := by
      decide
    rw [h, map_mul]
    simp⟩

/-- The second standard generator, regarded as an element of `A₆`. -/
def alternatingSixPresentationB : AlternatingSix :=
  ⟨alternatingSixPresentationPermB, by
    rw [Equiv.Perm.mem_alternatingGroup]
    have h :
        alternatingSixPresentationPermB =
          Equiv.swap (0 : Fin 6) 1 *
            Equiv.swap 1 2 *
              Equiv.swap 2 4 *
                Equiv.swap 3 5 := by
      decide
    rw [h, map_mul, map_mul, map_mul]
    simp⟩

/-- The four standard relations hold for the concrete generators of `A₆`. -/
theorem alternatingSixPresentation_relations :
    alternatingSixPresentationA ^ 2 = 1 ∧
      alternatingSixPresentationB ^ 4 = 1 ∧
      (alternatingSixPresentationA * alternatingSixPresentationB) ^ 5 = 1 ∧
      (alternatingSixPresentationA * alternatingSixPresentationB ^ 2) ^ 5 = 1 := by
  decide

/-- A word in the two abstract generators. -/
def alternatingSixPresentationGenerator (i : Fin 2) :
    FreeGroup (Fin 2) :=
  FreeGroup.of i

/-- The relation `a² = 1`. -/
def alternatingSixPresentationRelatorA :
    FreeGroup (Fin 2) :=
  alternatingSixPresentationGenerator 0 ^ 2

/-- The relation `b⁴ = 1`. -/
def alternatingSixPresentationRelatorB :
    FreeGroup (Fin 2) :=
  alternatingSixPresentationGenerator 1 ^ 4

/-- The relation `(ab)⁵ = 1`. -/
def alternatingSixPresentationRelatorAB :
    FreeGroup (Fin 2) :=
  (alternatingSixPresentationGenerator 0 *
      alternatingSixPresentationGenerator 1) ^ 5

/-- The relation `(ab²)⁵ = 1`. -/
def alternatingSixPresentationRelatorABSq :
    FreeGroup (Fin 2) :=
  (alternatingSixPresentationGenerator 0 *
      alternatingSixPresentationGenerator 1 ^ 2) ^ 5

/-- The four standard relators for `A₆`. -/
def alternatingSixPresentationRelators :
    Set (FreeGroup (Fin 2)) :=
  {alternatingSixPresentationRelatorA,
    alternatingSixPresentationRelatorB,
    alternatingSixPresentationRelatorAB,
    alternatingSixPresentationRelatorABSq}

/-- The group defined by the four standard `A₆` relators. -/
abbrev AlternatingSixPresentedGroup :=
  PresentedGroup alternatingSixPresentationRelators

/-- The presented generator `a`. -/
def alternatingSixPresentedA :
    AlternatingSixPresentedGroup :=
  PresentedGroup.of 0

/-- The presented generator `b`. -/
def alternatingSixPresentedB :
    AlternatingSixPresentedGroup :=
  PresentedGroup.of 1

/-- The concrete generators kill each of the four defining relators. -/
theorem alternatingSixPresentationGenerator_kills_relators :
    ∀ r ∈ alternatingSixPresentationRelators,
      FreeGroup.lift
        (fun i : Fin 2 ↦
          if i = 0 then alternatingSixPresentationA
          else alternatingSixPresentationB) r = 1 := by
  intro r hr
  simp only [alternatingSixPresentationRelators, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa [alternatingSixPresentationRelatorA,
      alternatingSixPresentationGenerator] using
        alternatingSixPresentation_relations.1
  · simpa [alternatingSixPresentationRelatorB,
      alternatingSixPresentationGenerator] using
        alternatingSixPresentation_relations.2.1
  · simpa [alternatingSixPresentationRelatorAB,
      alternatingSixPresentationGenerator] using
        alternatingSixPresentation_relations.2.2.1
  · simpa [alternatingSixPresentationRelatorABSq,
      alternatingSixPresentationGenerator] using
        alternatingSixPresentation_relations.2.2.2

/-- The homomorphism from the standard presentation to concrete `A₆`. -/
def alternatingSixPresentationToAlternatingSix :
    AlternatingSixPresentedGroup →* AlternatingSix :=
  PresentedGroup.toGroup
    alternatingSixPresentationGenerator_kills_relators

@[simp]
theorem alternatingSixPresentationToAlternatingSix_a :
    alternatingSixPresentationToAlternatingSix
        alternatingSixPresentedA =
      alternatingSixPresentationA := by
  simp [alternatingSixPresentationToAlternatingSix,
    alternatingSixPresentedA]

@[simp]
theorem alternatingSixPresentationToAlternatingSix_b :
    alternatingSixPresentationToAlternatingSix
        alternatingSixPresentedB =
      alternatingSixPresentationB := by
  simp [alternatingSixPresentationToAlternatingSix,
    alternatingSixPresentedB]

end GroupTheory
end McKayConjecture
