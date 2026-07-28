/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Simple
import McKayConjecture.IrreducibleCharacter

/-!
# The trivial irreducible character

This file constructs the trivial ordinary irreducible complex character of an
arbitrary group.  No finiteness assumption on the group is needed: its
realizing representation is the one-dimensional trivial representation.
-/

noncomputable section

open CategoryTheory

universe u

namespace McKayConjecture
namespace IrreducibleCharacter

variable (G : Type u) [Group G]

/-- The one-dimensional trivial representation, regarded as an object of
`FDRep ℂ G`. -/
private abbrev trivialFDRep : FDRep ℂ G :=
  FDRep.of (Representation.trivial ℂ G ℂ)

private theorem trivialFDRep_simple : Simple (trivialFDRep G) := by
  letI : Simple (ModuleCat.of ℂ ℂ) :=
    simple_of_finrank_eq_one (k := ℂ) (R := ℂ) (by simp)
  letI : Simple (Rep.trivial ℂ G ℂ) :=
    Functor.simple_of_simple_obj
      (forget₂ (Rep ℂ G) (ModuleCat ℂ)) (Rep.trivial ℂ G ℂ)
  letI : Simple ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (trivialFDRep G)) := by
    change Simple (Rep.trivial ℂ G ℂ)
    infer_instance
  exact Functor.simple_of_simple_obj
    (forget₂ (FDRep ℂ G) (Rep ℂ G)) (trivialFDRep G)

/-- The trivial irreducible complex character of `G`. -/
def trivial : IrreducibleCharacter G where
  values := fun _ ↦ 1
  degree := 1
  isIrreducible := by
    letI : Simple (trivialFDRep G) := trivialFDRep_simple G
    refine ⟨trivialFDRep G, inferInstance, ?_, ?_⟩
    · funext g
      simp [trivialFDRep, FDRep.character]
    · simp [trivialFDRep]

@[simp]
theorem trivial_values (g : G) : (trivial G).values g = 1 :=
  rfl

@[simp]
theorem trivial_degree : (trivial G).degree = 1 :=
  rfl

/-- For a prime `p`, the trivial character has `p'`-degree. -/
theorem trivial_isPPrimeDegree (p : ℕ) [Fact p.Prime] :
    (trivial G).IsPPrimeDegree p := by
  rw [IsPPrimeDegree, trivial_degree]
  exact (Fact.out : p.Prime).not_dvd_one

/-- The trivial character as an element of `Irr_{p'}(G)`. -/
def trivialPPrime (p : ℕ) [Fact p.Prime] :
    PPrimeIrreducibleCharacter G p :=
  ⟨trivial G, trivial_isPPrimeDegree G p⟩

@[simp]
theorem trivialPPrime_degree (p : ℕ) [Fact p.Prime] :
    (trivialPPrime G p).1.degree = 1 :=
  rfl

end IrreducibleCharacter
end McKayConjecture
