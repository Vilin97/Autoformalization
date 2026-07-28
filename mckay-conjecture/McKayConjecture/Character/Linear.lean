/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Simple
import McKayConjecture.Character.Construction
import McKayConjecture.Character.Transport
import McKayConjecture.Character.Trivial

/-!
# Linear characters

A homomorphism `λ : G →* ℂˣ` affords a one-dimensional representation and
hence an irreducible character of degree one.  The construction is available
for arbitrary groups and is injective.
-/

noncomputable section

open CategoryTheory

universe u v

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type u} [Group G]

/-- The one-dimensional representation associated to
`λ : G →* ℂˣ`. -/
def linearRepresentation (lam : G →* ℂˣ) :
    Representation ℂ G ℂ where
  toFun g := (lam g : ℂ) • (LinearMap.id : Module.End ℂ ℂ)
  map_one' := by
    rw [map_one, Units.val_one]
    apply LinearMap.ext
    intro z
    simp
  map_mul' g h := by
    rw [map_mul, Units.val_mul]
    apply LinearMap.ext
    intro z
    simp [Module.End.mul_apply, smul_smul, mul_comm]

/-- The corresponding finite-dimensional representation object. -/
abbrev linearFDRep (lam : G →* ℂˣ) : FDRep ℂ G :=
  FDRep.of (linearRepresentation lam)

/-- Every one-dimensional representation is a simple object. -/
theorem linearFDRep_simple (lam : G →* ℂˣ) :
    Simple (linearFDRep lam) := by
  letI : Simple (ModuleCat.of ℂ ℂ) :=
    simple_of_finrank_eq_one (k := ℂ) (R := ℂ) (by simp)
  letI : Simple ((forget₂ (Rep ℂ G) (ModuleCat ℂ)).obj
      (Rep.of (linearRepresentation lam))) :=
    inferInstance
  letI : Simple (Rep.of (linearRepresentation lam)) :=
    Functor.simple_of_simple_obj
      (forget₂ (Rep ℂ G) (ModuleCat ℂ))
      (Rep.of (linearRepresentation lam))
  letI : Simple ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj
      (linearFDRep lam)) := by
    change Simple (Rep.of (linearRepresentation lam))
    infer_instance
  exact Functor.simple_of_simple_obj
    (forget₂ (FDRep ℂ G) (Rep ℂ G)) (linearFDRep lam)

@[simp]
theorem linearFDRep_character (lam : G →* ℂˣ) :
    (linearFDRep lam).character = fun g ↦ (lam g : ℂ) := by
  funext g
  change
    LinearMap.trace ℂ ℂ
        ((lam g : ℂ) • (LinearMap.id : Module.End ℂ ℂ)) =
      (lam g : ℂ)
  rw [map_smul, LinearMap.trace_id]
  simp

@[simp]
theorem linearFDRep_finrank (lam : G →* ℂˣ) :
    Module.finrank ℂ (linearFDRep lam) = 1 := by
  simp [linearFDRep]

/-- A multiplicative homomorphism to `ℂˣ`, regarded as an irreducible
character. -/
def linear (lam : G →* ℂˣ) : IrreducibleCharacter G := by
  letI : Simple (linearFDRep lam) := linearFDRep_simple lam
  exact ofSimple (linearFDRep lam)

@[simp]
theorem linear_values (lam : G →* ℂˣ) (g : G) :
    (linear lam).values g = (lam g : ℂ) := by
  change (linearFDRep lam).character g = (lam g : ℂ)
  rw [linearFDRep_character]

@[simp]
theorem linear_degree (lam : G →* ℂˣ) :
    (linear lam).degree = 1 := by
  change Module.finrank ℂ (linearFDRep lam) = 1
  exact linearFDRep_finrank lam

/-- The construction of a linear irreducible character is injective. -/
theorem linear_injective :
    Function.Injective (linear (G := G)) := by
  intro lam mu h
  apply MonoidHom.ext
  intro g
  apply Units.ext
  have hg := congrArg (fun χ : IrreducibleCharacter G ↦ χ.values g) h
  simpa using hg

@[simp]
theorem linear_eq_trivial_iff (lam : G →* ℂˣ) :
    linear lam = trivial G ↔ lam = 1 := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro g
    apply Units.ext
    have hg := congrArg (fun χ : IrreducibleCharacter G ↦ χ.values g) h
    simpa using hg
  · rintro rfl
    apply IrreducibleCharacter.ext
    funext g
    simp

/-- Pullback of a linear character agrees with composition of the underlying
homomorphism. -/
theorem linear_comap
    {H : Type v} [Group H] (e : H ≃* G) (lam : G →* ℂˣ) :
    (linear lam).comap e = linear (lam.comp (e : H →* G)) := by
  apply IrreducibleCharacter.ext
  funext h
  simp

/-- Every linear character has `p'`-degree for a prime `p`. -/
theorem linear_isPPrimeDegree (lam : G →* ℂˣ)
    (p : ℕ) [Fact p.Prime] :
    (linear lam).IsPPrimeDegree p := by
  rw [IsPPrimeDegree, linear_degree]
  exact (Fact.out : p.Prime).not_dvd_one

end IrreducibleCharacter
end McKayConjecture
