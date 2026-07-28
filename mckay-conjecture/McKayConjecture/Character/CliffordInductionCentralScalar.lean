/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalarConstituent

/-!
# Central scalars and Clifford induction

The irreducible character obtained by a verified-simple Clifford induction
contains its inertia-group source upon restriction back to the inertia
subgroup.  Consequently a central element already lying in that inertia
subgroup acts by the same normalized scalar before and after induction.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CliffordCorrespondence

variable {G : Type} [Group G] [Fintype G]
variable (N : Subgroup G) [N.Normal]
variable (θ : IrreducibleCharacter N)

/-- A verified-simple Clifford induction lies over its inertia-group source
when restricted back to the inertia subgroup. -/
theorem inducedIrreducibleCharacter_liesOver_inertia
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hsimple : Simple (inertiaInduction N θ ψ.realization)) :
    LiesOverAlong
      (IrreducibleCharacter.inertia N θ).subtype
      ψ
      (inducedIrreducibleCharacter N θ ψ hsimple) := by
  let χ :=
    inducedIrreducibleCharacter N θ ψ hsimple
  let u :=
    inertiaInductionUnit N θ ψ.realization
  have hu : u ≠ 0 :=
    inertiaInductionUnit_ne_zero N θ ψ.realization hsimple
  letI : Simple (inertiaInduction N θ ψ.realization) :=
    hsimple
  have hcharacter :
      (inertiaInduction N θ ψ.realization).character =
        χ.realization.character := by
    rw [χ.realization_character]
    rfl
  obtain ⟨e⟩ :=
    FDRep.nonempty_iso_of_character_eq
      (inertiaInduction N θ ψ.realization)
      χ.realization hcharacter
  let eI :=
    (FDRep.resSubgroupFunctor
      (k := ℂ) (IrreducibleCharacter.inertia N θ)).map e.hom
  let composite :
      ψ.realization ⟶
        FDRep.resSubgroup
          (IrreducibleCharacter.inertia N θ)
          χ.realization :=
    u ≫ eI
  haveI : Mono u :=
    mono_of_nonzero_from_simple hu
  haveI : Mono eI := by
    dsimp [eI]
    infer_instance
  haveI : Mono composite := by
    dsimp [composite]
    exact mono_comp u eI
  rw [LiesOverAlong, restrictionMultiplicity,
    Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨composite, ?_⟩
  intro hzero
  apply id_nonzero ψ.realization
  apply (cancel_mono composite).mp
  simp [hzero]

/-- Clifford induction preserves the normalized value of an ambient-central
element lying in the inertia subgroup. -/
theorem inducedIrreducibleCharacter_central_cross
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hsimple : Simple (inertiaInduction N θ ψ.realization))
    (z : IrreducibleCharacter.inertia N θ)
    (hzG : (z : G) ∈ Subgroup.center G) :
    (inducedIrreducibleCharacter N θ ψ hsimple).values (z : G) *
        (ψ.degree : ℂ) =
      ψ.values z *
        ((inducedIrreducibleCharacter N θ ψ hsimple).degree : ℂ) :=
  central_cross_of_liesOverSubgroup
    (IrreducibleCharacter.inertia N θ)
    ψ
    (inducedIrreducibleCharacter N θ ψ hsimple)
    (inducedIrreducibleCharacter_liesOver_inertia
      N θ ψ hsimple)
    z hzG

/-- The ordinary Clifford correspondence preserves normalized values of
ambient-central elements. -/
theorem induceOverInertiaOrbit_central_cross
    (ψ : IrreducibleCharactersOverInertia N θ)
    (z : IrreducibleCharacter.inertia N θ)
    (hzG : (z : G) ∈ Subgroup.center G) :
    (CliffordEquivalence.induceOverInertiaOrbit
          N θ ψ).1.values (z : G) *
        (ψ.1.degree : ℂ) =
      ψ.1.values z *
        ((CliffordEquivalence.induceOverInertiaOrbit
          N θ ψ).1.degree : ℂ) := by
  simpa only [
    CliffordEquivalence.induceOverInertiaOrbit,
    induceSimpleOverInertiaOrbit,
    induceSimpleOverInertia
  ] using
    inducedIrreducibleCharacter_central_cross
      N θ ψ.1
        (CliffordEquivalence.inertiaInduction_simple
          N θ ψ.1 ψ.2)
        z hzG

end CliffordCorrespondence
end McKayConjecture
