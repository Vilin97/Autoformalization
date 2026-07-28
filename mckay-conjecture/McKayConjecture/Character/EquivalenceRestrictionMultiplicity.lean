/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordCorrespondence
import McKayConjecture.Character.Transport
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# Restriction multiplicity along a group equivalence

Pulling an irreducible character back along a group equivalence and then
restricting its original realization gives the same simple character.
Schur's lemma therefore makes the corresponding restriction multiplicity
exactly one.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CliffordCorrespondence

variable {G H : Type} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite G] in
/-- Restriction along a group equivalence contains the pulled-back
irreducible character with multiplicity one. -/
theorem restrictionMultiplicity_comap_mulEquiv_eq_one
    (e : H ≃* G)
    (χ : IrreducibleCharacter G) :
    restrictionMultiplicity e.toMonoidHom
      (χ.comap e) χ = 1 := by
  letI : Fintype H := Fintype.ofFinite H
  let V : FDRep ℂ H :=
    FDRep.res e.toMonoidHom χ.realization
  have hchar :
      V.character = (χ.comap e).values := by
    funext h
    rw [FDRep.res_character_apply,
      χ.realization_character]
    rfl
  letI : Simple V := by
    rw [FDRep.simple_iff_char_is_norm_one]
    rw [hchar,
      ← (χ.comap e).realization_character]
    exact
      (FDRep.simple_iff_char_is_norm_one
        (χ.comap e).realization).mp inferInstance
  obtain ⟨i :
      (χ.comap e).realization ≅ V⟩ :=
    FDRep.nonempty_iso_of_character_eq
      (χ.comap e).realization V (by
        rw [(χ.comap e).realization_character,
          hchar])
  exact
    (finrank_hom_simple_simple_eq_one_iff
      ℂ (χ.comap e).realization V).2 ⟨i⟩

omit [Finite G] in
/-- Every other irreducible character has multiplicity zero in restriction
along a group equivalence. -/
theorem restrictionMultiplicity_mulEquiv_eq_zero_of_ne
    (e : H ≃* G)
    (χ : IrreducibleCharacter G)
    (η : IrreducibleCharacter H)
    (hne : η ≠ χ.comap e) :
    restrictionMultiplicity e.toMonoidHom η χ = 0 := by
  letI : Fintype H := Fintype.ofFinite H
  let V : FDRep ℂ H :=
    FDRep.res e.toMonoidHom χ.realization
  have hchar :
      V.character = (χ.comap e).values := by
    funext h
    rw [FDRep.res_character_apply,
      χ.realization_character]
    rfl
  letI : Simple V := by
    rw [FDRep.simple_iff_char_is_norm_one]
    rw [hchar,
      ← (χ.comap e).realization_character]
    exact
      (FDRep.simple_iff_char_is_norm_one
        (χ.comap e).realization).mp inferInstance
  apply
    (finrank_hom_simple_simple_eq_zero_iff
      ℂ η.realization V).2
  exact
    ⟨fun i ↦ hne (by
      apply IrreducibleCharacter.ext
      exact η.realization_character.symm.trans
        ((FDRep.char_iso i).trans hchar))⟩

end CliffordCorrespondence
end McKayConjecture
