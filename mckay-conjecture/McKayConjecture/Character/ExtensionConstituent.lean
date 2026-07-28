/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordCorrespondence
import McKayConjecture.Character.Extension
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# Extensions are constituents

An irreducible character extending another irreducible character restricts
to exactly that character, hence in particular lies over it.  This small
bridge is useful when an explicit extension is used to prove activation of
a Clifford orbit.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G H : Type} [Group G] [Group H] [Finite H]

/-- An irreducible extension has positive restriction multiplicity. -/
theorem IsExtensionAlong.liesOver
    {f : H →* G}
    {χ : IrreducibleCharacter H}
    {ψ : IrreducibleCharacter G}
    (hψ : IsExtensionAlong f χ ψ) :
    CliffordCorrespondence.LiesOverAlong f χ ψ := by
  letI : Fintype H := Fintype.ofFinite H
  letI : Simple (FDRep.res f ψ.realization) := by
    rw [FDRep.simple_iff_char_is_norm_one]
    have hsimple : Simple χ.realization :=
      inferInstance
    have hnorm :=
      (FDRep.simple_iff_char_is_norm_one
        χ.realization).mp hsimple
    rw [hψ.realization_character,
      ← χ.realization_character]
    exact hnorm
  rw [CliffordCorrespondence.liesOverAlong_iff_exists_nonzero]
  obtain ⟨i :
      χ.realization ≅ FDRep.res f ψ.realization⟩ :=
    FDRep.nonempty_iso_of_character_eq
      χ.realization
      (FDRep.res f ψ.realization) (by
        rw [χ.realization_character,
          hψ.realization_character])
  refine ⟨i.hom, ?_⟩
  intro hi
  exact
    Simple.not_isZero χ.realization
      (Limits.IsZero.of_mono_eq_zero i.hom hi)

end IrreducibleCharacter
end McKayConjecture
