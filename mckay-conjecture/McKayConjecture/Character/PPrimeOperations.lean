/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InductionCharacter

/-!
# `p'`-degree and representation induction

Induction multiplies dimension by the subgroup index.  For a prime `p`, the
induced representation has `p'`-dimension exactly when both the original
dimension and the index are prime to `p`.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture

/-- A finite-dimensional complex representation has `p'`-dimension when
`p` does not divide its dimension. -/
def FDRep.HasPPrimeDimension {G : Type} [Group G]
    (p : ℕ) (V : FDRep ℂ G) : Prop :=
  ¬p ∣ Module.finrank ℂ V

namespace FDRep

variable {G : Type} [Group G] [Finite G]

/-- The dimension of an induced representation is the subgroup index times
the original dimension. -/
theorem finrank_indSubgroup (S : Subgroup G)
    (V : FDRep ℂ S) :
    Module.finrank ℂ (FDRep.ind S.subtype V) =
      S.index * Module.finrank ℂ V := by
  letI : Fintype G := Fintype.ofFinite G
  apply Nat.cast_injective (R := ℂ)
  calc
    (Module.finrank ℂ (FDRep.ind S.subtype V) : ℂ) =
        (FDRep.ind S.subtype V).character 1 := by
      rw [FDRep.char_one]
    _ = ClassFunction.induce S V.characterClassFunction 1 :=
      InductionCharacter.ind_character_eq_induce S V 1
    _ = (S.index : ℂ) * Module.finrank ℂ V :=
      ClassFunction.induce_character_apply_one S V
    _ = (S.index * Module.finrank ℂ V : ℕ) := by
      push_cast
      rfl

/-- Prime-to-`p` dimension is preserved by induction exactly when the
subgroup index is also prime to `p`. -/
theorem hasPPrimeDimension_indSubgroup_iff
    {p : ℕ} (hp : p.Prime)
    (S : Subgroup G) (V : FDRep ℂ S) :
    FDRep.HasPPrimeDimension p (FDRep.ind S.subtype V) ↔
      ¬p ∣ S.index ∧ FDRep.HasPPrimeDimension p V := by
  rw [FDRep.HasPPrimeDimension, FDRep.HasPPrimeDimension,
    finrank_indSubgroup, hp.dvd_mul]
  tauto

/-- Forward form of the prime-to-`p` induction criterion. -/
theorem hasPPrimeDimension_indSubgroup
    {p : ℕ} (hp : p.Prime)
    (S : Subgroup G) (V : FDRep ℂ S)
    (hindex : ¬p ∣ S.index)
    (hV : FDRep.HasPPrimeDimension p V) :
    FDRep.HasPPrimeDimension p (FDRep.ind S.subtype V) :=
  (hasPPrimeDimension_indSubgroup_iff hp S V).2
    ⟨hindex, hV⟩

end FDRep
end McKayConjecture
