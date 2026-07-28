/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordModule
import McKayConjecture.Character.Realization
import McKayConjecture.Character.Restriction

/-!
# Clifford theory for restricted finite-dimensional representations

This file connects categorical simplicity for `FDRep` with the
module-theoretic Clifford theorem in `CliffordModule`.

For a simple finite-dimensional representation `V` and a normal subgroup
`N`, the group-algebra module underlying `FDRep.resSubgroup N V` is
semisimple and contains a nonzero simple submodule.  The final results
specialize this statement to the chosen realization of an
`IrreducibleCharacter`.
-/

open CategoryTheory
open scoped MonoidAlgebra

universe u v

namespace McKayConjecture.CliffordRestriction

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/-- The carrier of a categorically simple finite-dimensional representation
is nontrivial. -/
theorem nontrivial_of_simple (V : FDRep k G) [Simple V] : Nontrivial V := by
  rw [nontrivial_iff]
  by_contra h
  push Not at h
  exact id_nonzero V (by
    apply ConcreteCategory.hom_ext
    intro x
    exact h x 0)

/-- A categorically simple finite-dimensional representation is irreducible
in the subrepresentation-lattice sense.

For an invariant subspace `W`, its inclusion into `V` is a monomorphism in
`FDRep`.  Simplicity makes that inclusion either zero or an isomorphism,
forcing `W` to be respectively bottom or top. -/
theorem isIrreducible_of_simple (V : FDRep k G) [Simple V] :
    Representation.IsIrreducible V.ρ := by
  letI : Nontrivial V := nontrivial_of_simple V
  letI : Nontrivial (Subrepresentation V.ρ) :=
    ⟨⟨⊥, ⊤, fun h =>
      bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩⟩
  refine ⟨fun W => ?_⟩
  let ι : FDRep.of W.toRepresentation ⟶ V :=
    { hom := FGModuleCat.ofHom W.toSubmodule.subtype
      comm := by
        intro g
        apply FGModuleCat.hom_ext
        ext w
        rfl }
  letI : Mono ι :=
    ConcreteCategory.mono_of_injective ι Subtype.val_injective
  by_cases hι : ι = 0
  · left
    apply Subrepresentation.ext
    apply (Submodule.eq_bot_iff W.toSubmodule).mpr
    intro x hx
    let wx : W.toSubmodule := ⟨x, hx⟩
    have heq := ConcreteCategory.congr_hom hι wx
    change x = 0 at heq
    exact heq
  · right
    letI : IsIso ι := isIso_of_mono_of_nonzero hι
    apply Subrepresentation.ext
    apply top_unique
    intro x _
    obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso ι).2 x
    change (w : V) = x at hw
    exact hw ▸ w.property

/-- Clifford semisimplicity for a normal-subgroup restriction of a simple
finite-dimensional representation. -/
theorem isSemisimpleModule_resSubgroup
    (V : FDRep k G) [Simple V] (N : Subgroup G) [N.Normal] :
    IsSemisimpleModule k[N]
      (Representation.asModule (FDRep.resSubgroup N V).ρ) := by
  letI : Nontrivial V := nontrivial_of_simple V
  letI : Representation.IsIrreducible V.ρ := isIrreducible_of_simple V
  exact
    CliffordModule.isSemisimpleModule_resRep_of_isIrreducible
      (H := N) V.ρ

/-- A normal-subgroup restriction of a simple finite-dimensional
representation has a nonzero simple constituent. -/
theorem exists_simple_constituent_resSubgroup
    (V : FDRep k G) [Simple V] (N : Subgroup G) [N.Normal] :
    ∃ W : Submodule k[N]
        (Representation.asModule (FDRep.resSubgroup N V).ρ),
      W ≠ ⊥ ∧ IsSimpleModule k[N] W := by
  letI : Nontrivial V := nontrivial_of_simple V
  letI :
      Nontrivial (Representation.asModule (FDRep.resSubgroup N V).ρ) :=
    ‹Nontrivial V›
  letI :
      IsSemisimpleModule k[N]
        (Representation.asModule (FDRep.resSubgroup N V).ρ) :=
    isSemisimpleModule_resSubgroup V N
  obtain ⟨W, -, hW⟩ :=
    (IsSemisimpleModule.eq_bot_or_exists_simple_le
      (⊤ : Submodule k[N]
        (Representation.asModule
          (FDRep.resSubgroup N V).ρ))).resolve_left top_ne_bot
  exact ⟨W, (isSimpleModule_iff_isAtom.mp hW).1, hW⟩

end McKayConjecture.CliffordRestriction

namespace McKayConjecture.IrreducibleCharacter

variable {G : Type v} [Group G]

/-- The restriction of the chosen realization of an irreducible character to
a normal subgroup is semisimple. -/
theorem realization_restriction_semisimple
    (χ : IrreducibleCharacter G) (N : Subgroup G) [N.Normal] :
    IsSemisimpleModule ℂ[N]
      (Representation.asModule (FDRep.resSubgroup N χ.realization).ρ) :=
  CliffordRestriction.isSemisimpleModule_resSubgroup χ.realization N

/-- The restriction of the chosen realization of an irreducible character
contains a nonzero simple constituent. -/
theorem exists_simple_constituent_realization_restriction
    (χ : IrreducibleCharacter G) (N : Subgroup G) [N.Normal] :
    ∃ W : Submodule ℂ[N]
        (Representation.asModule (FDRep.resSubgroup N χ.realization).ρ),
      W ≠ ⊥ ∧ IsSimpleModule ℂ[N] W :=
  CliffordRestriction.exists_simple_constituent_resSubgroup χ.realization N

/-- The Clifford restriction package for the chosen realization of an
irreducible character: semisimplicity together with an explicit nonzero
simple constituent. -/
theorem realization_clifford_restriction
    (χ : IrreducibleCharacter G) (N : Subgroup G) [N.Normal] :
    IsSemisimpleModule ℂ[N]
        (Representation.asModule (FDRep.resSubgroup N χ.realization).ρ) ∧
      ∃ W : Submodule ℂ[N]
          (Representation.asModule (FDRep.resSubgroup N χ.realization).ρ),
        W ≠ ⊥ ∧ IsSimpleModule ℂ[N] W :=
  ⟨χ.realization_restriction_semisimple N,
    χ.exists_simple_constituent_realization_restriction N⟩

end McKayConjecture.IrreducibleCharacter
