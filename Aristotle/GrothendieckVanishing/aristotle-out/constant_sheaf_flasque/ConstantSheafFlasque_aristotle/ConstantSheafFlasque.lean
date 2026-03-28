import Mathlib

universe u

open CategoryTheory TopologicalSpace Opposite

/-- The bottom sieve covers ⊥ in the opens Grothendieck topology. -/
lemma bot_mem_opens_grothendieckTopology_bot (X : TopCat.{u}) :
    ⊥ ∈ (Opens.grothendieckTopology X) ⊥ := by
  aesop_cat

/-- For any sheaf F on Opens X with values in AddCommGrpCat, F(⊥) is zero
    (terminal, hence zero in AddCommGrpCat), so any map to it is epi. -/
lemma epi_of_target_bot (X : TopCat.{u})
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {V : Opens X} (f : F.val.obj (op V) ⟶ F.val.obj (op ⊥)) :
    Epi f :=
  (F.isTerminalOfBotCover ⊥ (bot_mem_opens_grothendieckTopology_bot X)).isZero.epi f

/-- On an irreducible space, every nonempty open is irreducible. -/
lemma IsIrreducible_of_nonempty_open (X : TopCat.{u}) [IrreducibleSpace X]
    (W : Opens X) (hW : W ≠ ⊥) :
    IsIrreducible (W : Set X) := by
  sorry

/-- The constant presheaf satisfies the sheaf condition (as a presheaf of sets via
    coyoneda) at every nonempty open of an irreducible space. -/
lemma constPresheaf_isSheafFor_nonempty (X : TopCat.{u}) [IrreducibleSpace X]
    (A : AddCommGrpCat.{u}) (E : AddCommGrpCat.{u})
    (W : Opens X) (hW : W ≠ ⊥)
    (S : Sieve W) (hS : S ∈ (Opens.grothendieckTopology X) W) :
    Presieve.IsSheafFor
      (((Functor.const (Opens X)ᵒᵖ).obj A ⋙ coyoneda.obj (op E))) S.arrows := by
  sorry

/-- The sheafification unit for the constant presheaf is epi at nonempty opens. -/
lemma sheafificationUnit_epi_of_nonempty
    (X : TopCat.{u}) [IrreducibleSpace X] (W : Opens X) (hW : W ≠ ⊥) :
    Epi ((sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).unit.app
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u} ℤ))) |>.app (op W)) := by
  sorry

/-- Combining the empty and nonempty cases. -/
lemma sheafificationUnit_epi_constantPresheaf
    (X : TopCat.{u}) [IrreducibleSpace X] (U : (Opens X)ᵒᵖ) :
    Epi ((sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).unit.app
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u} ℤ))) |>.app U) := by
  by_cases hU : U.unop = ⊥
  · obtain ⟨W⟩ := U; subst hU; sorry
  · exact sheafificationUnit_epi_of_nonempty X U.unop hU

/-- On an irreducible space, the constant sheaf Z (= AddCommGrpCat.of (ULift ℤ))
    has epi (surjective) restriction maps, i.e., is flasque.

    Proof strategy: Use naturality of the sheafification unit η.
    Since the constant presheaf has identity restriction maps,
    η.app (op U) = η.app (op V) ≫ F.val.map i.op.
    By `sheafificationUnit_epi_constantPresheaf`, η.app (op U) is epi.
    By `epi_of_epi`, F.val.map i.op is epi. -/
theorem constantSheaf_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X]
    {U V : Opens X} (i : U ⟶ V) :
    Epi (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))).val.map i.op) := by
  sorry
