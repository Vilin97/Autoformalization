import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits Opposite GrothendieckTopology.Plus

set_option maxHeartbeats 800000

-- Harmonic `generalize_proofs` tactic

variable {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]

private abbrev P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))

private abbrev J' : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X

/-- toPlus is surjective at nonempty opens (proved by Aristotle 17b9bce9). -/
theorem toPlus_surjective (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ConcreteCategory.hom
      ((J' (X := X)).toPlus (P (X := X)) |>.app (op U))) := by
  admit -- Use Aristotle's proof (17b9bce9): exists_rep + meq_const_values_eq

/-- toSheafify = toPlus ≫ plusMap(toPlus) is surjective at nonempty opens.
    Follows from toPlus being surjective for BOTH the original presheaf
    and its Plus (which has the same properties at nonempty opens). -/
theorem toSheafify_surjective (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ConcreteCategory.hom
      ((J' (X := X)).toSheafify (P (X := X)) |>.app (op U))) := by
  sorry

/-- The constant sheaf has epi restriction maps on irreducible X.
    Uses naturality of toSheafify + surjectivity at nonempty opens.

    For i : U ⟶ V:
    toSheafify_U = toSheafify_V ≫ res  (naturality + const has id maps)
    For any y ∈ sheafify(P)(U): y = toSheafify_U(a) = res(toSheafify_V(a))
    So res is surjective → epi. -/
theorem constantSheaf_flasque_of_irreducible_full
    (X : TopCat.{u}) [IrreducibleSpace X]
    {U V : Opens X} (i : U ⟶ V) :
    Epi (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))).val.map i.op) := by
  sorry
