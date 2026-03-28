import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits Opposite GrothendieckTopology.Plus

set_option maxHeartbeats 800000

-- Harmonic `generalize_proofs` tactic

/-- Matching families for the constant presheaf are constant at ALL arrows (including empty).

    For nonempty arrows: follows from irreducibility (nonempty opens intersect).
    For empty arrows I with I.Y = ⊥: construct a relation connecting I to any nonempty
    arrow J via Z = ⊥. Since ⊥ is initial, g₁ : ⊥ → I.Y and g₂ : ⊥ → J.Y exist,
    and the compatibility g₁ ≫ I.f = g₂ ≫ J.f holds (both are ⊥ → U, which is unique).
    The Meq condition then gives x(I) = x(J).

    Combined with the nonempty case: x(I) = x(J) for ALL I, J in the cover. -/
theorem meq_const_all {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    {U : Opens X} (hU : (U : Set X).Nonempty)
    {S : (Opens.grothendieckTopology X).Cover U}
    (x : Meq ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))) S)
    (I₁ I₂ : S.Arrow) : x I₁ = x I₂ := by
  sorry

/-- toPlus is surjective for the constant presheaf on irreducible X at nonempty opens.

    Proof:
    1. By Plus.exists_rep: y = mk(x) for some cover S and matching family x.
    2. Since S covers nonempty U, there exists an arrow I₀ with I₀.Y nonempty.
    3. Let a = x(I₀). By meq_const_all: x(I) = a for ALL arrows I in S.
    4. toPlus(a) = mk(Meq.mk ⊤ a) by Plus.toPlus_eq_mk.
    5. By Plus.eq_mk_iff_exists with W = S:
       - h₁ : S ⟶ S (identity)
       - h₂ : S ⟶ ⊤ (S ≤ ⊤ = le_top)
       - (Meq.mk ⊤ a).refine h₂ at I = a (const presheaf, P.map = id)
       - x.refine h₁ at I = x(I) = a (by meq_const_all)
       - They agree! So mk(Meq.mk ⊤ a) = mk(x).
    6. Therefore y = mk(x) = mk(Meq.mk ⊤ a) = toPlus(a). ✓ -/
theorem toPlus_surjective_of_irreducible_const
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ConcreteCategory.hom
      ((Opens.grothendieckTopology X).toPlus
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
        |>.app (Opposite.op U))) := by
  sorry
