import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits Opposite GrothendieckTopology.Plus

set_option maxHeartbeats 800000

/-- On an irreducible space, the toPlus map for the constant presheaf is surjective
    at nonempty opens.

    Proof strategy using the concrete Plus API:
    1. By Plus.exists_rep, every element y ∈ plus(P)(U) equals Plus.mk(x) for some
       cover S of U and matching family x : Meq P S.
    2. For the constant presheaf P on irreducible X: all elements of a matching family
       at a nonempty open are equal (since nonempty opens have nonempty pairwise
       intersections, connecting all arrows via relations).
    3. Let a be this common value. Then y = Plus.mk(Meq.mk S a).
    4. By Plus.toPlus_eq_mk: toPlus(a) = Plus.mk(Meq.mk ⊤ a).
    5. By Plus.eq_mk_iff_exists: mk(Meq.mk ⊤ a) = mk(Meq.mk S a) because
       they agree on the common refinement S (both give a at each component).
    6. So y = toPlus(a), proving surjectivity.

    Key Mathlib tools:
    - GrothendieckTopology.Plus.exists_rep
    - GrothendieckTopology.Plus.toPlus_eq_mk (or toPlus_mk)
    - GrothendieckTopology.Plus.eq_mk_iff_exists
    - GrothendieckTopology.Plus.mk
    - Meq, Meq.mk, Meq.refine
    - Meq.condition (the compatibility condition on matching families)
    - IrreducibleSpace: any two nonempty opens intersect

    For the constant presheaf (Functor.const).obj A:
    - (Functor.const).obj A).map f = 𝟙 A for any f
    - Meq for constant presheaf: x(I) ∈ A for each arrow I, with x(R.fst) = x(R.snd) -/
theorem toPlus_surjective_of_irreducible_const
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ConcreteCategory.hom
      ((Opens.grothendieckTopology X).toPlus
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
        |>.app (Opposite.op U))) := by
  sorry
