import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits Opposite

set_option maxHeartbeats 800000

/-- On an irreducible space, a matching family for the constant presheaf over a
    cover of a nonempty open consists of equal elements at all nonempty arrows.

    This is because: for any two arrows I₁, I₂ in the cover with nonempty domains,
    I₁.Y ∩ I₂.Y is nonempty (irreducible space property), so there exists a relation
    connecting them, forcing x(I₁) = x(I₂).

    Key facts used:
    - Meq.condition: for any relation R, P.map R.g₁.op (x R.fst) = P.map R.g₂.op (x R.snd)
    - For constant presheaf: P.map f = 𝟙, so x(R.fst) = x(R.snd)
    - On irreducible X: nonempty opens have nonempty intersection (IsIrreducible.inter) -/
theorem meq_const_of_irreducible
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    {U : Opens X} {S : (Opens.grothendieckTopology X).Cover U}
    (x : Meq ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))) S)
    {I₁ I₂ : S.Arrow} (h₁ : (I₁.Y : Set X).Nonempty) (h₂ : (I₂.Y : Set X).Nonempty) :
    x I₁ = x I₂ := by
  sorry
