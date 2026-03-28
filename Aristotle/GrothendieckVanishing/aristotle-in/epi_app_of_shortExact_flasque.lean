-- Harmonic `generalize_proofs` tactic
import Mathlib

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-- A sheaf of abelian groups is **flasque** if all restriction maps are epi.
    This is equivalent to surjectivity of restriction on sections. -/
def IsFlasqueSheaf {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op)

/-- **Zorn argument** (Nugent, PR #35790, `epi_of_shortExact`).
    In a SES `0 -> F' -> G -> H -> 0` with `F'` flasque, the map `G(U) -> H(U)` is epi.

    Proof sketch: given `s : H(U)`, consider the poset of pairs `(V, t)` where `V ≤ U`
    is open and `t : G(V)` maps to `s|_V`. By Zorn (using the sheaf gluing axiom for
    chains), there is a maximal such pair. Local surjectivity of `G -> H` (from epi)
    plus flasqueness of `F'` (to patch the difference) show the maximal `V` must be `U`. -/
theorem epi_app_of_shortExact_flasque {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (hFlasque₁ : IsFlasqueSheaf S.X₁) (U : Opens X) :
    Epi (S.g.val.app (op U)) := by
  sorry
