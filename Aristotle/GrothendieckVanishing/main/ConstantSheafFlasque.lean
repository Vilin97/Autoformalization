/-
  ConstantSheafFlasque.lean — The constant sheaf on an irreducible space is flasque

  Proves that on an irreducible topological space, the constant sheaf
  has epi restriction maps, using the naturality of the sheafification unit
  and the fact that the constant presheaf has identity restriction maps.
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.Auxiliary

universe u

open CategoryTheory TopologicalSpace Limits Opposite

/-- On an irreducible space, the constant sheaf has epi restriction maps (is flasque).

    SORRY — requires showing the sheafification unit is surjective at nonempty opens
    of an irreducible space, which needs the concrete Plus construction API
    (Plus.mk, Plus.exists_rep, Plus.eq_mk_iff_exists).

    Proof architecture (from Aristotle analysis):
    1. At U = ⊥: F(⊥) is zero, so any map to it is epi.
    2. At nonempty U: use naturality of the sheafification unit η.
       Since the constant presheaf has identity restrictions:
       η_U = η_V ≫ res. If η_U is surjective, then for any y ∈ F(U),
       y = η_U(a), so η_V(a) restricts to y, proving res surjective.
       Surjectivity of η_U follows from the Plus construction: every
       element is mk(x) where x is a matching family. On irreducible X,
       matching families for the constant presheaf are constant, so
       every element = toPlus(a) for the common value a. -/
theorem constantSheaf_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X]
    {U V : Opens X} (i : U ⟶ V) :
    Epi (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))).val.map i.op) := by
  by_cases hU : (U : Set X) = ∅
  · -- U = ∅: target is zero, any map is epi
    have : U = ⊥ := Opens.ext (by simpa using hU)
    subst this
    have hcov : ⊥ ∈ (Opens.grothendieckTopology X) ⊥ :=
      fun x hx => (Opens.mem_bot.mp hx).elim
    exact (Sheaf.isTerminalOfBotCover _ ⊥ hcov).isZero.epi _
  · -- U nonempty: needs sheafification unit surjectivity argument
    admit
