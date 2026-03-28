/-
  ConstantSheafFlasque.lean — The constant sheaf on an irreducible space is flasque

  Proves that on an irreducible topological space, the constant sheaf
  has epi restriction maps, using the naturality of the sheafification unit
  and the fact that the constant presheaf has identity restriction maps.

  The proof chain (all steps mathematically verified, formalization in progress):
  1. toPlus surjective at nonempty U (Aristotle 17b9bce9, sorry-free)
  2. toPlus injective at nonempty U (by eq_mk_iff_exists + covers have arrows)
  3. plusObj(constP) has identity restrictions at nonempty opens (by 1+2)
  4. toPlus(plusObj P) surjective at nonempty U (by same argument as 1, using 3)
  5. toSheafify = toPlus ≫ toPlus(plusObj P) surjective (by 1+4, plusMap_toPlus)
  6. Naturality: toSheafify_U = toSheafify_V ≫ res (const has id maps)
  7. Surjectivity of toSheafify_U → surjectivity of res → Epi
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.Auxiliary

universe u

open CategoryTheory TopologicalSpace Limits Opposite

/-- On an irreducible space, the constant sheaf has epi restriction maps (is flasque).

    The full proof requires showing `J.toSheafify` (the sheafification unit) is surjective
    at nonempty opens. This follows from:
    1. `toPlus` is surjective for the constant presheaf (Aristotle proved this)
    2. `toPlus(plusObj P)` is surjective (same argument, since `plusObj P` has
       the same properties at nonempty opens)
    3. `toSheafify = toPlus ≫ toPlus(plusObj P)` (by `plusMap_toPlus`)
    4. Composition of surjective maps is surjective
    5. Naturality: `toSheafify_U = toSheafify_V ≫ res` (const has identity maps)
    6. Surjectivity of `toSheafify_U` → surjectivity of `res` → Epi

    SORRY on the nonempty case — the sheafification unit surjectivity is mathematically
    proved but the formalization through the double Plus construction API is technically
    involved. Multiple Aristotle jobs are working on this. -/
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
  · -- U nonempty: by naturality of toSheafify + surjectivity at nonempty opens
    -- The full mathematical proof is in the docstring above.
    admit
