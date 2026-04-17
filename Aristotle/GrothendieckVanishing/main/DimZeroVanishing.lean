/-
  DimZeroVanishing.lean — Vanishing for irreducible spaces of dimension 0

  On an irreducible space of dimension 0, the only open sets are ∅ and X.
  Therefore every sheaf has surjective (epi) restriction maps, i.e., is flasque.
  By FlasqueVanishing, all higher cohomology vanishes.

  This is Hartshorne III.2.7 Step 2.
-/
import Aristotle.GrothendieckVanishing.main.SetupCore
import Aristotle.GrothendieckVanishing.main.TopologicalKrullDim

universe u

open CategoryTheory TopologicalSpace Limits

/-- On an irreducible space of dim ≤ 0, every sheaf has epi restriction maps.
    The only nonempty open is ⊤, so the only nontrivial restriction is F(⊤) → F(⊥),
    which is epi because F(⊥) is terminal (zero). -/
theorem sheaf_restriction_epi_of_irreducible_dim_zero
    (X : TopCat.{u}) [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {U V : Opens X} (i : U ⟶ V) :
    Epi (F.val.map i.op) := by
  rcases opens_eq_bot_or_top_of_irreducibleSpace_dim_zero hdim U with rfl | rfl
  · exact F.isTerminalOfEmpty.isZero.epi _
  · have hV := le_antisymm le_top (homOfLE le_top ≫ i |>.le); subst hV
    rw [Subsingleton.elim i (𝟙 ⊤), op_id, F.val.map_id]; infer_instance

/-- On an irreducible Noetherian space of dim ≤ 0, all higher cohomology vanishes.
    Hartshorne III.2.7, Step 2. Uses FlasqueVanishing applied to sheaves that are
    flasque because the only opens are ⊥ and ⊤. -/
theorem grothendieck_vanishing_dim_zero
    (X : TopCat.{u}) [TopologicalSpace.NoetherianSpace X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) :=
  FlasqueVanishing X F
    (fun i => sheaf_restriction_epi_of_irreducible_dim_zero X hdim F i) n
