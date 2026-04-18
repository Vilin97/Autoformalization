/-
  GrothendieckVanishing.lean — Main theorem

  Grothendieck's vanishing theorem (Hartshorne III.2.7):
  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  The proof assembles (FULLY PROVED — 0 sorry's):
  - Dim 0 case: handled inline (sheaf_restriction_epi_of_irreducible_dim_zero,
    grothendieck_vanishing_dim_zero)
  - IrreducibleStep + FiniteGeneratorReduction: irreducible dim >= 1 case
  - ClosedOpenDecomposition: reduction to irreducible
-/
import Aristotle.GrothendieckVanishing.main.ClosedOpenDecomposition
import Aristotle.GrothendieckVanishing.main.IrreducibleStep

universe u

open CategoryTheory TopologicalSpace Order Limits

/-! ## Dim 0 vanishing -/

/-- On an irreducible space of dim ≤ 0, every sheaf has epi restriction maps.
    The only nonempty open is ⊤, so the only nontrivial restriction is F(⊤) → F(⊥),
    which is epi because F(⊥) is terminal (zero). -/
private theorem sheaf_restriction_epi_of_irreducible_dim_zero
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
private theorem grothendieck_vanishing_dim_zero
    (X : TopCat.{u}) [TopologicalSpace.NoetherianSpace X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) :=
  FlasqueVanishing X F
    (fun i => sheaf_restriction_epi_of_irreducible_dim_zero X hdim F i) n

/-! ## Main theorem -/

/-- **Grothendieck's vanishing theorem** (Hartshorne III, Theorem 2.7). -/
theorem GrothendieckVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n) := by
  have hwf : WellFounded (fun (a b : WithBot ℕ∞) => a < b) := IsWellFounded.wf
  exact hwf.induction (C := fun d =>
    ∀ (X : TopCat.{u}) [NoetherianSpace X]
      (n : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X),
      topologicalKrullDim X = d → n > d → Subsingleton (Sheaf.H F n))
    (topologicalKrullDim X) (fun d ih X _ n F hd hn => by
      -- Reduce to irreducible X
      apply grothendieck_vanishing_of_irreducible X n (hd ▸ hn) F
      intro Y _ _ m G hle hY
      by_cases hdim : topologicalKrullDim Y ≤ 0
      · -- dim Y ≤ 0: use DimZeroVanishing
        have hm0 : m ≠ 0 := fun heq => by
          subst heq
          exact not_lt.mpr topologicalKrullDim_nonneg_of_irreducible (by exact_mod_cast hY)
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
        exact grothendieck_vanishing_dim_zero Y hdim G k
      · -- dim Y > 0: use IrreducibleStep
        push_neg at hdim
        exact IrreduciblePosVanishing Y m hY hdim G
          (fun Z _ m' G' hlt hG' =>
            ih (topologicalKrullDim Z) (lt_of_lt_of_le hlt (hd ▸ hle)) Z m' G' rfl hG'))
    X n F rfl h
