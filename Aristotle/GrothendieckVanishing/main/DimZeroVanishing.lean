/-
  DimZeroVanishing.lean — Vanishing for irreducible spaces of dimension 0

  On an irreducible space of dimension 0, the only open sets are ∅ and X.
  Therefore every sheaf has surjective (epi) restriction maps, i.e., is flasque.
  By FlasqueVanishing, all higher cohomology vanishes.

  This is Hartshorne III.2.7 Step 2.
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.Auxiliary

universe u

open CategoryTheory TopologicalSpace Limits Opposite

/-- On an irreducible space of dim ≤ 0, every sheaf has epi restriction maps.
    The only nonempty open is ⊤, so the only nontrivial restriction is F(⊤) → F(⊥),
    which is epi because F(⊥) is terminal (zero). -/
theorem sheaf_restriction_epi_of_irreducible_dim_zero
    (X : TopCat.{u}) [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {U V : Opens X} (i : U ⟶ V) :
    Epi (F.val.map i.op) := by
  -- U ≤ V in Opens X. We need F(V) → F(U) to be epi.
  rcases opens_eq_bot_or_top_of_irreducibleSpace_dim_zero hdim U with rfl | rfl
  · -- U = ⊥: F(V) → F(⊥) is epi because F(⊥) is terminal (zero)
    exact epi_of_isTerminal_tgt (isTerminal_sheaf_bot F) _
  · -- U = ⊤: then V = ⊤ (since U ≤ V and U = ⊤), so restriction is identity
    have hV := le_antisymm le_top (homOfLE le_top ≫ i |>.le)
    subst hV
    have : i = 𝟙 ⊤ := Subsingleton.elim _ _
    rw [this, op_id, F.val.map_id]
    infer_instance

/-! ## Alternative dim 0 proof via projectivity of constant sheaf -/

set_option synthInstance.maxHeartbeats 80000 in
/-- On a dim 0 irreducible nonempty space, Γ preserves epis.
    Proof: Γ ≅ eval_⊤ (via ΓNatIsoSheafSections), and eval_⊤ preserves epis
    because epi sheaf morphisms are surjective at ⊤ (epi_app_top_surjective). -/
noncomputable def gamma_preservesEpimorphisms_of_dim_zero
    (X : TopCat.{u}) [IrreducibleSpace X] [Nonempty X]
    (hdim : topologicalKrullDim X ≤ 0) :
    (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesEpimorphisms := by
  have heval : ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op ⊤)).PreservesEpimorphisms := by
    constructor; intro F G φ hφ
    apply ConcreteCategory.epi_of_surjective
    exact epi_app_top_surjective hdim φ
  exact @Functor.preservesEpimorphisms.of_iso _ _ _ _ _ _ heval
    (Sheaf.ΓNatIsoSheafSections _ AddCommGrpCat.{u} isTerminalTop).symm

set_option synthInstance.maxHeartbeats 80000 in
/-- On an irreducible Noetherian space of dim ≤ 0, all higher cohomology vanishes.
    Uses projectivity of constant sheaf (bypasses flasque_injective entirely).

    Chain: ULift ℤ projective in Ab → Γ preserves epis (dim 0) →
    constantSheaf(ULift ℤ) projective in Sh(X) → Ext vanishes. -/
noncomputable def grothendieck_vanishing_dim_zero
    (X : TopCat.{u}) [TopologicalSpace.NoetherianSpace X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  -- IrreducibleSpace implies Nonempty
  haveI : Nonempty X := ⟨(IrreducibleSpace.isIrreducible_univ X).nonempty.some⟩
  letI := gamma_preservesEpimorphisms_of_dim_zero X hdim
  have hproj : Projective ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) :=
    (constantSheafΓAdj _ AddCommGrpCat.{u}).map_projective _ inferInstance
  haveI := @instHasProjectiveDimensionLTOfNatNatOfProjective _ _ _ _ hproj
  unfold Sheaf.H
  exact HasProjectiveDimensionLT.subsingleton _ 1 (n + 1) (by omega) F
