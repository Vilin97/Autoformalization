/-
  ClosedOpenDecomposition.lean — Reduction from general to irreducible spaces

  All cases proved (sorry-free):
  - Empty X: all sheaves are zero → Ext vanishes
  - Irreducible X: apply ih_irred directly
  - Reducible X: Finset.induction on irreducible components
-/
import Aristotle.GrothendieckVanishing.main.SetupCore
import Aristotle.GrothendieckVanishing.main.TopologicalKrullDim

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-! ## Reducible vanishing -/

private theorem ReducibleVanishing'
    (X : TopCat.{u}) [NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (_ : ¬ IrreducibleSpace X) [Nonempty X]
    (ih_irred : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      [IrreducibleSpace Y] (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      n > topologicalKrullDim Y → Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) := by
  classical
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := X)
  set comps := hfin.toFinset with comps_def
  have hcover : ∀ x : X, x ∈ ⋃₀ (comps : Set (Set X)) := by
    intro x; simp [comps_def, Set.Finite.toFinset]
    exact Set.mem_sUnion.mp
      (sUnion_irreducibleComponents (X := (↑X : Type u)) ▸ Set.mem_univ x)
  have hcomp_irred : ∀ Z ∈ comps, Z ∈ irreducibleComponents X := by
    intro Z hZ; simp [comps_def] at hZ; exact hZ
  suffices ∀ (s : Finset (Set X)),
      (∀ Z ∈ s, Z ∈ irreducibleComponents X) →
      ∀ (G : TopCat.Sheaf AddCommGrpCat.{u} X),
      (∀ x : X, x ∉ ⋃₀ (s : Set (Set X)) →
        ∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj G.val),
        a = 0) →
      Subsingleton (Sheaf.H G n) by
    exact this comps hcomp_irred F (fun x hx => absurd (hcover x) hx)
  intro s; induction s using Finset.induction_on with
  | empty =>
    intro _ G hG
    exact Ext.subsingleton_of_isZero_tgt
      (sheaf_isZero_of_zero_stalks X G (fun x a => hG x (by simp) a)) n
  | @insert Z s' hZ_notin ih =>
    intro hs_irred G hG_stalks
    have hZ_comp := hs_irred Z (Finset.mem_insert_self Z s')
    have hZ_closed := isClosed_of_mem_irreducibleComponents Z hZ_comp
    have hZ_irred := hZ_comp.1
    let S := closedImmersionSES Z hZ_closed G
    have hSE := closedImmersionSES_shortExact Z hZ_closed G
    have hpush : Subsingleton (Sheaf.H S.X₃ n) := by
      apply PushforwardHVanishing Z hZ_closed
      haveI : IrreducibleSpace (TopCat.of Z) :=
        isIrreducible_iff_irreducibleSpace.mp hZ_irred
      exact ih_irred (TopCat.of Z) _
        (topologicalKrullDim_subspace_le (X := (↑X : Type u)) Z)
        (lt_of_le_of_lt (topologicalKrullDim_subspace_le (X := (↑X : Type u)) Z) hn)
    have hker : Subsingleton (Sheaf.H S.X₁ n) := by
      apply ih (fun Z' hZ' => hs_irred Z' (Finset.mem_insert_of_mem hZ')) S.X₁
      intro x hx a
      by_cases hxZ : x ∈ Z
      · -- closedIncl_unit_stalk_isIso: iso on stalks at z ∈ Z
        haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val) :=
          TopCat.closedIncl_unit_stalk_isIso hZ_closed G ⟨x, hxZ⟩
        exact stalk_zero_of_ses_g_iso hSE x inferInstance a
      · have hx' : x ∉ ⋃₀ ((insert Z s' : Finset (Set X)) : Set (Set X)) := by
          simp only [Finset.coe_insert, Set.sUnion_insert, Set.mem_union] at hx ⊢
          push_neg; exact ⟨hxZ, hx⟩
        exact stalk_zero_of_shortExact_kernel hSE x (fun b => hG_stalks x hx' b) a
    exact subsingleton_sheafH_of_shortExact_middle hSE n hker hpush

/-! ## Main theorem -/

theorem grothendieck_vanishing_of_irreducible
    (X : TopCat.{u}) [TopologicalSpace.NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih_irred : ∀ (Y : TopCat.{u}) [TopologicalSpace.NoetherianSpace Y]
      [IrreducibleSpace Y] (m : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      m > topologicalKrullDim Y → Subsingleton (Sheaf.H G m)) :
    Subsingleton (Sheaf.H F n) := by
  by_cases hEmpty : IsEmpty X
  · exact sheafH_subsingleton_of_isEmpty F n
  · rw [not_isEmpty_iff] at hEmpty
    by_cases hIrred : IrreducibleSpace X
    · exact @ih_irred X _ hIrred n F le_rfl hn
    · exact ReducibleVanishing' X n hn F hIrred
        (fun Y [_] [_] G hle hY => ih_irred Y n G hle hY)
