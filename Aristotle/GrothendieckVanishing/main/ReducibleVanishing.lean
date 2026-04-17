/-
  ReducibleVanishing.lean -- Proof of ReducibleVanishing

  Proves ReducibleVanishing' (re-exported by Setup.lean as ReducibleVanishing)
  by iterating ClosedImmersionSES over the finitely many irreducible components.
-/
import Aristotle.GrothendieckVanishing.main.SetupCore

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-! ## Helper lemmas -/

/-! ## Main proof -/

theorem ReducibleVanishing'
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
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app G
    haveI : Epi η := epi_unit_of_closedImmersion Z hZ_closed G
    let S := ShortComplex.mk (kernel.ι η) η (kernel.condition η)
    have hSE : S.ShortExact := shortExact_of_epi η
    have hpush : Subsingleton (Sheaf.H S.X₃ n) := by
      show Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj G)) n)
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
