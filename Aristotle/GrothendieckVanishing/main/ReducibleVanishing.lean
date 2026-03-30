/-
  ReducibleVanishing.lean -- Proof of ReducibleVanishing

  Fills in the sorry in Setup.lean for ReducibleVanishing by iterating
  ClosedImmersionSES over the finitely many irreducible components.
-/
import Aristotle.GrothendieckVanishing.main.SetupCore

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-! ## Helper lemmas -/

theorem sheaf_isZero_of_zero_stalks (X : TopCat.{u})
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hstalk : ∀ (x : X)
      (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F.val), a = 0) :
    IsZero F := by
  have val_sub : ∀ (U : Opens X), Subsingleton (F.val.obj (op U)) := by
    intro U; constructor; intro s t
    apply TopCat.Presheaf.section_ext F U s t
    intro x hx; exact (hstalk x _).trans (hstalk x _).symm
  have val_isZero : ∀ (U : (Opens X)ᵒᵖ), IsZero (F.val.obj U) := by
    intro ⟨U⟩; exact @AddCommGrpCat.isZero_of_subsingleton _ (val_sub U)
  apply IsZero.mk
  · intro G; exact ⟨{
      default := 0
      uniq := fun f => by
        apply Sheaf.Hom.ext; apply NatTrans.ext; funext U
        exact (val_isZero U).eq_zero_of_src (f.val.app U) }⟩
  · intro G; exact ⟨{
      default := 0
      uniq := fun f => by
        apply Sheaf.Hom.ext; apply NatTrans.ext; funext U
        exact (val_isZero U).eq_zero_of_tgt (f.val.app U) }⟩

theorem subsingleton_sheafH_of_isZero' {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : IsZero F) (n : ℕ) :
    Subsingleton (Sheaf.H F n) := by
  constructor; intro a b
  have hid : (𝟙 F : F ⟶ F) = 0 := hF.eq_of_src _ _
  calc a = a.comp (Ext.mk₀ (𝟙 F)) (add_zero n) := (Ext.comp_mk₀_id a).symm
    _ = a.comp 0 (add_zero n) := by rw [hid, Ext.mk₀_zero]
    _ = 0 := Ext.comp_zero a F 0 n (add_zero n)
    _ = b.comp 0 (add_zero n) := (Ext.comp_zero b F 0 n (add_zero n)).symm
    _ = b.comp (Ext.mk₀ (𝟙 F)) (add_zero n) := by rw [hid, Ext.mk₀_zero]
    _ = b := Ext.comp_mk₀_id b

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 400000 in
theorem stalk_zero_of_ses_g_iso
    {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hSE : S.ShortExact) (x : X)
    (hiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₁.val) :
    a = 0 := by
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hcomp_elem : ConcreteCategory.hom (T.map S.g.val)
      (ConcreteCategory.hom (T.map S.f.val) a) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← T.map_comp]
    obtain ⟨U, hxU, s, rfl⟩ := S.X₁.presheaf.germ_exist x a
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change ConcreteCategory.hom (S.X₃.presheaf.germ U x hxU)
      (ConcreteCategory.hom ((S.f.val ≫ S.g.val).app (op U)) s) = 0
    have : ConcreteCategory.hom ((S.f.val ≫ S.g.val).app (op U)) s = 0 := by
      change ConcreteCategory.hom ((S.f ≫ S.g).val.app (op U)) s = 0
      rw [S.zero]; exact AddMonoidHom.zero_apply s
    rw [this]; exact map_zero _
  have hfa_zero : ConcreteCategory.hom (T.map S.f.val) a = 0 :=
    (ConcreteCategory.bijective_of_isIso (T.map S.g.val)).1
      (hcomp_elem.trans (map_zero _).symm)
  haveI : Mono S.f := hSE.mono_f
  haveI := TopCat.Presheaf.stalkFunctor_preserves_mono
    (C := AddCommGrpCat.{u}) (X := X) x
  haveI : Mono ((TopCat.Sheaf.forget _ _ ⋙ T).map S.f) :=
    Functor.map_mono (TopCat.Sheaf.forget _ _ ⋙ T) S.f
  rw [AddCommGrpCat.mono_iff_injective] at this
  exact this (hfa_zero.trans (map_zero _).symm)

/-! ## Main proof -/

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 160000 in
theorem ReducibleVanishing'
    (X : TopCat.{u}) [NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hNotIrred : ¬ IrreducibleSpace X) [Nonempty X]
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
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ G hG
    exact subsingleton_sheafH_of_isZero' G
      (sheaf_isZero_of_zero_stalks X G (fun x a => hG x (by simp) a)) n
  | @insert Z s' hZ_notin ih =>
    intro hs_irred G hG_stalks
    have hZ_comp := hs_irred Z (Finset.mem_insert_self Z s')
    have hZ_closed := isClosed_of_mem_irreducibleComponents Z hZ_comp
    have hZ_irred := hZ_comp.1
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i
    let η := adj.unit.app G
    haveI : Epi η := epi_unit_of_closedImmersion Z hZ_closed G
    let S := ShortComplex.mk (kernel.ι η) η (kernel.condition η)
    have hSE : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel η)) inferInstance inferInstance
    have hX₂ : S.X₂ = G := rfl
    have hX₃ : S.X₃ = (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj G) := rfl
    have hpush : Subsingleton (Sheaf.H S.X₃ n) := by
      rw [hX₃]
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
        haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val) := by
          dsimp [S, η]
          exact TopCat.closedIncl_unit_stalk_isIso hZ_closed G ⟨x, hxZ⟩
        exact stalk_zero_of_ses_g_iso hSE x inferInstance a
      · have hx' : x ∉ ⋃₀ ((insert Z s' : Finset (Set X)) : Set (Set X)) := by
          simp only [Finset.coe_insert, Set.sUnion_insert, Set.mem_union] at hx ⊢
          push_neg; exact ⟨hxZ, hx⟩
        have hX₂_stalk :
            ∀ (b : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₂.val),
            b = 0 := fun b => hG_stalks x hx' b
        let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
        haveI : Mono S.f := hSE.mono_f
        haveI := TopCat.Presheaf.stalkFunctor_preserves_mono
          (C := AddCommGrpCat.{u}) (X := X) x
        haveI : Mono ((TopCat.Sheaf.forget _ _ ⋙ T).map S.f) :=
          Functor.map_mono (TopCat.Sheaf.forget _ _ ⋙ T) S.f
        rw [AddCommGrpCat.mono_iff_injective] at this
        exact this ((hX₂_stalk _).trans (map_zero _).symm)
    exact hX₂ ▸ subsingleton_sheafH_of_shortExact_middle hSE n hker hpush
