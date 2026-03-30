/-
  IrreducibleStep.lean — Vanishing for irreducible spaces of positive dimension

  Key results:
  - subsingleton_ext_of_ses: PROVED — abstract LES vanishing
  - constantSheaf_flasque_of_irreducible: PROVED (in ConstantSheafFlasque.lean)
  - constantSheaf_cohomology_vanishing: PROVED from flasque + FlasqueVanishing
  - grothendieck_vanishing_irreducible_pos: uses IrreduciblePosVanishing (sorry)
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.ConstantSheafFlasque

universe u

open CategoryTheory TopologicalSpace Abelian

/-- Given a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, if `Ext(Z, X₃, n) = 0`
    and `Ext(Z, X₂, n+1) = 0`, then `Ext(Z, X₁, n+1) = 0`. -/
theorem subsingleton_ext_of_ses {C : Type*} [Category C] [Abelian C] [HasExt C]
    {S : ShortComplex C} (hS : S.ShortExact) (Z : C) (n : ℕ)
    (h₃ : Subsingleton (Ext Z S.X₃ n))
    (h₂ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Subsingleton (Ext Z S.X₁ (n + 1)) := by
  constructor
  intro a b
  have h_a_f : a.comp (Ext.mk₀ S.f) rfl = 0 := Subsingleton.elim _ _
  have h_b_f : b.comp (Ext.mk₀ S.f) rfl = 0 := Subsingleton.elim _ _
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ Z hS a h_a_f rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ Z hS b h_b_f rfl
  rw [← hc, ← hd, Subsingleton.elim c d]

/-- Given a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, if `Ext(Z, X₁, n) = 0`
    and `Ext(Z, X₃, n) = 0`, then `Ext(Z, X₂, n) = 0`.
    This is the "middle term" version of `subsingleton_ext_of_ses`. -/
theorem subsingleton_ext_of_ses_middle {C : Type*} [Category C] [Abelian C] [HasExt C]
    {S : ShortComplex C} (hS : S.ShortExact) (Z : C) (n : ℕ)
    (h₁ : Subsingleton (Ext Z S.X₁ n))
    (h₃ : Subsingleton (Ext Z S.X₃ n)) :
    Subsingleton (Ext Z S.X₂ n) := by
  constructor
  intro a b
  have h₃' : Subsingleton (Ext Z S.X₃ (n + 0)) := (add_zero n) ▸ h₃
  have ha : a.comp (Ext.mk₀ S.g) (add_zero n) = 0 := Subsingleton.elim _ _
  have hb : b.comp (Ext.mk₀ S.g) (add_zero n) = 0 := Subsingleton.elim _ _
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₂ Z hS a ha
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₂ Z hS b hb
  rw [← hc, ← hd, Subsingleton.elim c d]

/-- The constant sheaf on an irreducible space has vanishing higher cohomology. -/
theorem constantSheaf_cohomology_vanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X] (n : ℕ) :
    Subsingleton (Sheaf.H ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))) (n + 1)) :=
  FlasqueVanishing X _ (fun i => constantSheaf_flasque_of_irreducible X i) n

/-- **Step 5** (Hartshorne III.2.7): `zeroOutsideInt V` has vanishing cohomology
    on irreducible X with dim ≥ 1 when n > dim X.
    Uses the SES `0 → zeroOutsideInt V → zeroOutsideInt ⊤ → cokernel → 0`
    where `zeroOutsideInt ⊤ = Z_X` (constant sheaf, flasque on irreducible spaces).
    The cokernel vanishing at degree `m = n-1` is assumed (from IH on the
    closed complement `Vᶜ`). -/
set_option synthInstance.maxHeartbeats 80000 in
theorem zeroOutsideInt_vanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (m : ℕ)
    (hCoker : Subsingleton (Sheaf.H (Limits.cokernel
      (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤))) m)) :
    Subsingleton (Sheaf.H (TopCat.Sheaf.zeroOutsideInt V) (m + 1)) := by
  let f := TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤)
  let S := ShortComplex.mk f (Limits.cokernel.π f) (Limits.cokernel.condition f)
  have hSE : S.ShortExact :=
    ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (Limits.cokernelIsCokernel _))
      inferInstance inferInstance
  exact subsingleton_ext_of_ses hSE _ m hCoker (constantSheaf_cohomology_vanishing X m)

/-- The presheaf stalk map of `zeroOutside_openHom` at `x ∈ V` is surjective:
    any germ in `stalk(constZ, x)` can be lifted by restricting to `W ∩ V ≤ V`
    where the presheaf map is `eqToHom` (identity). -/
private theorem presheaf_stalk_surj {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (TopCat.Presheaf.zeroOutside_openHom (F := TopCat.Presheaf.constZ) (le_top : V ≤ ⊤)))) := by
  intro g
  obtain ⟨W, hxW, s, rfl⟩ := (TopCat.Presheaf.constZ.zeroOutside (⊤ : Opens X)).germ_exist x g
  refine ⟨(TopCat.Presheaf.constZ.zeroOutside V).germ (W ⊓ V) x ⟨hxW, hx⟩
    ((eqToHom (TopCat.Presheaf.zeroOutside_le (F := TopCat.Presheaf.constZ) inf_le_right).symm)
    ((TopCat.Presheaf.constZ.zeroOutside ⊤).map (homOfLE inf_le_left).op s)), ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_left) s ⟨hxW, hx⟩]
  congr 1
  simp [TopCat.Presheaf.zeroOutside_openHom, inf_le_right,
    TopCat.Presheaf.zeroOutside_le, TopCat.Presheaf.zeroOutside]

/-- The sheaf stalk map of `openHom(le_top)` at `x ∈ V` is surjective.
    Transfers presheaf stalk surjectivity via `toSheafify_naturality` and
    the fact that `stalk(toSheafify)` is an isomorphism. -/
set_option synthInstance.maxHeartbeats 200000 in
private theorem sheaf_stalk_surj {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤)).val)) := by
  let J := Opens.grothendieckTopology (T := X)
  let φ := TopCat.Presheaf.zeroOutside_openHom (F := TopCat.Presheaf.constZ) (le_top : V ≤ ⊤)
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hnat : T.map φ ≫ T.map (toSheafify J _) = T.map (toSheafify J _) ≫ T.map (sheafifyMap J φ) := by
    rw [← T.map_comp, ← T.map_comp, toSheafify_naturality]
  haveI : IsIso (T.map (toSheafify J (TopCat.Presheaf.constZ.zeroOutside V))) := inferInstance
  haveI : IsIso (T.map (toSheafify J (TopCat.Presheaf.constZ.zeroOutside ⊤))) := inferInstance
  intro g
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map (toSheafify J _))).2 g
  obtain ⟨p, hp⟩ := presheaf_stalk_surj V x hx q
  exact ⟨ConcreteCategory.hom (T.map (toSheafify J _)) p, by
    simp only [← ConcreteCategory.comp_apply, ← hnat, ConcreteCategory.comp_apply, hp]⟩

/-- The cokernel of `openHom(le_top)` has zero stalks at points of `V`.
    Uses: sheaf stalk surjectivity + section_ext + local surjectivity of `cokernel.π`
    + `cokernel.condition`. -/
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
private theorem cokernel_stalk_zero_V {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (Limits.cokernel (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤))).val) :
    a = 0 := by
  obtain ⟨W, hxW, t, rfl⟩ := (Limits.cokernel _).presheaf.germ_exist x a
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_left) t ⟨hxW, hx⟩]
  suffices h : (Limits.cokernel _).presheaf.map (homOfLE inf_le_left).op t = 0 by
    rw [h]; exact map_zero _
  apply TopCat.Presheaf.section_ext (Limits.cokernel _) (W ⊓ V) _ 0
  intro y hy; simp only [map_zero]
  have hls := (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
    (Limits.cokernel.π _)).mpr (inferInstance : Epi (Limits.cokernel.π _))
  rw [show Sheaf.IsLocallySurjective _ = TopCat.Presheaf.IsLocallySurjective _ from rfl,
    TopCat.Presheaf.isLocallySurjective_iff] at hls
  obtain ⟨W_y, iW_y, ⟨u_y, hu_y⟩, hy_W_y⟩ := hls (W ⊓ V)
    ((Limits.cokernel _).presheaf.map (homOfLE inf_le_left).op t) y hy
  obtain ⟨v_germ, hv⟩ := sheaf_stalk_surj V y hy.2
    ((TopCat.Sheaf.zeroOutsideInt ⊤).presheaf.germ W_y y hy_W_y u_y)
  obtain ⟨W'', hyW'', w, rfl⟩ := (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ_exist y v_germ
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hv
  obtain ⟨W''', hW'''W'', hW'''W_y, hyW''', hfwu⟩ :=
    (TopCat.Sheaf.zeroOutsideInt ⊤).presheaf.germ_eq y hyW'' hy_W_y _ _ hv
  rw [← TopCat.Presheaf.germ_res_apply _ iW_y _ hy_W_y, hu_y,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE hW'''W_y) u_y hyW''',
    TopCat.Presheaf.stalkFunctor_map_germ_apply, ← hfwu,
    show (Limits.cokernel.π _).val.app (op W''')
      ((TopCat.Sheaf.zeroOutsideInt.openHom le_top).val.app (op W''') _) =
      ConcreteCategory.hom (((TopCat.Sheaf.zeroOutsideInt.openHom le_top) ≫
        Limits.cokernel.π _).val.app (op W''')) _ from by
        simp [ConcreteCategory.comp_apply],
    Limits.cokernel.condition]; simp

/-- Cokernel of `openHom(le_top)` has vanishing cohomology on irreducible X.
    The cokernel C has zero stalks on V (since openHom is stalkwise iso there).
    Apply ClosedImmersionSES to C with `Y = Vᶜ`:
    - kernel K has zero stalks everywhere → IsZero → vanishing
    - pushforward from Vᶜ vanishes by IH (dim Vᶜ < dim X)
    - middle-term vanishing gives H^n(C) = 0. -/
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
theorem cokernel_openHom_vanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (hV : V ≠ ⊥)
    (n : ℕ) (hn : n > topologicalKrullDim X) (hpos : topologicalKrullDim X > 0)
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (m : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      m > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G m)) :
    let f := TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤)
    Subsingleton (Sheaf.H (Limits.cokernel f) n) := by
  intro f
  let Y := (V : Set X)ᶜ
  have hYcl : IsClosed Y := V.isOpen.isClosed_compl
  have hY_ne : Y ≠ Set.univ := by
    intro h; apply hV; ext x; simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => (show x ∈ Y from h ▸ Set.mem_univ x) hx
  have hY_dim : topologicalKrullDim (TopCat.of Y) < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl hY_ne
      (lt_of_le_of_lt (topologicalKrullDim_subspace_le X Y)
        (lt_of_lt_of_le (show topologicalKrullDim X < ⊤ from lt_of_lt_of_le hn le_top) le_top))
  have hn_Y : ↑n > topologicalKrullDim (TopCat.of Y) := lt_trans hY_dim hn
  obtain ⟨S', hS'E, hS'₂, hS'₃⟩ := ClosedImmersionSES Y hYcl (Limits.cokernel f)
  -- Kernel K of η_C has zero stalks everywhere → IsZero → vanishing
  -- On Vᶜ: stalk iso from closedIncl_unit_stalk_isIso → kernel stalk = 0
  -- On V: C has zero stalks (openHom stalkwise iso) → K ↪ C has zero stalks
  have hK_zero : IsZero S'.X₁ := by
    apply sheaf_isZero_of_zero_stalks X S'.X₁
    intro x a
    by_cases hx : (x : X) ∈ (V : Set X)
    · -- x ∈ V: cokernel has zero stalks on V.
      -- The presheaf stalk map of openHom at x ∈ V is surjective (restriction to W∩V
      -- where the presheaf map is eqToHom). The sheaf stalk map is surjective by
      -- conjugation via sheafifyStalkIso. Then cokernel stalk = 0 by section_ext +
      -- local surjectivity of cokernel.π + cokernel.condition.
      -- K ↪ C (mono) and C_x = 0, so K_x = 0.
      -- K ↪ cokernel(f) via S'.f (mono). Map a into stalk(cokernel(f), x).
      -- stalk(cokernel(f), x) = 0, so the image of a is 0.
      -- By injectivity of the stalk of S'.f (mono), a = 0.
      let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
      have ha_img : ConcreteCategory.hom (T.map S'.f.val) a = 0 := by
        rw [hS'₂] at *; exact cokernel_stalk_zero_V V x hx _
      haveI : Mono S'.f := hS'E.mono_f
      haveI := TopCat.Presheaf.stalkFunctor_preserves_mono
        (C := AddCommGrpCat.{u}) (X := X) x
      haveI : Mono (T.map S'.f.val) := Functor.map_mono T S'.f.val
      rwa [AddCommGrpCat.mono_iff_injective.mp inferInstance |>.eq_iff] at ha_img
    · -- x ∈ Vᶜ = Y: stalk map of η is iso by closedIncl_unit_stalk_isIso.
      -- kernel stalk at x = 0.
      have hxY : (x : X) ∈ Y := hx
      haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
            (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Y ⟶ X)).unit.app
            (Limits.cokernel f) |>.val) :=
        closedIncl_unit_stalk_isIso hYcl (Limits.cokernel f) ⟨x, hxY⟩
      exact stalk_zero_of_ses_g_iso hS'E x inferInstance a
  have hK_van : Subsingleton (Sheaf.H S'.X₁ n) :=
    subsingleton_sheafH_of_isZero' S'.X₁ hK_zero n
  have hP_van : Subsingleton (Sheaf.H S'.X₃ n) := by
    rw [hS'₃]
    exact PushforwardHVanishing Y hYcl _ n (@ih (TopCat.of Y) _ n _ hY_dim hn_Y)
  exact hS'₂ ▸ subsingleton_sheafH_of_shortExact_middle hS'E n hK_van hP_van

/-! ## Sub-lemmas for Hartshorne III.2.7 Steps 3-5

These lemmas decompose the kernel vanishing argument.
`zeroOutsideInt_cohomology_vanishing` is proved; the other two remain sorry.
-/

/-- **Step 5** (Hartshorne III.2.7): `zeroOutsideInt V` has vanishing cohomology in every
    degree `m > dim X` on an irreducible Noetherian space of positive dimension.
    Proof: write `m = m' + 1`, apply `zeroOutsideInt_vanishing` (SES + flasque), then prove
    cokernel vanishing at `m'` via `ClosedImmersionSES` on `Vᶜ` + `PushforwardHVanishing`. -/
set_option synthInstance.maxHeartbeats 80000 in
theorem zeroOutsideInt_cohomology_vanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (m : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      m > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G m))
    (hpos : topologicalKrullDim X > 0)
    (V : Opens X) (hV : V ≠ ⊥)
    (m : ℕ) (hm : m > topologicalKrullDim X) :
    Subsingleton (Sheaf.H (TopCat.Sheaf.zeroOutsideInt V) m) := by
  have hm0 : m ≠ 0 := by
    intro h; subst h; simp at hm; exact not_lt.mpr bot_le (lt_trans hpos hm)
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  apply zeroOutsideInt_vanishing X V m'
  let Y := (V : Set X)ᶜ
  have hYcl : IsClosed Y := V.isOpen.isClosed_compl
  have hY_ne : Y ≠ Set.univ := by
    intro h; apply hV; ext x; simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => (show x ∈ Y from h ▸ Set.mem_univ x) hx
  have hdim_lt_top : topologicalKrullDim X < ⊤ := lt_of_lt_of_le hm le_top
  have hY_dim : topologicalKrullDim (TopCat.of Y) < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl hY_ne
      (lt_of_le_of_lt (topologicalKrullDim_subspace_le X Y)
        (lt_of_lt_of_le hdim_lt_top le_top))
  have hm'_Y : (m' : WithBot ℕ∞) > topologicalKrullDim (TopCat.of Y) :=
    lt_trans hY_dim (by exact_mod_cast Nat.lt_of_lt_pred (by exact_mod_cast hm))
  let f := TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤)
  obtain ⟨S', hS'E, hS'₂, hS'₃⟩ := ClosedImmersionSES Y hYcl (Limits.cokernel f)
  have hK_zero : IsZero S'.X₁ := by
    apply sheaf_isZero_of_zero_stalks X S'.X₁
    intro x a
    by_cases hx : (x : X) ∈ (V : Set X)
    · let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
      have ha_img : ConcreteCategory.hom (T.map S'.f.val) a = 0 := by
        rw [hS'₂] at *; exact cokernel_stalk_zero_V V x hx _
      haveI : Mono S'.f := hS'E.mono_f
      haveI := TopCat.Presheaf.stalkFunctor_preserves_mono
        (C := AddCommGrpCat.{u}) (X := X) x
      haveI : Mono (T.map S'.f.val) := Functor.map_mono T S'.f.val
      rwa [AddCommGrpCat.mono_iff_injective.mp inferInstance |>.eq_iff] at ha_img
    · have hxY : (x : X) ∈ Y := hx
      haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
            (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Y ⟶ X)).unit.app
            (Limits.cokernel f) |>.val) :=
        closedIncl_unit_stalk_isIso hYcl (Limits.cokernel f) ⟨x, hxY⟩
      exact stalk_zero_of_ses_g_iso hS'E x inferInstance a
  have hK_van : Subsingleton (Sheaf.H S'.X₁ m') :=
    subsingleton_sheafH_of_isZero' S'.X₁ hK_zero m'
  have hP_van : Subsingleton (Sheaf.H S'.X₃ m') := by
    rw [hS'₃]
    exact PushforwardHVanishing Y hYcl _ m' (@ih (TopCat.of Y) _ m' _ hY_dim hm'_Y)
  exact hS'₂ ▸ subsingleton_sheafH_of_shortExact_middle hS'E m' hK_van hP_van

/-- Third-term LES: for 0 → X₁ → X₂ → X₃ → 0, H^n(X₂)=0 ∧ H^{n+1}(X₁)=0 ⟹ H^n(X₃)=0. -/
theorem subsingleton_ext_of_ses_third {C : Type*} [Category C] [Abelian C] [HasExt C]
    {S : ShortComplex C} (hS : S.ShortExact) (Z : C) (n : ℕ)
    (h₂ : Subsingleton (Ext Z S.X₂ n))
    (h₁ : Subsingleton (Ext Z S.X₁ (n + 1))) :
    Subsingleton (Ext Z S.X₃ n) := by
  constructor; intro a b
  have ha_δ : a.comp hS.extClass rfl = 0 := @Subsingleton.elim _ h₁ _ _
  have hb_δ : b.comp hS.extClass rfl = 0 := @Subsingleton.elim _ h₁ _ _
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₃ Z hS a rfl ha_δ
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₃ Z hS b rfl hb_δ
  rw [← hc, ← hd, @Subsingleton.elim _ h₂ c d]

theorem subsingleton_sheafH_of_shortExact_third {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₂ : Subsingleton (Sheaf.H S.X₂ n))
    (h₁ : Subsingleton (Sheaf.H S.X₁ (n + 1))) :
    Subsingleton (Sheaf.H S.X₃ n) :=
  subsingleton_ext_of_ses_third hS _ n h₂ h₁

/-- `zeroOutsideInt ⊥` is the zero sheaf (all stalks vanish). -/
theorem isZero_zeroOutsideInt_bot (X : TopCat.{u}) :
    IsZero (TopCat.Sheaf.zeroOutsideInt (⊥ : Opens X)) := by
  sorry

/-- **Step 4** (Hartshorne III.2.7): any subsheaf of `zeroOutsideInt V` has vanishing
    cohomology in degree `m > dim X`. Uses the structure of subsheaves of `Z_V`:
    stalks are `d_x·ℤ ⊆ ℤ`, and after shrinking to an open `V' ⊆ V`, the subsheaf
    restricts to `d·Z_{V'}` ≅ `Z_{V'}`. The quotient is supported on a smaller closed set. -/
theorem subsheaf_zeroOutsideInt_vanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (m : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      m > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G m))
    (hpos : topologicalKrullDim X > 0)
    (V : Opens X) (R : TopCat.Sheaf AddCommGrpCat.{u} X)
    (i : R ⟶ TopCat.Sheaf.zeroOutsideInt V) [Mono i]
    (m : ℕ) (hm : m > topologicalKrullDim X) :
    Subsingleton (Sheaf.H R m) := by
  sorry

/-- **Steps 3C + 4 + LES** (Hartshorne III.2.7): any epi image of `zeroOutsideInt V` has
    vanishing cohomology in degree `m > dim X`. Uses third-term LES with
    `zeroOutsideInt_cohomology_vanishing` (Step 5) and
    `subsheaf_zeroOutsideInt_vanishing` (Step 4). -/
set_option synthInstance.maxHeartbeats 80000 in
theorem epiImage_zeroOutsideInt_vanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (m : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      m > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G m))
    (hpos : topologicalKrullDim X > 0)
    (V : Opens X) {G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : TopCat.Sheaf.zeroOutsideInt V ⟶ G) (hf : Epi f)
    (m : ℕ) (hm : m > topologicalKrullDim X) :
    Subsingleton (Sheaf.H G m) := by
  by_cases hV : V = ⊥
  · subst hV
    have hZero : IsZero G := by
      rw [IsZero.iff_id_eq_zero]
      exact (cancel_epi f).mp (by simp [(isZero_zeroOutsideInt_bot X).eq_of_src f 0])
    exact subsingleton_sheafH_of_isZero' G hZero m
  · let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have hSE : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f)) inferInstance inferInstance
    have hZV : Subsingleton (Sheaf.H S.X₂ m) :=
      zeroOutsideInt_cohomology_vanishing X ih hpos V hV m hm
    have hKer : Subsingleton (Sheaf.H S.X₁ (m + 1)) :=
      subsheaf_zeroOutsideInt_vanishing X ih hpos V (kernel f) (kernel.ι f) (m + 1)
        (lt_trans hm (by exact_mod_cast Nat.lt_succ_of_le le_rfl))
    exact subsingleton_sheafH_of_shortExact_third hSE m hZV hKer

/-- **Step 3A** (Hartshorne III.2.7): on a Noetherian space, if vanishing holds for
    all epi images of `zeroOutsideInt V`, then it holds for every sheaf. -/
theorem directLimit_cohomology_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    (K : TopCat.Sheaf AddCommGrpCat.{u} X) (m : ℕ)
    (hzero : ∀ {G : TopCat.Sheaf AddCommGrpCat.{u} X} {V : Opens X}
      (f : TopCat.Sheaf.zeroOutsideInt V ⟶ G), Epi f → Subsingleton (Sheaf.H G m)) :
    Subsingleton (Sheaf.H K m) := by
  sorry

/-- Kernel vanishing via assembly of Steps 3-5. -/
theorem irreduciblePos_kernel_subsingleton
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X) (hpos : topologicalKrullDim X > 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (m : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      m > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G m))
    (Z : Set X) (hZ_closed : IsClosed Z) (hZ_ne_univ : Z ≠ Set.univ)
    (hZ_dim : topologicalKrullDim (TopCat.of Z) < topologicalKrullDim X)
    (hn_Z : ↑n > topologicalKrullDim (TopCat.of Z))
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (hSE : S.ShortExact) (hS₂ : S.X₂ = F)
    (hS₃ : S.X₃ = (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).obj F)) :
    Subsingleton (Sheaf.H S.X₁ n) :=
  directLimit_cohomology_vanishing S.X₁ n
    (fun f hf => epiImage_zeroOutsideInt_vanishing X ih hpos _ f hf n hn)

set_option synthInstance.maxHeartbeats 80000 in
/-- **Irreducible positive-dimension vanishing** (Hartshorne III.2.7, irreducible case). -/
theorem IrreduciblePosVanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X) (hpos : topologicalKrullDim X > 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (m : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      m > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G m)) :
    Subsingleton (Sheaf.H F n) := by
  obtain ⟨Z, hZ_closed, hZ_ne_univ, hZ_dim, hn_Z⟩ :=
    exists_closed_subset_lt_dim_of_irreducible_pos X n hn hpos
  obtain ⟨S, hSE, hS₂, hS₃⟩ := ClosedImmersionSES Z hZ_closed F
  have hPush : Subsingleton (Sheaf.H S.X₃ n) :=
    irreduciblePos_pushforward_subsingleton X n F ih Z hZ_closed hZ_dim hn_Z S hS₃
  have hKer : Subsingleton (Sheaf.H S.X₁ n) :=
    irreduciblePos_kernel_subsingleton X n hn hpos F ih Z hZ_closed hZ_ne_univ hZ_dim hn_Z
      S hSE hS₂ hS₃
  rw [← hS₂]
  exact subsingleton_sheafH_of_shortExact_middle hSE n hKer hPush

/-- Hartshorne Steps 3-5: delegates to IrreduciblePosVanishing. -/
private theorem grothendieck_reduction
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X) (hpos : topologicalKrullDim X > 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (m : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      m > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G m)) :
    Subsingleton (Sheaf.H F n) :=
  IrreduciblePosVanishing X n hn hpos F ih

/-- Positive-dimensional irreducible vanishing. -/
theorem grothendieck_vanishing_irreducible_pos
    (X : TopCat.{u}) [TopologicalSpace.NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (hpos : topologicalKrullDim X > 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih : ∀ (Y : TopCat.{u}) [TopologicalSpace.NoetherianSpace Y]
      (m : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      m > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G m)) :
    Subsingleton (Sheaf.H F n) :=
  grothendieck_reduction X n hn hpos F ih
