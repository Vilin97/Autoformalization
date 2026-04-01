/-
  IrreducibleStep.lean — Vanishing for irreducible spaces of positive dimension

  Key results:
  - subsingleton_ext_of_ses: PROVED — abstract LES vanishing
  - constantSheaf_flasque_of_irreducible: PROVED (in ConstantSheafFlasque.lean)
  - constantSheaf_cohomology_vanishing: PROVED from flasque + FlasqueVanishing
  - grothendieck_vanishing_irreducible_pos: uses IrreduciblePosVanishing
    2 sorry's: exists_good_section, cohomology_vanishing_of_finitelyGenerated_vanishing
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.ConstantSheafFlasque

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

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

/-- The presheaf stalk map of `zeroOutside_openHom h` at `x ∈ V` is surjective:
    any germ in the larger zero-outside presheaf can be lifted by restricting to `W ∩ V ≤ V`
    where the presheaf map is `eqToHom` (identity). -/
private theorem presheaf_stalk_surj_openHom
    {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) (x : X) (hx : x ∈ V) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (TopCat.Presheaf.zeroOutside_openHom (F := TopCat.Presheaf.constZ) h))) := by
  intro g
  obtain ⟨W, hxW, s, rfl⟩ := (TopCat.Presheaf.constZ.zeroOutside U).germ_exist x g
  refine ⟨(TopCat.Presheaf.constZ.zeroOutside V).germ (W ⊓ V) x ⟨hxW, hx⟩
    ((eqToHom (TopCat.Presheaf.zeroOutside_le (F := TopCat.Presheaf.constZ) inf_le_right).symm)
    ((TopCat.Presheaf.constZ.zeroOutside U).map (homOfLE inf_le_left).op s)), ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_left) s ⟨hxW, hx⟩]
  congr 1
  simp [TopCat.Presheaf.zeroOutside_openHom, h, inf_le_right,
    TopCat.Presheaf.zeroOutside_le, TopCat.Presheaf.zeroOutside]

/-- The presheaf stalk map of `zeroOutside_openHom(le_top)` at `x ∈ V` is surjective. -/
private theorem presheaf_stalk_surj {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (TopCat.Presheaf.zeroOutside_openHom (F := TopCat.Presheaf.constZ) (le_top : V ≤ ⊤)))) :=
  presheaf_stalk_surj_openHom (le_top : V ≤ ⊤) x hx

/-- The sheaf stalk map of `openHom(le_top)` at `x ∈ V` is surjective.
    Transfers presheaf stalk surjectivity via `toSheafify_naturality` and
    the fact that `stalk(toSheafify)` is an isomorphism. -/
private theorem sheaf_stalk_surj_openHom
    {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) (x : X) (hx : x ∈ V) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (TopCat.Sheaf.zeroOutsideInt.openHom h).val)) := by
  let J := Opens.grothendieckTopology (T := X)
  let φ := TopCat.Presheaf.zeroOutside_openHom (F := TopCat.Presheaf.constZ) h
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hnat : T.map φ ≫ T.map (toSheafify J _) = T.map (toSheafify J _) ≫ T.map (sheafifyMap J φ) := by
    rw [← T.map_comp, ← T.map_comp, toSheafify_naturality]
  haveI : IsIso (T.map (toSheafify J (TopCat.Presheaf.constZ.zeroOutside V))) := inferInstance
  haveI : IsIso (T.map (toSheafify J (TopCat.Presheaf.constZ.zeroOutside U))) := inferInstance
  intro g
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map (toSheafify J _))).2 g
  obtain ⟨p, hp⟩ := presheaf_stalk_surj_openHom h x hx q
  exact ⟨ConcreteCategory.hom (T.map (toSheafify J _)) p, by
    simp only [← ConcreteCategory.comp_apply, ← hnat, ConcreteCategory.comp_apply, hp]⟩

/-- The sheaf stalk map of `openHom(le_top)` at `x ∈ V` is surjective. -/
private theorem sheaf_stalk_surj {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤)).val)) :=
  sheaf_stalk_surj_openHom (le_top : V ≤ ⊤) x hx

/-- On points of the smaller open, `zeroOutsideInt.openHom h` induces a stalk bijection. -/
private theorem sheaf_stalk_bijective_openHom
    {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) (x : X) (hx : x ∈ V) :
    Function.Bijective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (TopCat.Sheaf.zeroOutsideInt.openHom h).val)) := by
  refine ⟨?_, sheaf_stalk_surj_openHom h x hx⟩
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI := TopCat.Presheaf.stalkFunctor_preserves_mono
    (C := AddCommGrpCat.{u}) (X := X) x
  haveI : Mono (T.map (TopCat.Sheaf.zeroOutsideInt.openHom h).val) :=
    Functor.map_mono T (TopCat.Sheaf.zeroOutsideInt.openHom h).val
  exact AddCommGrpCat.mono_iff_injective.mp inferInstance

/-- The cokernel of `openHom(le_top)` has zero stalks at points of `V`.
    Uses: sheaf stalk surjectivity + section_ext + local surjectivity of `cokernel.π`
    + `cokernel.condition`. -/
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
  constructor
  intro a b
  have h_a_δ : a.comp hS.extClass rfl = 0 := Subsingleton.elim _ _
  have h_b_δ : b.comp hS.extClass rfl = 0 := Subsingleton.elim _ _
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₃ Z hS a rfl h_a_δ
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₃ Z hS b rfl h_b_δ
  rw [← hc, ← hd, Subsingleton.elim c d]

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
  apply sheaf_isZero_of_zero_stalks X; intro x a
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI : IsIso (T.map (toSheafify (Opens.grothendieckTopology X)
    (TopCat.Presheaf.constZ.zeroOutside (⊥ : Opens X)))) := inferInstance
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (T.map (toSheafify _ (TopCat.Presheaf.constZ.zeroOutside ⊥)))).2 a
  obtain ⟨W, hxW, s, rfl⟩ := (TopCat.Presheaf.constZ.zeroOutside (⊥ : Opens X)).germ_exist x q
  have hW : ¬ (W ≤ ⊥) := fun h => (Opens.mem_bot.mp (h hxW))
  have hs : s = 0 := @IsZero.eq_zero_of_src _ _ _ (by
    rw [show (TopCat.Presheaf.constZ.zeroOutside (⊥ : Opens X)).obj (op W) =
      (if W ≤ ⊥ then TopCat.Presheaf.constZ.obj (op W) else 0) from by
        simp [TopCat.Presheaf.zeroOutside]]
    rw [if_neg hW]; exact isZero_zero _) s
  simp [hs, map_zero]

/-- Stalks of `zeroOutsideInt V` vanish outside `V`. -/
theorem stalk_zeroOutsideInt_zero_outside
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∉ V)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (TopCat.Sheaf.zeroOutsideInt V).val) : a = 0 := by
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI : IsIso (T.map (toSheafify (Opens.grothendieckTopology X)
    (TopCat.Presheaf.constZ.zeroOutside V))) := inferInstance
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (T.map (toSheafify _ (TopCat.Presheaf.constZ.zeroOutside V)))).2 a
  obtain ⟨W, hxW, s, rfl⟩ := (TopCat.Presheaf.constZ.zeroOutside V).germ_exist x q
  have hW : ¬ (W ≤ V) := fun h => hx (h hxW)
  have hs : s = 0 := @IsZero.eq_zero_of_src _ _ _ (by
    rw [show (TopCat.Presheaf.constZ.zeroOutside V).obj (op W) =
      (if W ≤ V then TopCat.Presheaf.constZ.obj (op W) else 0) from by
        simp [TopCat.Presheaf.zeroOutside]]
    rw [if_neg hW]; exact isZero_zero _) s
  simp [hs, map_zero]

/-- A nonzero subsheaf of `zeroOutsideInt V` has a nonzero stalk at some point of `V`. -/
theorem exists_nonzero_stalk_in_V
    {X : TopCat.{u}} (V : Opens X)
    (R : TopCat.Sheaf AddCommGrpCat.{u} X)
    (i : R ⟶ TopCat.Sheaf.zeroOutsideInt V) [Mono i]
    (hR : ¬ IsZero R) :
    ∃ (x : X) (_ : x ∈ V)
      (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj R.val),
      a ≠ 0 := by
  by_contra h; push_neg at h; apply hR
  apply sheaf_isZero_of_zero_stalks; intro x a
  by_cases hx : (x : X) ∈ (V : Set X)
  · exact h x hx a
  · let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    have h_img : ConcreteCategory.hom (T.map i.val) a = 0 :=
      stalk_zeroOutsideInt_zero_outside V x hx _
    haveI := TopCat.Presheaf.stalkFunctor_preserves_mono (C := AddCommGrpCat.{u}) (X := X) x
    haveI : Mono (T.map i.val) := Functor.map_mono T i.val
    rwa [AddCommGrpCat.mono_iff_injective.mp inferInstance |>.eq_iff] at h_img

/-- A sheaf morphism is mono if all its stalk maps are injective. -/
theorem sheaf_mono_of_stalk_injective
    {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (h : ∀ x : X, Function.Injective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.val))) :
    Mono f := by
  have : ∀ x, Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.val) := by
    intro x
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr (h x)
  exact TopCat.Presheaf.mono_of_stalk_mono f

/-- Every additive subgroup of `ℤ` is of the form `nℤ`. -/
private theorem int_addSubgroup_eq_zmultiples (H : AddSubgroup ℤ) :
    ∃ n : ℤ, H = AddSubgroup.zmultiples n := by
  obtain ⟨n, hn⟩ := Int.subgroup_cyclic H
  refine ⟨n, ?_⟩
  simpa [AddSubgroup.zmultiples_eq_closure] using hn

/-- At a point inside the support open, every stalk element of the presheaf `constZ.zeroOutside V`
    is an integer multiple of the germ of the distinguished generator over `V`. -/
private theorem presheaf_stalk_zeroOutside_eq_zsmul_generator
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (TopCat.Presheaf.constZ.zeroOutside V)) :
    ∃ n : ℤ,
      a = n • ((TopCat.Presheaf.constZ.zeroOutside V).germ V x hx
        (TopCat.Presheaf.zeroOutside.generator V)) := by
  obtain ⟨W, hxW, s, rfl⟩ := (TopCat.Presheaf.constZ.zeroOutside V).germ_exist x a
  by_cases hWV : W ≤ V
  · have hObjW : (TopCat.Presheaf.constZ.zeroOutside V).obj (op W) =
        AddCommGrpCat.of (ULift ℤ) := by
      simp [TopCat.Presheaf.zeroOutside, hWV, TopCat.Presheaf.constZ]
    let z : ULift ℤ := (AddCommGrpCat.Hom.hom (eqToHom hObjW)) s
    have hgenW :
        Presheaf.restrictOpen (F := TopCat.Presheaf.constZ.zeroOutside V)
            (TopCat.Presheaf.zeroOutside.generator V) W hWV =
          (eqToHom hObjW.symm : AddCommGrpCat.of (ULift ℤ) ⟶
            (TopCat.Presheaf.constZ.zeroOutside V).obj (op W)) (1 : ULift ℤ) := by
      simpa [TopCat.Presheaf.zeroOutside_openHom, TopCat.Presheaf.zeroOutside,
        TopCat.Presheaf.constZ, TopCat.Presheaf.zeroOutside.generator, hWV, hObjW] using
        (TopCat.Presheaf.zeroOutside.openHom_generator (U := V) (V := W) hWV).symm
    have hs :
        s = (z.down : ℤ) • Presheaf.restrictOpen (F := TopCat.Presheaf.constZ.zeroOutside V)
          (TopCat.Presheaf.zeroOutside.generator V) W hWV := by
      calc
        s = (AddCommGrpCat.Hom.hom (eqToHom hObjW.symm)) z := by
          simpa [z] using
            (TopCat.Presheaf.zeroOutside.hom_eqToHom_symm_hom_eqToHom (e := hObjW) s).symm
        _ = (z.down : ℤ) • (AddCommGrpCat.Hom.hom (eqToHom hObjW.symm)) (1 : ULift ℤ) := by
          have hz : z = (z.down : ℤ) • (1 : ULift ℤ) := by
            ext
            simp [z]
          rw [hz]
          simpa using
            (map_zsmul (AddCommGrpCat.Hom.hom (eqToHom hObjW.symm)) z.down (1 : ULift ℤ))
        _ = (z.down : ℤ) • Presheaf.restrictOpen (F := TopCat.Presheaf.constZ.zeroOutside V)
              (TopCat.Presheaf.zeroOutside.generator V) W hWV := by
          rw [hgenW]
    refine ⟨z.down, ?_⟩
    rw [hs]
    simp only [map_zsmul]
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hWV)
      (TopCat.Presheaf.zeroOutside.generator V) hxW]
  · have hs : s = 0 := by
      exact @IsZero.eq_zero_of_src _ _ _ (TopCat.Presheaf.zeroOutside_isZero
        (F := TopCat.Presheaf.constZ) hWV) s
    refine ⟨0, ?_⟩
    simp [hs]

/-- At a point inside the support open, every stalk element of `zeroOutsideInt V` is an integer
    multiple of the germ of the distinguished generator over `V`. -/
private theorem stalk_zeroOutsideInt_eq_zsmul_generator
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (TopCat.Sheaf.zeroOutsideInt V).val) :
    ∃ n : ℤ,
      a = n • ((TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V x hx
        (TopCat.Sheaf.zeroOutsideInt.generator V)) := by
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI : IsIso (T.map (toSheafify (Opens.grothendieckTopology X)
    (TopCat.Presheaf.constZ.zeroOutside V))) := inferInstance
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (T.map (toSheafify (Opens.grothendieckTopology X)
      (TopCat.Presheaf.constZ.zeroOutside V)))).2 a
  obtain ⟨n, hn⟩ := presheaf_stalk_zeroOutside_eq_zsmul_generator V x hx q
  refine ⟨n, ?_⟩
  rw [hn]
  simp only [map_zsmul]
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

/-- Every nonzero subgroup of `ULift ℤ` is generated by its smallest positive element.
    Proved by Aristotle (job 5bca8de6). -/
private theorem ulift_int_subgroup_cyclic
    (H : AddSubgroup (ULift.{u} ℤ)) (hH : H ≠ ⊥) :
    ∃ d : ULift.{u} ℤ, d ∈ H ∧ d.down > 0 ∧
      ∀ h ∈ H, ∃ k : ℤ, h = ⟨k * d.down⟩ := by
  obtain ⟨d, hd_pos, hd_gen⟩ : ∃ d ∈ H, 0 < d.down ∧ ∀ h ∈ H, h.down % d.down = 0 := by
    obtain ⟨d, hd_pos, hd_gen⟩ : ∃ d ∈ H, 0 < d.down := by
      contrapose! hH; simp_all +decide [AddSubgroup.eq_bot_iff_forall]
      exact fun x hx => by
        simpa [ULift.ext_iff] using
          le_antisymm (hH x hx) (neg_nonpos.mp (hH (-x) (H.neg_mem hx)))
    obtain ⟨d, hd_pos, hd_gen⟩ :
        ∃ d ∈ H, 0 < d.down ∧ ∀ e ∈ H, 0 < e.down → d.down ≤ e.down := by
      have h_min :
          ∃ m ∈ Set.image (fun e : ULift ℤ => e.down) (H ∩ {e : ULift ℤ | 0 < e.down}),
            ∀ n ∈ Set.image (fun e : ULift ℤ => e.down) (H ∩ {e : ULift ℤ | 0 < e.down}),
              m ≤ n := by
        apply_rules [Int.exists_least_of_bdd]
        · exact ⟨0, fun z hz => by obtain ⟨e, he, rfl⟩ := hz; exact le_of_lt he.2⟩
        · exact ⟨_, ⟨d, ⟨hd_pos, hd_gen⟩, rfl⟩⟩
      aesop
    refine' ⟨d, hd_pos, hd_gen.1, fun h hh => _⟩
    contrapose! hd_gen
    intro hd_pos'
    refine' ⟨h - ⌊h.down / d.down⌋ • d, _, _, _⟩ <;> simp_all +decide [Int.emod_def]
    · convert H.sub_mem hh (H.zsmul_mem hd_pos (h.down / d.down)) using 1
    · cases lt_or_gt_of_ne hd_gen <;>
        linarith [Int.mul_ediv_add_emod h.down d.down,
          Int.emod_nonneg h.down hd_pos'.ne', Int.emod_lt_of_pos h.down hd_pos']
    · linarith [Int.mul_ediv_add_emod h.down d.down,
        Int.emod_lt_of_pos h.down hd_pos']
  exact ⟨d, hd_pos, hd_gen.1, fun h hh =>
    ⟨h.down / d.down, by
      ext; simp +decide [Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero (hd_gen.2 h hh))]⟩⟩

/-- If `i : A →+ ULift ℤ` is injective, `j : ULift ℤ →+ A`, `i ∘ j` is multiplication by
    `c ≠ 0`, and `range(i) = c·ℤ`, then `j` is bijective.
    Proved by Aristotle (job 68d0f4f8). -/
private theorem zmul_bijective_of_index_match
    {A : Type u} [AddCommGroup A]
    (i : A →+ ULift.{u} ℤ) (hi : Function.Injective i)
    (j : ULift.{u} ℤ →+ A)
    (c : ℤ) (hc : c ≠ 0)
    (hcomp : ∀ n : ULift.{u} ℤ, i (j n) = ⟨c * n.down⟩)
    (himg : ∀ z : ULift.{u} ℤ, z ∈ Set.range i ↔ ∃ k : ℤ, z = ⟨c * k⟩) :
    Function.Bijective j := by
  refine' ⟨_, _⟩
  · intro n m hnm; have := hcomp n; aesop
  · intro a; specialize himg (i a); aesop

/-- Core construction for Step 4: find V' ≤ V, V' ≠ ⊥, and a section s ∈ R(V') such that
    `sHom s : zeroOutsideInt V' ⟶ R` is a stalk-isomorphism on V'.
    Uses: minimum-index point, generator section, locally constant germ shrinking. -/
theorem exists_good_section
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (R : TopCat.Sheaf AddCommGrpCat.{u} X)
    (i : R ⟶ TopCat.Sheaf.zeroOutsideInt V) [Mono i]
    (hR : ¬ IsZero R) :
    ∃ (V' : Opens X) (_ : V' ≤ V) (_ : V' ≠ ⊥)
      (s : R.val.obj (op V')),
      ∀ (x : X) (hx : x ∈ V'),
        Function.Bijective (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (TopCat.Sheaf.zeroOutsideInt.sHom s).val)) := by
  -- Step 1: Find a point x₀ ∈ V with nonzero stalk in R
  obtain ⟨x₀, hx₀V, a₀, ha₀⟩ := exists_nonzero_stalk_in_V V R i hR
  -- Step 2: The image of stalk(R, x₀) in stalk(zeroOutsideInt V, x₀) ≅ ULift ℤ
  -- is a nonzero subgroup d₀·ℤ. By ulift_int_subgroup_cyclic, find the generator d₀.
  -- Step 3: Lift the d₀-generator of stalk(R, x₀) to a section s ∈ R(V') for some V' ≤ V.
  -- Step 4: Shrink V' so that sHom s is a stalk-iso on all of V'.
  -- Uses: Noetherian space (ascending chain on opens where stalk map is bijective),
  -- irreducible (the open where bijective holds is dense, hence nonempty).
  -- Key helper: zmul_bijective_of_index_match provides bijectivity once we verify
  -- the index conditions at each point of V'.
  sorry

/-- **Structure lemma** (Hartshorne Step 4 core): a nonzero subsheaf of `zeroOutsideInt V`
    contains `zeroOutsideInt V'` for some nonempty open `V' ⊆ V`, with the inclusion
    being a stalk-isomorphism on `V'`. This follows from: stalks of `Z_V` are `ℤ` or `0`,
    stalks of `R` are `d_x·ℤ ⊆ ℤ`, and after shrinking to an open where the multiplicity
    `d_x` is constant and minimal, `R` restricts to `d·Z_{V'}` ≅ `Z_{V'}`. -/
theorem subsheaf_contains_zeroOutsideInt
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (R : TopCat.Sheaf AddCommGrpCat.{u} X)
    (i : R ⟶ TopCat.Sheaf.zeroOutsideInt V) [Mono i]
    (hR : ¬ IsZero R) :
    ∃ (V' : Opens X) (_ : V' ≤ V) (_ : V' ≠ ⊥)
      (j : TopCat.Sheaf.zeroOutsideInt V' ⟶ R), Mono j ∧
      (∀ (x : X) (hx : x ∈ V'),
        Function.Bijective (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map j.val))) := by
  obtain ⟨V', hle, hne, s, hbij⟩ := exists_good_section V R i hR
  refine ⟨V', hle, hne, TopCat.Sheaf.zeroOutsideInt.sHom s, ?_, hbij⟩
  apply sheaf_mono_of_stalk_injective
  intro y
  by_cases hy : y ∈ V'
  · exact (hbij y hy).1
  · intro a b _
    have ha := stalk_zeroOutsideInt_zero_outside V' y hy a
    have hb := stalk_zeroOutsideInt_zero_outside V' y hy b
    rw [ha, hb]

/-- Cokernel stalk vanishes at points where the map is stalk-surjective.
    Since the stalk functor on sheaves of abelian groups is exact, `stalk(cokernel f, x) =
    cokernel(stalk(f, x))`, which is zero when `stalk(f, x)` is surjective. -/
theorem cokernel_stalk_zero_of_stalk_surj
    {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (x : X)
    (hf : Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.val)))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj (Limits.cokernel f).val) :
    a = 0 := by
  -- stalk(cokernel.π f) is surjective (epi in sheaves → locally surj → stalk surj)
  have hπ_surj : Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (cokernel.π f).val) := by
    have hEpi : Epi (cokernel.π f) := inferInstance
    have hLS := (Sheaf.isLocallySurjective_iff_epi' (φ := cokernel.π f)).mpr hEpi
    exact ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
      (cokernel.π f).val).mp hLS) x
  -- Lift a to stalk(G) via cokernel.π, then to stalk(F) via f
  obtain ⟨b, rfl⟩ := hπ_surj a
  obtain ⟨c, rfl⟩ := hf b
  -- stalk(f) ≫ stalk(cokernel.π) = 0 at element c via germ representation
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.germ_exist F.val x c
  simp only [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have hcond : f.val ≫ (cokernel.π f).val = (0 : F ⟶ cokernel f).val :=
    congr_arg Sheaf.Hom.val (cokernel.condition f)
  have h1 : ConcreteCategory.hom ((f.val ≫ (cokernel.π f).val).app (op U)) s = 0 := by
    rw [hcond]; rfl
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h1
  rw [h1, map_zero]

/-- **Step 4** (Hartshorne III.2.7): any subsheaf of `zeroOutsideInt V` has vanishing
    cohomology in degree `m > dim X`. Uses `subsheaf_contains_zeroOutsideInt` to find
    `V' ⊆ V` with `Z_{V'} ↪ R` (stalk-iso on `V'`). The cokernel is supported on `(V')^c`
    (dim < dim X), so vanishes by the IH. Middle-term LES gives `H^m(R) = 0`. -/
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
  by_cases hR : IsZero R
  · exact subsingleton_sheafH_of_isZero' R hR m
  · obtain ⟨V', hV'le, hV'ne, j, hj_mono, hj_stalk⟩ :=
      subsheaf_contains_zeroOutsideInt V R i hR
    haveI : Mono j := hj_mono
    let S := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
    have hSE : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel j))
      inferInstance inferInstance
    have hV'van : Subsingleton (Sheaf.H S.X₁ m) :=
      zeroOutsideInt_cohomology_vanishing X ih hpos V' hV'ne m hm
    have hCoker : Subsingleton (Sheaf.H S.X₃ m) := by
      let Y := (V' : Set X)ᶜ
      have hYcl : IsClosed Y := V'.isOpen.isClosed_compl
      have hY_ne : Y ≠ Set.univ := by
        intro h; apply hV'ne; ext x
        simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        exact fun hx => (show x ∈ Y from h ▸ Set.mem_univ x) hx
      have hdim_lt_top : topologicalKrullDim X < ⊤ := lt_of_lt_of_le hm le_top
      have hY_dim : topologicalKrullDim (TopCat.of Y) < topologicalKrullDim X :=
        topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl hY_ne
          (lt_of_le_of_lt (topologicalKrullDim_subspace_le X Y)
            (lt_of_lt_of_le hdim_lt_top le_top))
      have hm_Y : (m : WithBot ℕ∞) > topologicalKrullDim (TopCat.of Y) :=
        lt_trans hY_dim hm
      obtain ⟨S', hS'E, hS'₂, hS'₃⟩ := ClosedImmersionSES Y hYcl (cokernel j)
      have hK_zero : IsZero S'.X₁ := by
        apply sheaf_isZero_of_zero_stalks X S'.X₁; intro x a
        by_cases hx : (x : X) ∈ (V' : Set X)
        · let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
          have ha_img : ConcreteCategory.hom (T.map S'.f.val) a = 0 := by
            rw [hS'₂]; exact cokernel_stalk_zero_of_stalk_surj j x (hj_stalk x hx).2 _
          haveI : Mono S'.f := hS'E.mono_f
          haveI := TopCat.Presheaf.stalkFunctor_preserves_mono
            (C := AddCommGrpCat.{u}) (X := X) x
          haveI : Mono (T.map S'.f.val) := Functor.map_mono T S'.f.val
          rwa [AddCommGrpCat.mono_iff_injective.mp inferInstance |>.eq_iff] at ha_img
        · have hxY : (x : X) ∈ Y := hx
          haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
              (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
                (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Y ⟶ X)).unit.app
                (cokernel j) |>.val) :=
            closedIncl_unit_stalk_isIso hYcl (cokernel j) ⟨x, hxY⟩
          exact stalk_zero_of_ses_g_iso hS'E x inferInstance a
      have hK_van := subsingleton_sheafH_of_isZero' S'.X₁ hK_zero m
      have hP_van : Subsingleton (Sheaf.H S'.X₃ m) := by
        rw [hS'₃]
        exact PushforwardHVanishing Y hYcl _ m (@ih (TopCat.of Y) _ m _ hY_dim hm_Y)
      exact hS'₂ ▸ subsingleton_sheafH_of_shortExact_middle hS'E m hK_van hP_van
    exact subsingleton_sheafH_of_shortExact_middle hSE m hV'van hCoker

/-- **Steps 3C + 4 + LES** (Hartshorne III.2.7): any epi image of `zeroOutsideInt V` has
    vanishing cohomology in degree `m > dim X`. Uses third-term LES with
    `zeroOutsideInt_cohomology_vanishing` (Step 5) and
    `subsheaf_zeroOutsideInt_vanishing` (Step 4). -/
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

/-- **Hartshorne 2.9 core**: on a Noetherian space, if `H^m = 0` for all finitely generated
    subsheaves of `K`, then `H^m(K) = 0`. This encapsulates the commutativity of cohomology
    with filtered colimits: `K = colim K_α`, `H^m(K) = colim H^m(K_α) = colim 0 = 0`. -/
open scoped Classical in
theorem cohomology_vanishing_of_finitelyGenerated_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    (K : TopCat.Sheaf AddCommGrpCat.{u} X) (m : ℕ)
    (hfg : ∀ (S : Finset (TopCat.Sheaf.SectionIndex K)),
      Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf S) m)) :
    Subsingleton (Sheaf.H K m) := by
  -- Key sub-claim: any element of Ext^m(Z, K) factors through some finsetGeneratedSheaf S.
  -- This follows from: (1) Sheaf category is Grothendieck abelian, (2) AB5 gives exact
  -- filtered colimits, (3) derived functors of Hom(Z,-) commute with filtered colimits
  -- when Z is finitely presented (which the constant sheaf is on a Noetherian space).
  sorry

section FinsetGenerated
open scoped Classical

/-- Coproduct inclusion from `S'` to `insert σ₀ S'`. -/
private noncomputable def finsetCoproductIncl
    {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K} (_ : σ₀ ∉ S')
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    (∐ fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟶
    (∐ fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) :=
  Sigma.desc fun σ => Sigma.ι _ ⟨σ.1, Finset.mem_insert_of_mem σ.2⟩

/-- Mono from `image(S')` to `image(insert σ₀ S')` via coproduct inclusion. -/
private noncomputable def imageIncl
    {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K} (hσ₀ : σ₀ ∉ S')
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    TopCat.Sheaf.finsetGeneratedSheaf S' ⟶ TopCat.Sheaf.finsetGeneratedSheaf (insert σ₀ S') :=
  Limits.image.lift ⟨_, Limits.image.ι _, finsetCoproductIncl hσ₀ ≫ factorThruImage _,
    by rw [Category.assoc, Limits.image.fac]; ext σ
       simp [finsetCoproductIncl, TopCat.Sheaf.finsetGeneratorMap,
             TopCat.Sheaf.familyGeneratorMap]⟩

private instance imageIncl_mono
    {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K} (hσ₀ : σ₀ ∉ S')
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Mono (imageIncl hσ₀ : TopCat.Sheaf.finsetGeneratedSheaf S' ⟶ _) := by
  apply mono_of_mono _ (Limits.image.ι _); rw [Limits.image.lift_fac]; exact mono_comp _ _

/-- The `σ₀`-component maps epi onto the cokernel of `imageIncl`. Uses the biproduct
    projection to factor `factorThruImage ≫ cokernel.π` (which is epi) through the
    `σ₀`-component, then `epi_of_epi_fac`. The S'-components vanish via
    `imageIncl ≫ cokernel.π = 0`. -/
private theorem imageIncl_cokernel_epi
    {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K} (hσ₀ : σ₀ ∉ S')
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Epi (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1)
      ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
      factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π (imageIncl hσ₀)) := by
  classical
  let F := fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1
  let σ₀' : {σ // σ ∈ insert σ₀ S'} := ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩
  haveI : Epi (factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π (imageIncl hσ₀)) := epi_comp _ _
  apply epi_of_epi_fac (f := biproduct.isoCoproduct.inv ≫ biproduct.π σ₀')
  show (biproduct.isoCoproduct.inv ≫ biproduct.π σ₀') ≫
    (Sigma.ι F σ₀' ≫ factorThruImage _ ≫ cokernel.π (imageIncl hσ₀)) =
    factorThruImage _ ≫ cokernel.π (imageIncl hσ₀)
  apply colimit.hom_ext; intro ⟨σ⟩
  simp only [Category.assoc, colimit.ι_desc_assoc, biproduct.isoCoproduct_inv,
    colimit.ι_desc_assoc]
  by_cases h : σ = σ₀'
  · subst h; simp [biproduct.ι_π_self_assoc]
  · rw [biproduct.ι_π_ne_assoc _ h, zero_comp, zero_comp]
    have h_S' : σ.1 ∈ S' := by
      have := σ.2; rw [Finset.mem_insert] at this
      rcases this with rfl | hmem
      · exact absurd rfl (by intro heq; exact h (Subtype.ext heq))
      · exact hmem
    have hfact : Sigma.ι (fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1)
        ⟨σ.1, h_S'⟩ ≫ finsetCoproductIncl hσ₀ = Sigma.ι F σ := by
      simp [finsetCoproductIncl]; congr 1; exact Subtype.ext rfl
    rw [← hfact, Category.assoc, Category.assoc]
    rw [show finsetCoproductIncl hσ₀ ≫ factorThruImage _ = factorThruImage _ ≫ imageIncl hσ₀ from by
      apply (cancel_mono (Limits.image.ι _)).mp
      rw [Category.assoc, Category.assoc, Limits.image.lift_fac, Limits.image.fac, Limits.image.fac]
      ext τ; simp [finsetCoproductIncl, TopCat.Sheaf.finsetGeneratorMap,
                    TopCat.Sheaf.familyGeneratorMap]]
    rw [Category.assoc, cokernel.condition, comp_zero]

/-- **Step 3B–3C**: vanishing for `finsetGeneratedSheaf S` by `Finset.induction`.
    Empty set: image = 0. Insert: SES `0 → image(S') → image(S) → cokernel → 0` where
    cokernel is epi image of `Z_{σ₀.1}`, so `hzero` + middle-term LES close the step. -/
theorem finsetGeneratedSheaf_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    (m : ℕ)
    (hzero : ∀ {G : TopCat.Sheaf AddCommGrpCat.{u} X} {V : Opens X}
      (f : TopCat.Sheaf.zeroOutsideInt V ⟶ G), Epi f → Subsingleton (Sheaf.H G m))
    (S : Finset (TopCat.Sheaf.SectionIndex K)) :
    Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf S) m) := by
  induction S using Finset.induction with
  | empty =>
    apply subsingleton_sheafH_of_isZero'
    have : IsZero (∐ fun σ : {σ // σ ∈ (∅ : Finset _)} => TopCat.Sheaf.zeroOutsideInt σ.1.1) := by
      haveI : IsEmpty {σ // σ ∈ (∅ : Finset (TopCat.Sheaf.SectionIndex K))} := by
        simp; exact inferInstance
      exact isZero_initial
    rw [TopCat.Sheaf.finsetGeneratedSheaf, this.eq_of_src _ 0]; exact isZero_image_zero_morphism
  | @insert σ₀ S' hσ₀ ih =>
    let S_ses := ShortComplex.mk (imageIncl hσ₀) (cokernel.π (imageIncl hσ₀))
      (cokernel.condition _)
    have hSE : S_ses.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) inferInstance inferInstance
    have h_old : Subsingleton (Sheaf.H S_ses.X₁ m) := ih
    have h_coker : Subsingleton (Sheaf.H S_ses.X₃ m) := by
      exact hzero
        (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1)
          ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
        factorThruImage _ ≫ cokernel.π (imageIncl hσ₀)) (imageIncl_cokernel_epi hσ₀)
    exact subsingleton_sheafH_of_shortExact_middle hSE m h_old h_coker

end FinsetGenerated

/-- **Step 3A** (Hartshorne III.2.7): on a Noetherian space, if vanishing holds for
    all epi images of `zeroOutsideInt V`, then it holds for every sheaf.
    Assembles `finsetGeneratedSheaf_vanishing` (finite case) with
    `cohomology_vanishing_of_finitelyGenerated_vanishing` (colimit step). -/
theorem directLimit_cohomology_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    (K : TopCat.Sheaf AddCommGrpCat.{u} X) (m : ℕ)
    (hzero : ∀ {G : TopCat.Sheaf AddCommGrpCat.{u} X} {V : Opens X}
      (f : TopCat.Sheaf.zeroOutsideInt V ⟶ G), Epi f → Subsingleton (Sheaf.H G m)) :
    Subsingleton (Sheaf.H K m) :=
  cohomology_vanishing_of_finitelyGenerated_vanishing K m
    (fun S => finsetGeneratedSheaf_vanishing m hzero S)

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
      (TopCat.closedIncl hZ_closed)).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
          (TopCat.closedIncl hZ_closed)).obj F)) :
    Subsingleton (Sheaf.H S.X₁ n) :=
  directLimit_cohomology_vanishing S.X₁ n
    (fun f hf => epiImage_zeroOutsideInt_vanishing X ih hpos _ f hf n hn)

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

