/-
  IrreducibleStep.lean — Vanishing for irreducible spaces of positive dimension

  Key results:
  - subsingleton_ext_of_ses: PROVED — abstract LES vanishing
  - constantSheaf_flasque_of_irreducible: PROVED (in ConstantSheafFlasque.lean)
  - constantSheaf_cohomology_vanishing: PROVED from flasque + FlasqueVanishing
  - grothendieck_vanishing_irreducible_pos: uses IrreduciblePosVanishing (2 sorry's:
    exists_good_section, cohomology_vanishing_of_finitelyGenerated_vanishing)
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
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hSE : S.ShortExact :=
    ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
      inferInstance inferInstance
  have hFlasque : IsFlasqueSheaf S.X₂ := by
    intro U W i
    have := constantSheaf_flasque_of_irreducible X i
    sorry -- needs: zeroOutsideInt ⊤ = constantSheaf ℤ (flasque)
  exact sheafH_dimension_shift_ses hSE m hCoker
    (FlasqueVanishing X S.X₂ hFlasque m)

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
  -- Restrict to W ⊓ V, where both presheaves agree with constZ
  set WV := W ⊓ V with hWV_def
  have hWV_le_V : WV ≤ V := inf_le_right
  have hWV_le_W : WV ≤ W := inf_le_left
  have hxWV : x ∈ WV := ⟨hxW, hx⟩
  -- On WV, openHom is an iso (eqToHom)
  have happ_iso : IsIso ((TopCat.Presheaf.zeroOutside_openHom
    (F := TopCat.Presheaf.constZ) h).app (op WV)) := by
    simp only [TopCat.Presheaf.zeroOutside_openHom, hWV_le_V, ↓reduceDIte]
    infer_instance
  -- Use the iso to find a preimage of the restricted section
  let s_res := ConcreteCategory.hom
    ((TopCat.Presheaf.constZ.zeroOutside U).map (homOfLE hWV_le_W).op) s
  have h_bij := ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.zeroOutside_openHom (F := TopCat.Presheaf.constZ) h).app (op WV))
  obtain ⟨t, ht⟩ := h_bij.2 s_res
  refine ⟨(TopCat.Presheaf.constZ.zeroOutside V).germ WV x hxWV t, ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change (TopCat.Presheaf.constZ.zeroOutside U).germ WV x hxWV
    ((TopCat.Presheaf.zeroOutside_openHom (F := TopCat.Presheaf.constZ) h).app (op WV) t) =
    (TopCat.Presheaf.constZ.zeroOutside U).germ W x hxW s
  rw [ht]; simp only [s_res]
  convert ((TopCat.Presheaf.constZ.zeroOutside U).germ_res_apply
    (homOfLE hWV_le_W) x hxWV s) using 1

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
  have hnat : T.map φ ≫ T.map (toSheafify J _) =
    T.map (toSheafify J _) ≫ T.map (sheafifyMap J φ) := by
    rw [← T.map_comp, ← T.map_comp, toSheafify_naturality]
  haveI : IsIso (T.map (toSheafify J (TopCat.Presheaf.constZ.zeroOutside V))) :=
    stalkFunctor_map_iso_toSheafify _ x
  haveI : IsIso (T.map (toSheafify J (TopCat.Presheaf.constZ.zeroOutside U))) :=
    stalkFunctor_map_iso_toSheafify _ x
  intro g
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map (toSheafify J _))).2 g
  obtain ⟨p, hp⟩ := presheaf_stalk_surj_openHom h x hx q
  exact ⟨ConcreteCategory.hom (T.map (toSheafify J _)) p, by
    change ConcreteCategory.hom (T.map (sheafifyMap J φ))
      (ConcreteCategory.hom (T.map (toSheafify J _)) p) = _
    rw [← ConcreteCategory.comp_apply, hnat.symm, ConcreteCategory.comp_apply, hp]⟩

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
        (TopCat.Sheaf.zeroOutsideInt.openHom h).val)) :=
  by
  refine ⟨?_, sheaf_stalk_surj_openHom h x hx⟩
  let FT := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI := TopCat.Presheaf.stalkFunctor_preserves_mono (C := AddCommGrpCat.{u}) (X := X) x
  haveI : Mono (FT.map (TopCat.Sheaf.zeroOutsideInt.openHom h)) :=
    Functor.map_mono FT (TopCat.Sheaf.zeroOutsideInt.openHom h)
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback
    (FT.map (TopCat.Sheaf.zeroOutsideInt.openHom h))).mp inferInstance

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
  have hπ_surj : Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (cokernel.π f).val)) := by
    have hEpi : Epi (cokernel.π f) := inferInstance
    have hLS := (Sheaf.isLocallySurjective_iff_epi' (φ := cokernel.π f)).mpr hEpi
    exact ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
      (cokernel.π f).val).mp hLS) x
  obtain ⟨b, rfl⟩ := hπ_surj a
  obtain ⟨c, rfl⟩ := hf b
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.germ_exist F.val x c
  simp only [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have hcond : f.val ≫ (cokernel.π f).val = (0 : F ⟶ cokernel f).val :=
    congr_arg Sheaf.Hom.val (cokernel.condition f)
  have h1 : ConcreteCategory.hom ((f.val ≫ (cokernel.π f).val).app (op U)) s = 0 := by
    rw [hcond]; rfl
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h1
  rw [h1, map_zero]

/-- The cokernel of `openHom(le_top)` has zero stalks at points of `V`.
    Uses: sheaf stalk surjectivity + section_ext + local surjectivity of `cokernel.π`
    + `cokernel.condition`. -/
private theorem cokernel_stalk_zero_V {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (Limits.cokernel (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤))).val) :
    a = 0 :=
  cokernel_stalk_zero_of_stalk_surj _ x (sheaf_stalk_surj V x hx) a

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
  set C := Limits.cokernel f
  -- Y = Vᶜ is closed, proper, has dim < dim X
  set Y := (V : Set X)ᶜ with hY_def
  have hYcl : IsClosed Y := V.2.isClosed_compl
  have hY_ne_univ : Y ≠ Set.univ :=
    Set.compl_ne_univ.mpr (Set.nonempty_iff_ne_empty.mpr (Opens.coe_eq_empty.not.mpr hV))
  have hY_dim_lt : topologicalKrullDim Y < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl hY_ne_univ
      (lt_of_le_of_lt (topologicalKrullDim_subspace_le (X := (↑X : Type u)) Y)
        (lt_of_lt_of_le hn le_top))
  have hn_Y : ↑n > topologicalKrullDim (TopCat.of Y) :=
    lt_trans hY_dim_lt hn
  -- Build SES via ClosedImmersionSES on Vᶜ with C (use let-bindings for dsimp)
  let i : TopCat.of Y ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i
  let η := adj.unit.app C
  haveI : Epi η := epi_unit_of_closedImmersion Y hYcl C
  let S := ShortComplex.mk (kernel.ι η) η (kernel.condition η)
  have hSE : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel η)) inferInstance inferInstance
  have hS₂ : S.X₂ = C := rfl
  have hS₃ : S.X₃ = (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj C) := rfl
  -- Pushforward vanishing by IH
  have hPush : Subsingleton (Sheaf.H S.X₃ n) := by
    rw [hS₃]
    exact PushforwardHVanishing Y hYcl _ n (@ih (TopCat.of Y) _ n _ hY_dim_lt hn_Y)
  -- Kernel vanishing: zero stalks everywhere → IsZero → vanishing
  have hKer : Subsingleton (Sheaf.H S.X₁ n) := by
    apply subsingleton_sheafH_of_isZero'
    apply sheaf_isZero_of_zero_stalks X; intro x a
    by_cases hxY : x ∈ Y
    · -- At points in Vᶜ: closedIncl_unit_stalk_isIso gives S.g iso → kernel stalk = 0
      haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val) := by
        dsimp [S, η]
        exact closedIncl_unit_stalk_isIso hYcl C ⟨x, hxY⟩
      exact stalk_zero_of_ses_g_iso hSE x inferInstance a
    · -- At points in V: C has zero stalks, so S.X₂ = C has zero stalk, mono gives kernel = 0
      have hxV : x ∈ V := by rwa [hY_def, Set.mem_compl_iff, not_not] at hxY
      have hstalk_zero :
          ∀ (b : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₂.val),
          b = 0 := fun b => cokernel_stalk_zero_V V x hxV b
      let FT := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
      haveI : Mono S.f := hSE.mono_f
      haveI := TopCat.Presheaf.stalkFunctor_preserves_mono
        (C := AddCommGrpCat.{u}) (X := X) x
      haveI : Mono (FT.map S.f) := Functor.map_mono FT S.f
      rw [AddCommGrpCat.mono_iff_injective] at this
      exact this ((hstalk_zero _).trans (map_zero _).symm)
  rw [← hS₂]
  exact subsingleton_sheafH_of_shortExact_middle hSE n hKer hPush

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
  -- Step 1: m ≠ 0 (since m > dim X > 0), write m = m' + 1
  have hm_ne : m ≠ 0 := by intro h; subst h; simp at hm; exact not_lt.mpr (le_of_lt hpos) hm
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne
  -- Step 2: apply zeroOutsideInt_vanishing, reducing to cokernel vanishing at m'
  apply zeroOutsideInt_vanishing X V m'
  -- Goal: Subsingleton (Sheaf.H (Limits.cokernel (openHom le_top)) m')
  -- Step 3: ClosedImmersionSES on Y = Vᶜ applied to the cokernel C
  set f := TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤)
  set C := Limits.cokernel f
  set Y := (V : Set X)ᶜ with hY_def
  have hYcl : IsClosed Y := V.2.isClosed_compl
  have hY_ne_univ : Y ≠ Set.univ :=
    Set.compl_ne_univ.mpr (Set.nonempty_iff_ne_empty.mpr (Opens.coe_eq_empty.not.mpr hV))
  have hY_dim_lt : topologicalKrullDim Y < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl hY_ne_univ
      (lt_of_le_of_lt (topologicalKrullDim_subspace_le (X := (↑X : Type u)) Y)
        (lt_of_lt_of_le hm le_top))
  -- Dimension arithmetic: m' > dim Y
  have hm'_Y : ↑m' > topologicalKrullDim (TopCat.of Y) := by
    show topologicalKrullDim Y < ↑m'
    have hd_ne_bot : topologicalKrullDim X ≠ ⊥ := ne_bot_of_gt hpos
    lift topologicalKrullDim X to ℕ∞ using hd_ne_bot with d
    have hm' : (d : WithBot ℕ∞) < ↑((m'.succ : ℕ) : ℕ∞) := hm
    rw [WithBot.coe_lt_coe] at hm'
    have hd_ne_top : d ≠ ⊤ := ne_top_of_lt hm'
    lift d to ℕ using hd_ne_top with d'
    rw [ENat.coe_lt_coe] at hm'
    calc topologicalKrullDim Y < ↑↑d' := hY_dim_lt
      _ ≤ ↑↑m' := by exact_mod_cast Nat.lt_succ_iff.mp hm'
  -- Build SES via ClosedImmersionSES on Vᶜ with C
  let i : TopCat.of Y ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i
  let η := adj.unit.app C
  haveI : Epi η := epi_unit_of_closedImmersion Y hYcl C
  let S := ShortComplex.mk (kernel.ι η) η (kernel.condition η)
  have hSE : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel η)) inferInstance inferInstance
  have hS₂ : S.X₂ = C := rfl
  have hS₃ : S.X₃ = (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj C) := rfl
  -- Pushforward vanishing by IH
  have hPush : Subsingleton (Sheaf.H S.X₃ m') := by
    rw [hS₃]
    exact PushforwardHVanishing Y hYcl _ m' (@ih (TopCat.of Y) _ m' _ hY_dim_lt hm'_Y)
  -- Kernel vanishing: zero stalks everywhere → IsZero → vanishing
  have hKer : Subsingleton (Sheaf.H S.X₁ m') := by
    apply subsingleton_sheafH_of_isZero'
    apply sheaf_isZero_of_zero_stalks X; intro x a
    by_cases hxY : x ∈ Y
    · -- At points in Vᶜ: closedIncl_unit_stalk_isIso gives S.g iso → kernel stalk = 0
      haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val) := by
        dsimp [S, η]
        exact closedIncl_unit_stalk_isIso hYcl C ⟨x, hxY⟩
      exact stalk_zero_of_ses_g_iso hSE x inferInstance a
    · -- At points in V: C has zero stalks, so S.X₂ = C has zero stalk, mono gives kernel = 0
      have hxV : x ∈ V := by rwa [hY_def, Set.mem_compl_iff, not_not] at hxY
      have hstalk_zero :
          ∀ (b : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₂.val),
          b = 0 := fun b => cokernel_stalk_zero_V V x hxV b
      let FT := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
      haveI : Mono S.f := hSE.mono_f
      haveI := TopCat.Presheaf.stalkFunctor_preserves_mono
        (C := AddCommGrpCat.{u}) (X := X) x
      haveI : Mono (FT.map S.f) := Functor.map_mono FT S.f
      rw [AddCommGrpCat.mono_iff_injective] at this
      exact this ((hstalk_zero _).trans (map_zero _).symm)
  rw [← hS₂]
  exact subsingleton_sheafH_of_shortExact_middle hSE m' hKer hPush

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
  let P := TopCat.Presheaf.constZ.zeroOutside (⊥ : Opens X)
  let J := Opens.grothendieckTopology (T := X)
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI : IsIso (T.map (toSheafify J P)) := stalkFunctor_map_iso_toSheafify P x
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map (toSheafify J P))).2 a
  obtain ⟨W, hxW, s, rfl⟩ := P.germ_exist x q
  have hW : ¬ (W ≤ ⊥) := fun h => Opens.mem_bot.mp (h hxW)
  have hIsZero := TopCat.Presheaf.zeroOutside_isZero (F := TopCat.Presheaf.constZ) hW
  haveI := AddCommGrpCat.subsingleton_of_isZero hIsZero
  simp [Subsingleton.eq_zero s, map_zero]

/-- Stalks of `zeroOutsideInt V` vanish outside `V`. -/
theorem stalk_zeroOutsideInt_zero_outside
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∉ V)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (TopCat.Sheaf.zeroOutsideInt V).val) : a = 0 := by
  let P := TopCat.Presheaf.constZ.zeroOutside V
  let J := Opens.grothendieckTopology (T := X)
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI : IsIso (T.map (toSheafify J P)) := stalkFunctor_map_iso_toSheafify P x
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map (toSheafify J P))).2 a
  obtain ⟨W, hxW, s, rfl⟩ := P.germ_exist x q
  have hW : ¬ (W ≤ V) := fun h => hx (h hxW)
  have hIsZero := TopCat.Presheaf.zeroOutside_isZero (F := TopCat.Presheaf.constZ) hW
  haveI := AddCommGrpCat.subsingleton_of_isZero hIsZero
  simp [Subsingleton.eq_zero s, map_zero]

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
  · let FT := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    have h_img : ConcreteCategory.hom (FT.map i) a = 0 :=
      stalk_zeroOutsideInt_zero_outside V x hx _
    haveI := TopCat.Presheaf.stalkFunctor_preserves_mono
      (C := AddCommGrpCat.{u}) (X := X) x
    haveI : Mono (FT.map i) := Functor.map_mono FT i
    have hinj := (ConcreteCategory.mono_iff_injective_of_preservesPullback
      (FT.map i)).mp inferInstance
    rw [← map_zero (ConcreteCategory.hom (FT.map i))] at h_img
    exact hinj h_img

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
  · -- W ≤ V: the section s lives in constZ.obj (op W) ≅ ULift ℤ
    have hObjW : (TopCat.Presheaf.zeroOutside V TopCat.Presheaf.constZ).obj (op W) =
        AddCommGrpCat.of (ULift ℤ) := by
      simp [TopCat.Presheaf.zeroOutside, hWV, TopCat.Presheaf.constZ]
    let w : ULift ℤ := (AddCommGrpCat.Hom.hom (eqToHom hObjW)) s
    -- The restriction of generator V to W
    let genW : (TopCat.Presheaf.constZ.zeroOutside V).obj (op W) :=
      ConcreteCategory.hom
        ((TopCat.Presheaf.constZ.zeroOutside V).map (homOfLE hWV).op)
        (TopCat.Presheaf.zeroOutside.generator V)
    -- Under the iso to ULift ℤ, genW maps to 1
    have hgenW_val : (AddCommGrpCat.Hom.hom (eqToHom hObjW)) genW = (1 : ULift ℤ) := by
      show (AddCommGrpCat.Hom.hom (eqToHom hObjW))
        (ConcreteCategory.hom ((TopCat.Presheaf.constZ.zeroOutside V).map (homOfLE hWV).op)
          (TopCat.Presheaf.zeroOutside.generator V)) = 1
      -- Unfold map and generator, reduce dite, compose eqToHoms
      simp only [TopCat.Presheaf.zeroOutside.generator, TopCat.Presheaf.zeroOutside_map,
        dif_pos hWV, dif_pos (le_refl V)]
      simp only [← ConcreteCategory.comp_apply, ← CategoryTheory.comp_apply,
        eqToHom_trans, Functor.const_obj_map, Category.id_comp]
      have : hObjW.symm.trans hObjW = rfl := Subsingleton.elim _ _
      simp [this]
    -- eqToHom is injective (it's an iso)
    have hinj : Function.Injective (AddCommGrpCat.Hom.hom (eqToHom hObjW)) := by
      intro a b h
      have := TopCat.Presheaf.zeroOutside.hom_eqToHom_symm_hom_eqToHom hObjW
      exact (this a).symm.trans (congrArg _ h |>.trans (this b))
    -- s = w.down • genW
    have hs_zsmul : s = w.down • genW := by
      apply hinj
      rw [map_zsmul, hgenW_val]
      show w = w.down • (1 : ULift ℤ)
      ext; simp
    refine ⟨w.down, ?_⟩
    rw [hs_zsmul, map_zsmul (ConcreteCategory.hom
      ((TopCat.Presheaf.constZ.zeroOutside V).germ W x hxW))]
    congr 1
    show (ConcreteCategory.hom ((TopCat.Presheaf.constZ.zeroOutside V).germ W x hxW))
        (ConcreteCategory.hom ((TopCat.Presheaf.constZ.zeroOutside V).map (homOfLE hWV).op)
          (TopCat.Presheaf.zeroOutside.generator V)) =
      (ConcreteCategory.hom ((TopCat.Presheaf.constZ.zeroOutside V).germ V x hx))
        (TopCat.Presheaf.zeroOutside.generator V)
    exact TopCat.Presheaf.germ_res_apply (TopCat.Presheaf.constZ.zeroOutside V)
      (homOfLE hWV) x hxW (TopCat.Presheaf.zeroOutside.generator V)
  · -- ¬(W ≤ V): the object at W is zero
    have hIsZero := TopCat.Presheaf.zeroOutside_isZero (F := TopCat.Presheaf.constZ) hWV
    haveI := AddCommGrpCat.subsingleton_of_isZero hIsZero
    refine ⟨0, ?_⟩
    simp [Subsingleton.eq_zero s, map_zero]

/-- At a point inside the support open, every stalk element of `zeroOutsideInt V` is an integer
    multiple of the germ of the distinguished generator over `V`. -/
private theorem stalk_zeroOutsideInt_eq_zsmul_generator
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (TopCat.Sheaf.zeroOutsideInt V).val) :
    ∃ n : ℤ,
      a = n • ((TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V x hx
        (TopCat.Sheaf.zeroOutsideInt.generator V)) := by
  let P := TopCat.Presheaf.constZ.zeroOutside V
  let J := Opens.grothendieckTopology (T := X)
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI : IsIso (T.map (toSheafify J P)) := stalkFunctor_map_iso_toSheafify P x
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map (toSheafify J P))).2 a
  obtain ⟨n, hn⟩ := presheaf_stalk_zeroOutside_eq_zsmul_generator V x hx q
  refine ⟨n, ?_⟩
  rw [hn, map_zsmul]
  congr 1
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply V x hx
    (toSheafify J P) (TopCat.Presheaf.zeroOutside.generator V)

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

/-- In `stalk(zeroOutsideInt V, x)` for `x ∈ V`, the integer coefficient in the generator
    representation is unique: `n • gen = m • gen → n = m`. -/
private theorem zsmul_generator_injective
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V)
    {n m : ℤ}
    (h : n • ((TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V x hx
        (TopCat.Sheaf.zeroOutsideInt.generator V)) =
      m • ((TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V x hx
        (TopCat.Sheaf.zeroOutsideInt.generator V))) : n = m := by
  let P := TopCat.Presheaf.constZ.zeroOutside V
  let J := Opens.grothendieckTopology (T := X)
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI : IsIso (T.map (toSheafify J P)) := stalkFunctor_map_iso_toSheafify P x
  have hbij := ConcreteCategory.bijective_of_isIso (T.map (toSheafify J P))
  have hgen_eq : ConcreteCategory.hom (T.map (toSheafify J P))
      (P.germ V x hx (TopCat.Presheaf.zeroOutside.generator V)) =
      (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V x hx
        (TopCat.Sheaf.zeroOutsideInt.generator V) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply V x hx
      (toSheafify J P) (TopCat.Presheaf.zeroOutside.generator V)
  -- Transfer to presheaf stalk via injectivity of toSheafify stalk map
  set gen_P := TopCat.Presheaf.zeroOutside.generator V with hgen_P_def
  have h' : P.germ V x hx (n • gen_P) = P.germ V x hx (m • gen_P) := by
    rw [map_zsmul, map_zsmul]
    apply hbij.1; simp only [map_zsmul, hgen_eq]; exact h
  -- Use germ_eq: equal germs agree on a refinement W ≤ V
  obtain ⟨W, hxW, iU, iV, hEq⟩ := P.germ_eq x hx hx _ _ h'
  -- Both iU, iV are maps W → V; they're equal by subsingleton
  have hiUiV : iU = iV := Subsingleton.elim _ _
  rw [hiUiV, map_zsmul, map_zsmul] at hEq
  -- Now: n • P.map iV.op gen_V = m • P.map iV.op gen_V in P.obj(op W)
  have hWV : W ≤ V := leOfHom iV
  -- Replace iV.op by (homOfLE hWV).op (subsingleton)
  have hiV_eq : iV = homOfLE hWV := Subsingleton.elim _ _
  rw [hiV_eq] at hEq
  -- P.obj(op W) = ULift ℤ since W ≤ V
  have hObjW : P.obj (op W) = AddCommGrpCat.of (ULift ℤ) := by
    simp [P, TopCat.Presheaf.zeroOutside, hWV, TopCat.Presheaf.constZ]
  -- The restricted generator maps to 1 in ULift ℤ (reuse pattern from line 491)
  set resGen := ConcreteCategory.hom (P.map (homOfLE hWV).op) gen_P with hresGen_def
  -- resGen maps to 1 ∈ ULift ℤ via eqToHom (same calculation as line ~491)
  have hresGen_val : (AddCommGrpCat.Hom.hom (eqToHom hObjW)) resGen = (1 : ULift ℤ) := by
    -- resGen = (P.map (homOfLE hWV).op) gen_P where P = constZ.zeroOutside V
    -- Under eqToHom to ULift ℤ, this composition sends gen to 1
    -- (eqToHom ∘ zeroOutside_map ∘ eqToHom)(1) = 1 by eqToHom_trans
    simp only [resGen, gen_P, P]
    -- Now the goal is explicit: unfold generator and zeroOutside_map
    unfold TopCat.Presheaf.zeroOutside.generator
    simp only [TopCat.Presheaf.zeroOutside_map, dif_pos hWV, dif_pos (le_refl V)]
    simp only [← ConcreteCategory.comp_apply, ← CategoryTheory.comp_apply,
      eqToHom_trans, Functor.const_obj_map, Category.id_comp]
    have : hObjW.symm.trans hObjW = rfl := Subsingleton.elim _ _
    simp [this]
  -- eqToHom is injective
  have hinj_eqToHom : Function.Injective (AddCommGrpCat.Hom.hom (eqToHom hObjW)) := by
    intro a b hab
    have := TopCat.Presheaf.zeroOutside.hom_eqToHom_symm_hom_eqToHom hObjW
    exact (this a).symm.trans (congrArg _ hab |>.trans (this b))
  -- Transfer hEq to ULift ℤ
  have hEq_ULift : n • (1 : ULift ℤ) = m • (1 : ULift ℤ) := by
    have := congrArg (AddCommGrpCat.Hom.hom (eqToHom hObjW)) hEq
    rwa [map_zsmul, map_zsmul, hresGen_val] at this
  -- n • (1 : ULift ℤ) = m • (1 : ULift ℤ) → n = m
  have := congrArg ULift.down hEq_ULift
  simp at this
  exact this

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


/-- The stalk map of `sHom s` at `x ∈ U` is bijective when every stalk element of R at x
    is an integer multiple of `germ(s, x)`, and R embeds into `zeroOutsideInt V`
    (providing torsion-freeness needed for injectivity). -/
private theorem sHom_stalk_bijective_at
    {X : TopCat.{u}} (V U : Opens X) (hUV : U ≤ V)
    (R : TopCat.Sheaf AddCommGrpCat.{u} X)
    (i : R ⟶ TopCat.Sheaf.zeroOutsideInt V) [Mono i]
    (s : R.val.obj (op U))
    (x : X) (hxU : x ∈ U)
    -- germ(s, x) ≠ 0 (needed for injectivity; without this, stalk(R,x) could be 0
    -- while stalk(zeroOutsideInt U, x) ≅ ℤ, making the map non-injective)
    (hs_ne : R.presheaf.germ U x hxU s ≠ 0)
    -- Every stalk element of R at x is an integer multiple of germ(s, x)
    (hgen : ∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj R.val),
      ∃ k : ℤ, a = k • R.presheaf.germ U x hxU s) :
    Function.Bijective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (TopCat.Sheaf.zeroOutsideInt.sHom s).val)) := by
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let sHom_x := ConcreteCategory.hom (T.map (TopCat.Sheaf.zeroOutsideInt.sHom s).val)
  let i_x := ConcreteCategory.hom (T.map i.val)
  -- i_x is injective
  let FT := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ T
  haveI := TopCat.Presheaf.stalkFunctor_preserves_mono (C := AddCommGrpCat.{u}) (X := X) x
  haveI : Mono (FT.map i) := Functor.map_mono FT i
  have hi_inj : Function.Injective i_x :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback (FT.map i)).mp inferInstance
  -- i_x(germ(s,x)) ≠ 0
  have hi_s_ne : i_x (R.presheaf.germ U x hxU s) ≠ 0 := by
    intro h; exact hs_ne (hi_inj (h.trans (map_zero i_x).symm))
  -- i_x(germ(s,x)) = c • gen_V for some c ≠ 0
  obtain ⟨c, hc⟩ := stalk_zeroOutsideInt_eq_zsmul_generator V x (hUV hxU)
    (i_x (R.presheaf.germ U x hxU s))
  have hc_ne : c ≠ 0 := by
    intro hc0; rw [hc0, zero_smul] at hc; exact hi_s_ne hc
  -- Key: sHom_x(germ(gen_U, x)) = germ(s, x)
  have h_sHom_gen : sHom_x ((TopCat.Sheaf.zeroOutsideInt U).presheaf.germ U x hxU
      (TopCat.Sheaf.zeroOutsideInt.generator U)) = R.presheaf.germ U x hxU s := by
    show T.map (TopCat.Sheaf.zeroOutsideInt.sHom s).val
      ((TopCat.Sheaf.zeroOutsideInt U).presheaf.germ U x hxU
        (TopCat.Sheaf.zeroOutsideInt.generator U)) =
      R.presheaf.germ U x hxU s
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    congr 1
    exact TopCat.Sheaf.zeroOutsideInt.sHom_app_generator s
  -- Surjectivity
  have h_surj : Function.Surjective sHom_x := by
    intro a
    obtain ⟨k, hk⟩ := hgen a
    refine ⟨k • (TopCat.Sheaf.zeroOutsideInt U).presheaf.germ U x hxU
      (TopCat.Sheaf.zeroOutsideInt.generator U), ?_⟩
    rw [map_zsmul, h_sHom_gen, hk]
  -- Injectivity: n • germ(s,x) = m • germ(s,x) → n = m (using torsion-freeness via i)
  have h_inj : Function.Injective sHom_x := by
    intro a b hab
    obtain ⟨n, rfl⟩ := stalk_zeroOutsideInt_eq_zsmul_generator U x hxU a
    obtain ⟨m, rfl⟩ := stalk_zeroOutsideInt_eq_zsmul_generator U x hxU b
    simp only [map_zsmul, h_sHom_gen] at hab
    -- hab : n • germ(s, x) = m • germ(s, x) in stalk(R, x)
    -- Apply i_x: n • i_x(germ(s,x)) = m • i_x(germ(s,x))
    have h_i : n • i_x (R.presheaf.germ U x hxU s) =
        m • i_x (R.presheaf.germ U x hxU s) := by
      rw [← map_zsmul i_x, ← map_zsmul i_x, hab]
    -- Substitute i_x(germ(s,x)) = c • gen_V: n • (c • gen_V) = m • (c • gen_V)
    rw [hc, smul_comm n, smul_comm m, ← mul_smul, ← mul_smul] at h_i
    -- h_i : (c * n) • gen_V = (c * m) • gen_V, so c * n = c * m
    have h_cn : c * n = c * m := zsmul_generator_injective V x (hUV hxU) h_i
    -- c ≠ 0, so n = m
    have h_nm : n = m := mul_left_cancel₀ hc_ne h_cn
    rw [h_nm]
  exact ⟨h_inj, h_surj⟩

/-- At each point `x ∈ V`, the image of the stalk of `R` under `i` is a subgroup of
    `stalk(zeroOutsideInt V, x) ≅ ULift ℤ`. By `ulift_int_subgroup_cyclic`, if this image
    is nonzero, it has a positive generator `d_x`. The "index" `d_x` measures how deeply
    `R` sits inside `zeroOutsideInt V` at `x`.

    This lemma produces `V' ≤ V`, `V' ≠ ⊥`, and `s ∈ R(V')` such that for all `x ∈ V'`:
    (1) `germ(s, x) ≠ 0`
    (2) every stalk element of `R` at `x` is an integer multiple of `germ(s, x)`.
    This is the hard "Noetherian shrinking" step of Hartshorne III.2.7, Step 4. -/
private theorem exists_section_generating_stalks
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (R : TopCat.Sheaf AddCommGrpCat.{u} X)
    (i : R ⟶ TopCat.Sheaf.zeroOutsideInt V) [Mono i]
    (hR : ¬ IsZero R) :
    ∃ (V' : Opens X) (_ : V' ≤ V) (_ : V' ≠ ⊥)
      (s : R.val.obj (op V')),
      ∀ (x : X) (hx : x ∈ V'),
        (R.presheaf.germ V' x hx s ≠ 0) ∧
        (∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj R.val),
          ∃ k : ℤ, a = k • R.presheaf.germ V' x hx s) := by
  sorry

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
  -- Use the Noetherian shrinking lemma to get V', s with generating property
  obtain ⟨V', hV'V, hV'ne, s, hgen⟩ := exists_section_generating_stalks V R i hR
  exact ⟨V', hV'V, hV'ne, s, fun x hx =>
    sHom_stalk_bijective_at V V' hV'V R i s x hx (hgen x hx).1 (hgen x hx).2⟩

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
  · -- Step 1: Get V' ⊆ V, V' ≠ ⊥, and j : zeroOutsideInt V' ⟶ R with stalk-iso on V'
    obtain ⟨V', hV'le, hV'ne, j, hj_mono, hj_stalk⟩ :=
      subsheaf_contains_zeroOutsideInt V R i hR
    haveI : Mono j := hj_mono
    -- Step 2: Build SES  0 → zeroOutsideInt V' → R → cokernel j → 0
    let S := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
    have hSE : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel j)) inferInstance inferInstance
    -- Step 3: First-term vanishing: H^m(zeroOutsideInt V') = 0
    have hV'van : Subsingleton (Sheaf.H S.X₁ m) :=
      zeroOutsideInt_cohomology_vanishing X ih hpos V' hV'ne m hm
    -- Step 4: Third-term (cokernel) vanishing via ClosedImmersionSES on (V')^c
    have hCoker : Subsingleton (Sheaf.H S.X₃ m) := by
      set CJ := Limits.cokernel j
      -- Y = (V')^c is closed, proper, has dim < dim X
      set Y := (V' : Set X)ᶜ with hY_def
      have hYcl : IsClosed Y := V'.isOpen.isClosed_compl
      have hY_ne_univ : Y ≠ Set.univ :=
        Set.compl_ne_univ.mpr (Set.nonempty_iff_ne_empty.mpr (Opens.coe_eq_empty.not.mpr hV'ne))
      have hY_dim_lt : topologicalKrullDim Y < topologicalKrullDim X :=
        topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl hY_ne_univ
          (lt_of_le_of_lt (topologicalKrullDim_subspace_le (X := (↑X : Type u)) Y)
            (lt_of_lt_of_le hm le_top))
      have hm_Y : ↑m > topologicalKrullDim (TopCat.of Y) :=
        lt_trans hY_dim_lt hm
      -- Build SES via ClosedImmersionSES on (V')^c with CJ
      let ci : TopCat.of Y ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} ci
      let η := adj.unit.app CJ
      haveI : Epi η := epi_unit_of_closedImmersion Y hYcl CJ
      let S' := ShortComplex.mk (kernel.ι η) η (kernel.condition η)
      have hSE' : S'.ShortExact := ShortComplex.ShortExact.mk'
        (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel η)) inferInstance inferInstance
      have hS'₂ : S'.X₂ = CJ := rfl
      have hS'₃ : S'.X₃ = (TopCat.Sheaf.pushforward AddCommGrpCat.{u} ci).obj
          ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ci).obj CJ) := rfl
      -- Pushforward vanishing by IH
      have hPush : Subsingleton (Sheaf.H S'.X₃ m) := by
        rw [hS'₃]
        exact PushforwardHVanishing Y hYcl _ m (@ih (TopCat.of Y) _ m _ hY_dim_lt hm_Y)
      -- Kernel vanishing: zero stalks everywhere → IsZero → vanishing
      have hKer : Subsingleton (Sheaf.H S'.X₁ m) := by
        apply subsingleton_sheafH_of_isZero'
        apply sheaf_isZero_of_zero_stalks X; intro x a
        by_cases hxY : x ∈ Y
        · -- At points in (V')^c: closedIncl_unit_stalk_isIso gives S'.g iso → kernel stalk = 0
          haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S'.g.val) := by
            dsimp [S', η]
            exact closedIncl_unit_stalk_isIso hYcl CJ ⟨x, hxY⟩
          exact stalk_zero_of_ses_g_iso hSE' x inferInstance a
        · -- At points in V': cokernel j has zero stalks (j is stalk-surjective)
          have hxV' : x ∈ V' := by rwa [hY_def, Set.mem_compl_iff, not_not] at hxY
          have hstalk_zero :
              ∀ (b : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S'.X₂.val),
              b = 0 := fun b =>
            cokernel_stalk_zero_of_stalk_surj j x (hj_stalk x hxV').2 b
          let FT := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
              TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
          haveI : Mono S'.f := hSE'.mono_f
          haveI := TopCat.Presheaf.stalkFunctor_preserves_mono
            (C := AddCommGrpCat.{u}) (X := X) x
          haveI : Mono (FT.map S'.f) := Functor.map_mono FT S'.f
          rw [AddCommGrpCat.mono_iff_injective] at this
          exact this ((hstalk_zero _).trans (map_zero _).symm)
      have hS₃_eq : S.X₃ = S'.X₂ := rfl
      rw [hS₃_eq]
      exact subsingleton_sheafH_of_shortExact_middle hSE' m hKer hPush
    -- Step 5: Middle-term LES gives H^m(R) = 0
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
    -- If V = ⊥, then zeroOutsideInt ⊥ is zero, so G is zero (epi image of zero)
    have hZero : IsZero G := (isZero_zeroOutsideInt_bot X).of_epi f
    exact subsingleton_sheafH_of_isZero' G hZero m
  · -- V ≠ ⊥: use kernel-cokernel SES  0 → ker f → zeroOutsideInt V → G → 0
    let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
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
theorem cohomology_vanishing_of_finitelyGenerated_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    (K : TopCat.Sheaf AddCommGrpCat.{u} X) (m : ℕ)
    (hfg : ∀ (S : Finset (TopCat.Sheaf.SectionIndex K))
      [HasCoproduct fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1],
      Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf S) m)) :
    Subsingleton (Sheaf.H K m) := by
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
  Sigma.desc fun σ =>
    Sigma.ι (fun τ : {τ // τ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1)
      ⟨σ.1, Finset.mem_insert_of_mem σ.2⟩

/-- Mono from `image(S')` to `image(insert σ₀ S')` via coproduct inclusion. -/
private noncomputable def imageIncl
    {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K} (hσ₀ : σ₀ ∉ S')
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    TopCat.Sheaf.finsetGeneratedSheaf S' ⟶ TopCat.Sheaf.finsetGeneratedSheaf (insert σ₀ S') :=
  Limits.image.lift
    { I := TopCat.Sheaf.finsetGeneratedSheaf (insert σ₀ S')
      m := Limits.image.ι _
      e := finsetCoproductIncl hσ₀ ≫ factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S'))
      fac := by
        rw [Category.assoc, Limits.image.fac]
        ext ⟨σ, hσ⟩
        simp [finsetCoproductIncl, TopCat.Sheaf.finsetGeneratorMap, TopCat.Sheaf.familyGeneratorMap] }

private instance imageIncl_mono
    {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K} (hσ₀ : σ₀ ∉ S')
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Mono (imageIncl hσ₀ : TopCat.Sheaf.finsetGeneratedSheaf S' ⟶ _) := by
  have h : imageIncl hσ₀ ≫ Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) =
      Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S') := Limits.image.lift_fac _
  exact mono_of_mono_fac h

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
  -- Define projection: coproduct over (insert σ₀ S') → zeroOutsideInt σ₀.1
  let proj : (∐ fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟶
      TopCat.Sheaf.zeroOutsideInt σ₀.1 :=
    Sigma.desc fun σ =>
      if h : σ.1 = σ₀ then
        eqToHom (by rw [h])
      else 0
  -- Key: finsetCoproductIncl ≫ factorThruImage = factorThruImage S' ≫ imageIncl
  have heq : finsetCoproductIncl hσ₀ ≫
      factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) =
    factorThruImage (TopCat.Sheaf.finsetGeneratorMap S') ≫ imageIncl hσ₀ := by
    apply (cancel_mono (Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')))).1
    rw [Category.assoc, Limits.image.fac]
    have hlf : imageIncl hσ₀ ≫ Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) =
        Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S') := Limits.image.lift_fac _
    rw [Category.assoc, hlf, Limits.image.fac]
    ext ⟨σ', hσ'⟩
    simp [finsetCoproductIncl, TopCat.Sheaf.finsetGeneratorMap, TopCat.Sheaf.familyGeneratorMap]
  -- Factorization: proj ≫ target = factorThruImage ≫ cokernel.π
  have hfac : proj ≫
      (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1)
        ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
      factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π (imageIncl hσ₀)) =
    factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π (imageIncl hσ₀) := by
    ext ⟨σ, hσ⟩
    simp only [proj, Category.assoc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    by_cases h : σ = σ₀
    · subst h; simp
    · -- LHS: ι ⟨σ,hσ⟩ ≫ desc ≫ ι ⟨σ₀,...⟩ ≫ factorThruImage ≫ cokernel.π
      -- First reassociate to get (ι ⟨σ,hσ⟩ ≫ desc) ≫ ...
      rw [← Category.assoc
        (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟨σ, hσ⟩)
        (Sigma.desc _)]
      rw [colimit.ι_desc, Cofan.mk_ι_app, dif_neg h, zero_comp]
      -- Now goal: 0 = ι ⟨σ,hσ⟩ ≫ factorThruImage ≫ cokernel.π
      symm
      have hσ' : σ ∈ S' := Finset.mem_of_mem_insert_of_ne hσ h
      have hι : Sigma.ι (fun τ : {τ // τ ∈ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, hσ'⟩ ≫
          finsetCoproductIncl hσ₀ =
        Sigma.ι (fun τ : {τ // τ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, hσ⟩ := by
        simp [finsetCoproductIncl]
      rw [← hι, Category.assoc, reassoc_of% heq]
      simp [cokernel.condition]
  exact epi_of_epi_fac hfac

/-- **Step 3B–3C**: vanishing for `finsetGeneratedSheaf S` by `Finset.induction`.
    Empty set: image = 0. Insert: SES `0 → image(S') → image(S) → cokernel → 0` where
    cokernel is epi image of `Z_{σ₀.1}`, so `hzero` + middle-term LES close the step. -/
theorem finsetGeneratedSheaf_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    (m : ℕ)
    (hzero : ∀ {G : TopCat.Sheaf AddCommGrpCat.{u} X} {V : Opens X}
      (f : TopCat.Sheaf.zeroOutsideInt V ⟶ G), Epi f → Subsingleton (Sheaf.H G m))
    (S : Finset (TopCat.Sheaf.SectionIndex K))
    [HasCoproduct fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf S) m) := by
  suffices h : ∀ (T : Finset (TopCat.Sheaf.SectionIndex K)),
      Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf T) m) from h S
  intro T
  induction T using Finset.induction with
  | empty =>
    -- finsetGeneratedSheaf ∅ is the image of a map from the empty coproduct, which is zero
    apply subsingleton_sheafH_of_isZero'
    apply IsZero.of_iso (isZero_zero _) (imageZero' _)
    apply Sigma.hom_ext; intro ⟨σ, hσ⟩; simp at hσ
  | @insert σ₀ S' hσ₀ ih =>
    -- SES: 0 → finsetGeneratedSheaf S' → finsetGeneratedSheaf (insert σ₀ S') → cokernel → 0
    haveI : Mono (imageIncl hσ₀) := imageIncl_mono hσ₀
    let SC := ShortComplex.mk (imageIncl hσ₀) (cokernel.π (imageIncl hσ₀))
      (cokernel.condition _)
    have hSE : SC.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) inferInstance inferInstance
    -- Cokernel vanishing: the σ₀-component maps epi onto it
    have hCoker : Subsingleton (Sheaf.H SC.X₃ m) := by
      haveI := imageIncl_cokernel_epi hσ₀
      exact hzero (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} =>
            TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
          factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
          cokernel.π (imageIncl hσ₀)) inferInstance
    exact subsingleton_sheafH_of_shortExact_middle hSE m ih hCoker

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
    (fun S _ => finsetGeneratedSheaf_vanishing m hzero S)

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

