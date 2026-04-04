/-
  SheafStalkAlgebra.lean — Stalk algebra for sheaves of abelian groups

  Split from IrreducibleStep.lean. Contains:
  - Stalk surjectivity/bijectivity for zeroOutsideInt
  - Cokernel vanishing (cokernel_openHom_vanishing)
  - zeroOutsideInt cohomology vanishing (zeroOutsideInt_cohomology_vanishing)

  Note: stalk_zeroOutsideInt_eq_zsmul_generator, ulift_int_subgroup_cyclic,
  and zsmul_generator_injective are in StalkGeneratorAlgebra.lean.
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.ConstantSheafFlasque
import Aristotle.GrothendieckVanishing.main.FiniteGeneratorReduction

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

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
    -- S.X₂ = zeroOutsideInt ⊤ ≅ constantSheaf ℤ (via presheaf NatIso + sheafification)
    -- Build NatIso at presheaf level
    let J := Opens.grothendieckTopology (T := X)
    let A := AddCommGrpCat.of (ULift.{u} ℤ)
    let α : TopCat.Presheaf.constZ.zeroOutside (⊤ : Opens X) ≅
        (CategoryTheory.Functor.const (Opens X)ᵒᵖ).obj A :=
      CategoryTheory.NatIso.ofComponents
        (fun W => eqToIso (by show _ = A; simp [TopCat.Presheaf.zeroOutside, TopCat.Presheaf.constZ, A]))
        (by intro W₁ W₂ f; simp [TopCat.Presheaf.zeroOutside, TopCat.Presheaf.constZ, A])
    -- Sheafify to get sheaf iso β : S.X₂ ≅ constantSheaf(A)
    let β : S.X₂ ≅ (constantSheaf J AddCommGrpCat.{u}).obj A :=
      (presheafToSheaf J AddCommGrpCat.{u}).mapIso α
    -- β is an iso in the Sheaf category; its val is a natural iso of presheaves
    have hβ_iso : IsIso β.hom := Iso.isIso_hom β
    -- β.hom is an iso in Sheaf, so β.hom.val is iso as a nat trans
    haveI : IsIso β.hom.val :=
      (sheafToPresheaf J AddCommGrpCat.{u}).map_isIso β.hom
    haveI : IsIso (β.hom.val.app (op W)) :=
      CategoryTheory.NatIso.isIso_app_of_isIso β.hom.val (op W)
    haveI : IsIso (β.hom.val.app (op U)) :=
      CategoryTheory.NatIso.isIso_app_of_isIso β.hom.val (op U)
    -- From naturality: S.X₂.val.map i.op = inv(β_W) ≫ C.val.map i.op ≫ β_U
    have h_nat := β.hom.val.naturality i.op
    have hEpi_const := constantSheaf_flasque_of_irreducible X i
    -- S.X₂.map = β_W⁻¹ ≫ C.map ≫ β_U, so epi (iso ∘ epi ∘ iso = epi)
    have hrw : S.X₂.val.map i.op = β.hom.val.app (op W) ≫
        ((constantSheaf J AddCommGrpCat.{u}).obj A).val.map i.op ≫
        inv (β.hom.val.app (op U)) := by
      have := h_nat
      rw [← Category.assoc, ← this, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [hrw]
    haveI := constantSheaf_flasque_of_irreducible X i
    exact inferInstance
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
    (n : ℕ) (hn : n > topologicalKrullDim X) (_ : topologicalKrullDim X > 0)
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
`zeroOutsideInt_cohomology_vanishing` is proved. `exists_good_section` is proved.
`sheafH_preserves_filtered_colimits` has 1 sorry (Gabriel's theorem — true, standard).
`cohomology_vanishing_of_finitelyGenerated_vanishing` is fully proved via the filtered diagram.
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


-- Stalk generator algebra, subgroup theory, and generator injectivity
-- are in StalkGeneratorAlgebra.lean.
