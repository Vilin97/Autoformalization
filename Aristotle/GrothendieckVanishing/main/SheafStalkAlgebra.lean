/-
  SheafStalkAlgebra.lean — Stalk algebra for sheaves of abelian groups

  Split from IrreducibleStep.lean. Contains:
  - Stalk surjectivity/bijectivity for zeroOutsideInt
  - zeroOutsideInt cohomology vanishing (zeroOutsideInt_cohomology_vanishing)

  Note: stalk_zeroOutsideInt_eq_zsmul_generator, ulift_int_subgroup_cyclic,
  and zsmul_generator_injective are in StalkGeneratorAlgebra.lean.
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.ConstantSheafFlasque
import Aristotle.GrothendieckVanishing.main.FiniteGeneratorReduction

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-- **Step 5** (Hartshorne III.2.7): given vanishing of the cokernel of
    `openHom(V ≤ ⊤)` at degree `m`, deduce vanishing of `zeroOutsideInt V` at
    degree `m + 1`. Uses the SES `0 → zeroOutsideInt V → zeroOutsideInt ⊤ → cokernel → 0`
    where `zeroOutsideInt ⊤ = Z_X` (constant sheaf, flasque on irreducible spaces). -/
theorem zeroOutsideInt_vanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (m : ℕ)
    (hCoker : Subsingleton (Sheaf.H (Limits.cokernel
      (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤))) m)) :
    Subsingleton (Sheaf.H (TopCat.Sheaf.zeroOutsideInt V) (m + 1)) := by
  let f := TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤)
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hSE : S.ShortExact := shortExact_of_mono f
  have hFlasque : IsFlasqueSheaf S.X₂ := by
    intro U W i
    let J := Opens.grothendieckTopology (T := X)
    let A := AddCommGrpCat.of (ULift.{u} ℤ)
    let α : TopCat.Presheaf.constZ.zeroOutside (⊤ : Opens X) ≅
        (CategoryTheory.Functor.const (Opens X)ᵒᵖ).obj A :=
      CategoryTheory.NatIso.ofComponents
        (fun W => eqToIso (by show _ = A; simp [TopCat.Presheaf.zeroOutside, TopCat.Presheaf.constZ, A]))
        (by intro W₁ W₂ f; simp [TopCat.Presheaf.zeroOutside, TopCat.Presheaf.constZ, A])
    exact epi_of_natIso_epi ((sheafToPresheaf J AddCommGrpCat.{u}).mapIso
      ((presheafToSheaf J AddCommGrpCat.{u}).mapIso α).symm) i.op
      (constantSheaf_flasque_of_irreducible X i)
  exact ext_dimension_shift _ hSE m hCoker (FlasqueVanishing X S.X₂ hFlasque m)

/-- The presheaf stalk map of `zeroOutside_openHom h` at `x ∈ V` is surjective:
    any germ in the larger zero-outside presheaf can be lifted by restricting to `W ∩ V ≤ V`
    where the presheaf map is `eqToHom` (identity). -/
private theorem presheaf_stalk_surj_openHom
    {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) (x : X) (hx : x ∈ V) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (TopCat.Presheaf.zeroOutside_openHom (F := TopCat.Presheaf.constZ) h))) := by
  intro g; obtain ⟨W, hxW, s, rfl⟩ := (TopCat.Presheaf.constZ.zeroOutside U).germ_exist x g
  -- Restrict to W ⊓ V, where both presheaves agree with constZ
  set WV := W ⊓ V
  have hWV_le_V : WV ≤ V := inf_le_right
  have hWV_le_W : WV ≤ W := inf_le_left
  have hxWV : x ∈ WV := ⟨hxW, hx⟩
  -- On WV, openHom is an iso (eqToHom)
  have happ_iso : IsIso ((TopCat.Presheaf.zeroOutside_openHom
    (F := TopCat.Presheaf.constZ) h).app (op WV)) := by
    simp only [TopCat.Presheaf.zeroOutside_openHom, hWV_le_V, ↓reduceDIte]; infer_instance
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

/-- The sheaf stalk map of `openHom(h)` at `x ∈ V` is surjective.
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
  intro g; obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map (toSheafify J _))).2 g
  obtain ⟨p, hp⟩ := presheaf_stalk_surj_openHom h x hx q
  exact ⟨ConcreteCategory.hom (T.map (toSheafify J _)) p, by
    change ConcreteCategory.hom (T.map (sheafifyMap J φ))
      (ConcreteCategory.hom (T.map (toSheafify J _)) p) = _
    rw [← ConcreteCategory.comp_apply, hnat.symm, ConcreteCategory.comp_apply, hp]⟩

/-- Cokernel stalk vanishes at points where the map is stalk-surjective.
    Proof: `cokernel.π` is epi hence stalk-surjective, so every stalk element lifts to `G`,
    then to `F` by hypothesis; `cokernel.condition` gives zero. -/
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
  have h1 : ConcreteCategory.hom ((f.val ≫ (cokernel.π f).val).app (op U)) s = 0 := by
    rw [show f.val ≫ (cokernel.π f).val = (0 : F ⟶ cokernel f).val from
      congr_arg Sheaf.Hom.val (cokernel.condition f)]; rfl
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h1; rw [h1, map_zero]

/-- The cokernel of `openHom(le_top)` has zero stalks at points of `V`.
    Delegates to `cokernel_stalk_zero_of_stalk_surj` via `sheaf_stalk_surj_openHom`. -/
private theorem cokernel_stalk_zero_V {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (Limits.cokernel (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤))).val) :
    a = 0 :=
  cokernel_stalk_zero_of_stalk_surj _ x (sheaf_stalk_surj_openHom le_top x hx) a

/-! ## Sub-lemmas for Hartshorne III.2.7 Steps 3-5

These lemmas decompose the kernel vanishing argument.
`exists_good_section` is in `IrreducibleStep.lean`.
`sheafH_preserves_filtered_colimits` and `cohomology_vanishing_of_finitelyGenerated_vanishing`
are in `FiniteGeneratorReduction.lean`.
-/

/-- **Step 5** (Hartshorne III.2.7): `zeroOutsideInt V` has vanishing cohomology in every
    degree `m > dim X` on an irreducible Noetherian space of positive dimension.
    Proof: write `m = m' + 1`, apply `zeroOutsideInt_vanishing` (SES + flasque), then prove
    cokernel vanishing at `m'` via `ClosedImmersionSES` on `Vᶜ` + `PushforwardHVanishing`. -/
theorem zeroOutsideInt_cohomology_vanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (ih : VanishingIH (X := X))
    (hpos : topologicalKrullDim X > 0)
    (V : Opens X) (hV : V ≠ ⊥)
    (m : ℕ) (hm : m > topologicalKrullDim X) :
    Subsingleton (Sheaf.H (TopCat.Sheaf.zeroOutsideInt V) m) := by
  -- m ≠ 0 (since m > dim X > 0), write m = m' + 1
  have hm_ne : m ≠ 0 := by intro h; subst h; simp at hm; exact not_lt.mpr (le_of_lt hpos) hm
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne
  -- Step 2: apply zeroOutsideInt_vanishing, reducing to cokernel vanishing at m'
  apply zeroOutsideInt_vanishing X V m'
  -- Goal: Subsingleton (Sheaf.H (Limits.cokernel (openHom le_top)) m')
  -- Cokernel vanishing at m': dim Vᶜ < dim X ≤ m' (since m'+1 > dim X > 0)
  set C := Limits.cokernel (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤))
  set Y := (V : Set X)ᶜ with hY_def
  have hYcl : IsClosed Y := V.2.isClosed_compl
  have hY_dim_lt : topologicalKrullDim Y < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl (compl_ne_univ_of_ne_bot hV)
      (lt_of_le_of_lt (topologicalKrullDim_subspace_le (X := (↑X : Type u)) Y)
        (lt_of_lt_of_le hm le_top))
  have hm'_Y : ↑m' > topologicalKrullDim (TopCat.of Y) := by
    show topologicalKrullDim Y < ↑m'
    have hd_ne_bot : topologicalKrullDim X ≠ ⊥ := ne_bot_of_gt hpos
    lift topologicalKrullDim X to ℕ∞ using hd_ne_bot with d
    have hd_lt : (d : WithBot ℕ∞) < ↑((m'.succ : ℕ) : ℕ∞) := hm
    rw [WithBot.coe_lt_coe] at hd_lt
    have hd_ne_top : d ≠ ⊤ := ne_top_of_lt hd_lt
    lift d to ℕ using hd_ne_top with d'
    rw [ENat.coe_lt_coe] at hd_lt
    calc topologicalKrullDim Y < ↑↑d' := hY_dim_lt
      _ ≤ ↑↑m' := by exact_mod_cast Nat.lt_succ_iff.mp hd_lt
  -- Build SES on Vᶜ, apply middle-term vanishing
  let i : TopCat.of Y ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app C
  haveI : Epi η := epi_unit_of_closedImmersion Y hYcl C
  let S := ShortComplex.mk (kernel.ι η) η (kernel.condition η)
  have hSE : S.ShortExact := shortExact_of_epi η
  exact subsingleton_sheafH_of_shortExact_middle hSE m'
    (by apply Ext.subsingleton_of_isZero_tgt; apply sheaf_isZero_of_zero_stalks X; intro x a
        by_cases hxY : x ∈ Y
        · haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val) :=
            closedIncl_unit_stalk_isIso hYcl C ⟨x, hxY⟩
          exact stalk_zero_of_ses_g_iso hSE x inferInstance a
        · exact stalk_zero_of_shortExact_kernel hSE x
            (fun b => cokernel_stalk_zero_V V x (by rwa [hY_def, Set.mem_compl_iff, not_not] at hxY) b) a)
    (PushforwardHVanishing Y hYcl _ m' (@ih (TopCat.of Y) _ m' _ hY_dim_lt hm'_Y))


-- Stalk generator algebra, subgroup theory, and generator injectivity
-- are in StalkGeneratorAlgebra.lean.
