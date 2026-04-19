/-
  SheafStalkAlgebra.lean — Stalk algebra for sheaves of abelian groups

  Split from IrreducibleStep.lean. Contains:
  - Stalk surjectivity for zeroOutside_openHom / sheafifyMap (any presheaf, not just constZ)
  - zeroOutsideInt cohomology vanishing (zeroOutsideInt_cohomology_vanishing)
  - isZero_zeroOutsideInt_bot: zeroOutsideInt ⊥ is zero
  - stalk_zeroOutsideInt_zero_outside: stalks vanish outside support
  - exists_nonzero_stalk_in_V: nonzero subsheaf has nonzero stalk in V
  - stalk_zeroOutsideInt_eq_zsmul_generator: stalks are Z-multiples of generator
  - ulift_int_subgroup_cyclic: cyclic subgroup classification
  - zsmul_generator_injective: injectivity of the ℤ-scalar action on the generator
-/
import Aristotle.GrothendieckVanishing.main.ClosedImmersionCohomology
import Aristotle.GrothendieckVanishing.main.ConstantSheafFlasque
import Aristotle.GrothendieckVanishing.main.FiniteGeneratorReduction

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-- **Step 5** (Hartshorne III.2.7): given vanishing of the cokernel of
    `openHom(V ≤ ⊤)` at degree `m`, deduce vanishing of `zeroOutsideInt V` at
    degree `m + 1`. Uses the SES `0 → zeroOutsideInt V → zeroOutsideInt ⊤ → cokernel → 0`
    where `zeroOutsideInt ⊤ = Z_X` (constant sheaf, flasque on irreducible spaces). -/
theorem zeroOutsideInt_vanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (m : ℕ)
    (hCoker : Subsingleton (Sheaf.H (Limits.cokernel
      (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤))) m)) :
    Subsingleton (Sheaf.H (TopCat.Sheaf.zeroOutsideInt V) (m + 1)) := by
  let f := TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤)
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hSE : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)) inferInstance inferInstance
  haveI : IsFlasqueSheaf S.X₂ := by
    constructor; intro U W i
    let J := Opens.grothendieckTopology (T := X)
    let A := AddCommGrpCat.of (ULift.{u} ℤ)
    let α : TopCat.Presheaf.constZ.zeroOutside (⊤ : Opens X) ≅
        (CategoryTheory.Functor.const (Opens X)ᵒᵖ).obj A :=
      CategoryTheory.NatIso.ofComponents
        (fun W => eqToIso (by show _ = A; simp [TopCat.Presheaf.zeroOutside, TopCat.Presheaf.constZ, A]))
        (by intro W₁ W₂ f; simp [TopCat.Presheaf.zeroOutside, TopCat.Presheaf.constZ, A])
    have h := constantSheaf_flasque_of_irreducible X A i
    exact @epi_of_epi_fac _ _ _ _ _ _ _ _ (epi_comp' h (IsIso.epi_of_iso _))
      (((sheafToPresheaf J AddCommGrpCat.{u}).mapIso
        ((presheafToSheaf J AddCommGrpCat.{u}).mapIso α).symm).hom.naturality i.op).symm
  exact ext_dimension_shift _ hSE m hCoker (FlasqueVanishing X S.X₂ m)

/-- The presheaf stalk map of `zeroOutside_openHom h` at `x ∈ V` is surjective:
    any germ in the larger zero-outside presheaf can be lifted by restricting to `W ∩ V ≤ V`
    where the presheaf map is `eqToHom` (identity). -/
theorem zeroOutside_openHom_stalk_surj
    {X : TopCat.{u}} {F : TopCat.Presheaf AddCommGrpCat.{u} X}
    {V U : Opens X} (h : V ≤ U) (x : X) (hx : x ∈ V) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (TopCat.Presheaf.zeroOutside_openHom (F := F) h))) := by
  intro g; obtain ⟨W, hxW, s, rfl⟩ := (F.zeroOutside U).germ_exist x g
  -- Restrict to W ⊓ V, where both presheaves agree with F
  set WV := W ⊓ V
  have hWV_le_V : WV ≤ V := inf_le_right
  have hWV_le_W : WV ≤ W := inf_le_left
  have hxWV : x ∈ WV := ⟨hxW, hx⟩
  -- On WV, openHom is an iso (eqToHom)
  have happ_iso : IsIso ((TopCat.Presheaf.zeroOutside_openHom
    (F := F) h).app (op WV)) := by
    simp only [TopCat.Presheaf.zeroOutside_openHom, hWV_le_V, ↓reduceDIte]; infer_instance
  -- Use the iso to find a preimage of the restricted section
  let s_res := ConcreteCategory.hom
    ((F.zeroOutside U).map (homOfLE hWV_le_W).op) s
  have h_bij := ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.zeroOutside_openHom (F := F) h).app (op WV))
  obtain ⟨t, ht⟩ := h_bij.2 s_res
  refine ⟨(F.zeroOutside V).germ WV x hxWV t, ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change (F.zeroOutside U).germ WV x hxWV
    ((TopCat.Presheaf.zeroOutside_openHom (F := F) h).app (op WV) t) =
    (F.zeroOutside U).germ W x hxW s
  rw [ht]; simp only [s_res]
  convert ((F.zeroOutside U).germ_res_apply
    (homOfLE hWV_le_W) x hxWV s) using 1

/-- The sheaf stalk map of `sheafifyMap(zeroOutside_openHom h)` at `x ∈ V` is surjective.
    Transfers presheaf stalk surjectivity via `toSheafify_naturality` and
    the fact that `stalk(toSheafify)` is an isomorphism. -/
theorem sheafifyMap_zeroOutside_openHom_stalk_surj
    {X : TopCat.{u}} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    {V U : Opens X} (h : V ≤ U) (x : X) (hx : x ∈ V) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (sheafifyMap (Opens.grothendieckTopology (T := X))
          (TopCat.Presheaf.zeroOutside_openHom (F := F) h)))) := by
  let J := Opens.grothendieckTopology (T := X)
  let φ := TopCat.Presheaf.zeroOutside_openHom (F := F) h
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hnat : T.map φ ≫ T.map (toSheafify J _) =
    T.map (toSheafify J _) ≫ T.map (sheafifyMap J φ) := by
    rw [← T.map_comp, ← T.map_comp, toSheafify_naturality]
  haveI : IsIso (T.map (toSheafify J (F.zeroOutside V))) :=
    stalkFunctor_map_iso_toSheafify _ x
  haveI : IsIso (T.map (toSheafify J (F.zeroOutside U))) :=
    stalkFunctor_map_iso_toSheafify _ x
  intro g; obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map (toSheafify J _))).2 g
  obtain ⟨p, hp⟩ := zeroOutside_openHom_stalk_surj h x hx q
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
  obtain ⟨b, rfl⟩ := ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
    (cokernel.π f).val).mp ((Sheaf.isLocallySurjective_iff_epi'
    (φ := cokernel.π f)).mpr inferInstance)) x a
  obtain ⟨c, rfl⟩ := hf b
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    show f.val ≫ (cokernel.π f).val = 0 from
      congr_arg Sheaf.Hom.val (cokernel.condition f)]
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.germ_exist F.val x c
  simp

/-! ## Sub-lemmas for Hartshorne III.2.7 Steps 3-5

These lemmas decompose the kernel vanishing argument.
`exists_good_section` is in `IrreducibleStep.lean`.
`sheafH_preserves_filtered_colimits` and `cohomology_vanishing_of_finitelyGenerated_vanishing`
are in `FiniteGeneratorReduction.lean`.
-/

/-- **Step 5** (Hartshorne III.2.7): `zeroOutsideInt V` has vanishing cohomology in every
    degree `m > dim X` on an irreducible Noetherian space.
    Proof: write `m = m' + 1`, apply `zeroOutsideInt_vanishing` (SES + flasque), then prove
    cokernel vanishing at `m'` via `closedImmersionSES` on `Vᶜ` + `PushforwardHVanishing`. -/
theorem zeroOutsideInt_cohomology_vanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (hV : V ≠ ⊥)
    (ih : VanishingIH.{u} (topologicalKrullDim X))
    (m : ℕ) (hm : m > topologicalKrullDim X) :
    Subsingleton (Sheaf.H (TopCat.Sheaf.zeroOutsideInt V) m) := by
  -- m ≠ 0 (since m > dim X ≥ 0), write m = m' + 1
  have hm_ne : m ≠ 0 := by
    intro h; subst h; exact absurd hm (not_lt.mpr topologicalKrullDim_nonneg)
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne
  -- Step 2: apply zeroOutsideInt_vanishing, reducing to cokernel vanishing at m'
  apply zeroOutsideInt_vanishing V m'
  -- Goal: Subsingleton (Sheaf.H (Limits.cokernel (openHom le_top)) m')
  -- Cokernel vanishing at m': dim Vᶜ < dim X ≤ m' (since m'+1 > dim X > 0)
  set C := Limits.cokernel (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤))
  set Y := (V : Set X)ᶜ with hY_def
  have hYcl : IsClosed Y := V.2.isClosed_compl
  have hY_dim_lt : topologicalKrullDim Y < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl
      (Set.compl_ne_univ.mpr (Set.nonempty_iff_ne_empty.mpr (Opens.coe_eq_empty.not.mpr hV)))
      (lt_of_le_of_lt (topologicalKrullDim_subspace_le (X := (↑X : Type u)) Y)
        (lt_of_lt_of_le hm le_top))
  have hm'_Y : ↑m' > topologicalKrullDim (TopCat.of Y) :=
    lt_coe_nat_of_lt_of_lt_coe_nat_succ hY_dim_lt hm
  -- Build SES on Vᶜ, apply middle-term vanishing
  let S := closedImmersionSES Y hYcl C
  have hSE := closedImmersionSES_shortExact Y hYcl C
  exact subsingleton_sheafH_of_shortExact_middle hSE m'
    (by apply Ext.subsingleton_of_isZero_tgt; apply sheaf_isZero_of_zero_stalks X; intro x a
        by_cases hxY : x ∈ Y
        · haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val) :=
            closedIncl_unit_stalk_isIso hYcl C ⟨x, hxY⟩
          exact stalk_zero_of_ses_g_iso hSE x inferInstance a
        · exact stalk_zero_of_shortExact_kernel hSE x
            (cokernel_stalk_zero_of_stalk_surj _ x
              (sheafifyMap_zeroOutside_openHom_stalk_surj Presheaf.constZ le_top x (by rwa [hY_def, Set.mem_compl_iff, not_not] at hxY))) a)
    (PushforwardHVanishing Y hYcl _ m' (ih (TopCat.of Y) m' _ hY_dim_lt hm'_Y))


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
  haveI := AddCommGrpCat.subsingleton_of_isZero
    (TopCat.Presheaf.zeroOutside_isZero (F := TopCat.Presheaf.constZ) (fun h => hx (h hxW)))
  simp [Subsingleton.eq_zero s, map_zero]

/-- `zeroOutsideInt ⊥` is the zero sheaf (all stalks vanish). -/
theorem isZero_zeroOutsideInt_bot (X : TopCat.{u}) :
    IsZero (TopCat.Sheaf.zeroOutsideInt (⊥ : Opens X)) :=
  sheaf_isZero_of_zero_stalks X _ fun x a =>
    stalk_zeroOutsideInt_zero_outside ⊥ x (Opens.mem_bot.not.mpr (fun h => h.elim)) a

/-- A nonzero subsheaf of `zeroOutsideInt V` has a nonzero stalk at some point of `V`. -/
theorem exists_nonzero_stalk_in_V
    {X : TopCat.{u}} (V : Opens X)
    (R : TopCat.Sheaf AddCommGrpCat.{u} X)
    (i : R ⟶ TopCat.Sheaf.zeroOutsideInt V) [Mono i]
    (hR : ¬ IsZero R) :
    ∃ (x : X) (_ : x ∈ V)
      (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj R.val),
      a ≠ 0 := by
  by_contra! h; apply hR
  apply sheaf_isZero_of_zero_stalks; intro x a
  by_cases hx : (x : X) ∈ (V : Set X)
  · exact h x hx a
  · haveI := TopCat.Presheaf.stalkFunctor_preserves_mono
      (C := AddCommGrpCat.{u}) (X := X) x
    exact (AddCommGrpCat.mono_iff_injective _).mp (Functor.map_mono
      (TopCat.Sheaf.forget _ _ ⋙ TopCat.Presheaf.stalkFunctor _ x) i)
      ((stalk_zeroOutsideInt_zero_outside V x hx _).trans (map_zero _).symm)

/-- At a point inside the support open, every stalk element of the presheaf `constZ.zeroOutside V`
    is an integer multiple of the germ of the distinguished generator over `V`. -/
-- The restricted generator of `constZ.zeroOutside V` maps to `1` under `eqToHom`.
private theorem resGen_eqToHom_eq_one
    {X : TopCat.{u}} (V : Opens X) {W : Opens X} (hWV : W ≤ V)
    (hObjW : (TopCat.Presheaf.constZ.zeroOutside V).obj (op W) =
        AddCommGrpCat.of (ULift ℤ)) :
    (AddCommGrpCat.Hom.hom (eqToHom hObjW))
      (ConcreteCategory.hom ((TopCat.Presheaf.constZ.zeroOutside V).map (homOfLE hWV).op)
        (TopCat.Presheaf.zeroOutside.generator V)) = (1 : ULift ℤ) := by
  unfold TopCat.Presheaf.zeroOutside.generator
  simp only [TopCat.Presheaf.zeroOutside_map, dif_pos hWV, dif_pos (le_refl V),
    ← ConcreteCategory.comp_apply, ← CategoryTheory.comp_apply, eqToHom_trans,
    Functor.const_obj_map, Category.id_comp]
  simp [show hObjW.symm.trans hObjW = rfl from Subsingleton.elim _ _]

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
    have hgenW_val : (AddCommGrpCat.Hom.hom (eqToHom hObjW)) genW = (1 : ULift ℤ) :=
      resGen_eqToHom_eq_one V hWV hObjW
    -- eqToHom is injective (it's an iso)
    have hinj : Function.Injective (AddCommGrpCat.Hom.hom (eqToHom hObjW)) :=
      (ConcreteCategory.bijective_of_isIso (eqToHom hObjW)).1
    -- s = w.down • genW
    have hs_zsmul : s = w.down • genW := by
      apply hinj
      rw [map_zsmul, hgenW_val]
      show w = w.down • (1 : ULift ℤ); ext; simp
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
    exact ⟨0, by simp [Subsingleton.eq_zero s, map_zero]⟩

/-- At a point inside the support open, every stalk element of `zeroOutsideInt V` is an integer
    multiple of the germ of the distinguished generator over `V`. -/
theorem stalk_zeroOutsideInt_eq_zsmul_generator
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
  rw [hn, map_zsmul]; congr 1
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply V x hx
    (toSheafify J P) (TopCat.Presheaf.zeroOutside.generator V)

/-- Every nonzero subgroup of `ULift ℤ` is generated by its smallest positive element.
    Derived from `Int.subgroup_cyclic` (Mathlib). -/
theorem ulift_int_subgroup_cyclic
    (H : AddSubgroup (ULift.{u} ℤ)) (hH : H ≠ ⊥) :
    ∃ d : ULift.{u} ℤ, d ∈ H ∧ d.down > 0 ∧
      ∀ h ∈ H, ∃ k : ℤ, h = ⟨k * d.down⟩ := by
  -- Transfer to ℤ via AddEquiv.ulift and apply Int.subgroup_cyclic
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic (H.map AddEquiv.ulift.toAddMonoidHom)
  have ha_ne : a ≠ 0 := by
    intro heq; apply hH; rw [eq_bot_iff]; intro x hx; rw [AddSubgroup.mem_bot]
    have hx' := AddSubgroup.mem_map_of_mem AddEquiv.ulift.toAddMonoidHom hx
    rw [ha, heq, AddSubgroup.closure_singleton_zero, AddSubgroup.mem_bot] at hx'
    exact AddEquiv.ulift.injective (hx'.trans (map_zero _).symm)
  have ha_mem : (⟨a⟩ : ULift.{u} ℤ) ∈ H := by
    have : a ∈ H.map AddEquiv.ulift.toAddMonoidHom :=
      ha ▸ AddSubgroup.subset_closure rfl
    obtain ⟨y, hy, hey⟩ := AddSubgroup.mem_map.mp this
    rwa [show y = ⟨a⟩ from by ext; exact hey] at hy
  refine ⟨⟨|a|⟩, ?_, abs_pos.mpr ha_ne, fun h hh => ?_⟩
  · by_cases hle : 0 ≤ a
    · rwa [abs_of_nonneg hle]
    · push_neg at hle; rw [abs_of_neg hle]; exact H.neg_mem ha_mem
  · have hx' := AddSubgroup.mem_map_of_mem AddEquiv.ulift.toAddMonoidHom hh
    rw [ha, AddSubgroup.mem_closure_singleton] at hx'
    obtain ⟨n, hn⟩ := hx'; rw [zsmul_eq_mul] at hn
    by_cases hle : 0 ≤ a
    · exact ⟨n, ULift.ext _ _ (by rw [abs_of_nonneg hle]; exact hn.symm)⟩
    · push_neg at hle
      exact ⟨-n, ULift.ext _ _ (by rw [abs_of_neg hle, neg_mul_neg]; exact hn.symm)⟩

/-- The map `n ↦ n • gen` from `ℤ` into `stalk(zeroOutsideInt V, x)` is injective
    for `x ∈ V`. -/
theorem zsmul_generator_injective
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V) :
    Function.Injective (fun (n : ℤ) =>
      n • ((TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V x hx
        (TopCat.Sheaf.zeroOutsideInt.generator V))) := by
  intro n m h
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
  set gen_P := TopCat.Presheaf.zeroOutside.generator V
  have h' : P.germ V x hx (n • gen_P) = P.germ V x hx (m • gen_P) := by
    rw [map_zsmul, map_zsmul]
    apply hbij.1; simp only [map_zsmul, hgen_eq]; exact h
  -- Use germ_eq: equal germs agree on a refinement W ≤ V
  obtain ⟨W, hxW, iU, iV, hEq⟩ := P.germ_eq x hx hx _ _ h'
  rw [Subsingleton.elim iU iV, map_zsmul, map_zsmul] at hEq
  have hWV : W ≤ V := leOfHom iV
  rw [Subsingleton.elim iV (homOfLE hWV)] at hEq
  -- P.obj(op W) = ULift ℤ since W ≤ V
  have hObjW : P.obj (op W) = AddCommGrpCat.of (ULift ℤ) := by
    simp [P, TopCat.Presheaf.zeroOutside, hWV, TopCat.Presheaf.constZ]
  -- The restricted generator maps to 1 in ULift ℤ
  set resGen := ConcreteCategory.hom (P.map (homOfLE hWV).op) gen_P
  have hresGen_val : (AddCommGrpCat.Hom.hom (eqToHom hObjW)) resGen = (1 : ULift ℤ) :=
    resGen_eqToHom_eq_one V hWV hObjW
  -- Transfer hEq to ULift ℤ and extract n = m
  have hEq_ULift : n • (1 : ULift ℤ) = m • (1 : ULift ℤ) := by
    have := congrArg (AddCommGrpCat.Hom.hom (eqToHom hObjW)) hEq
    rwa [map_zsmul, map_zsmul, hresGen_val] at this
  simpa using congrArg ULift.down hEq_ULift
