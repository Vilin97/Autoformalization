/-
  StalkGeneratorAlgebra.lean — Stalk algebra and generator properties

  Split from SheafStalkAlgebra.lean. Contains:
  - isZero_zeroOutsideInt_bot: zeroOutsideInt ⊥ is zero
  - stalk_zeroOutsideInt_zero_outside: stalks vanish outside support
  - exists_nonzero_stalk_in_V: nonzero subsheaf has nonzero stalk in V
  - sheaf_mono_of_stalk_injective: stalk injectivity → mono
  - stalk_zeroOutsideInt_eq_zsmul_generator: stalks are Z-multiples of generator
  - ulift_int_subgroup_cyclic: cyclic subgroup classification
  - zsmul_generator_injective: generator coefficient uniqueness
-/
import Aristotle.GrothendieckVanishing.main.SheafStalkAlgebra

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

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
  · haveI := TopCat.Presheaf.stalkFunctor_preserves_mono
      (C := AddCommGrpCat.{u}) (X := X) x
    let FT := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    exact (AddCommGrpCat.mono_iff_injective _).mp (Functor.map_mono FT i)
      ((stalk_zeroOutsideInt_zero_outside V x hx _).trans (map_zero _).symm)

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
    ∃ n : ℤ, H = AddSubgroup.zmultiples n :=
  (Int.subgroup_cyclic H).imp fun _ hn => by simpa [AddSubgroup.zmultiples_eq_closure] using hn

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
    refine ⟨0, ?_⟩
    simp [Subsingleton.eq_zero s, map_zero]

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
  rw [hn, map_zsmul]
  congr 1
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply V x hx
    (toSheafify J P) (TopCat.Presheaf.zeroOutside.generator V)

/-- Every nonzero subgroup of `ULift ℤ` is generated by its smallest positive element.
    Proved by Aristotle (job 5bca8de6). -/
theorem ulift_int_subgroup_cyclic
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
theorem zsmul_generator_injective
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
  set gen_P := TopCat.Presheaf.zeroOutside.generator V
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
  set resGen := ConcreteCategory.hom (P.map (homOfLE hWV).op) gen_P
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
  -- Transfer hEq to ULift ℤ and extract n = m
  have hEq_ULift : n • (1 : ULift ℤ) = m • (1 : ULift ℤ) := by
    have := congrArg (AddCommGrpCat.Hom.hom (eqToHom hObjW)) hEq
    rwa [map_zsmul, map_zsmul, hresGen_val] at this
  have := congrArg ULift.down hEq_ULift
  simp at this; exact this
