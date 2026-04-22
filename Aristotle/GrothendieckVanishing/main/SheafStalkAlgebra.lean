import Aristotle.GrothendieckVanishing.main.CohomologyAPI
import Aristotle.GrothendieckVanishing.main.ClosedImmersionCohomology
import Aristotle.GrothendieckVanishing.main.ConstantSheafFlasque
import Aristotle.GrothendieckVanishing.main.FiniteGeneratorReduction
import Aristotle.GrothendieckVanishing.main.ZeroOutside

/-!
  SheafStalkAlgebra.lean — Stalk algebra for sheaves of abelian groups

  Split from IrreducibleStep.lean. Contains:
  - zeroOutsideInt cohomology vanishing (zeroOutsideInt_cohomology_vanishing)
  - isZero_zeroOutsideInt_bot: zeroOutsideInt ⊥ is zero
  - exists_nonzero_stalk_in_V: nonzero subsheaf has nonzero stalk in V
  - stalk_zeroOutsideInt_eq_zsmul_generator: stalks are Z-multiples of generator
  - ulift_int_subgroup_cyclic: cyclic subgroup classification
  - zsmul_generator_injective: injectivity of the ℤ-scalar action on the generator
-/

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
  have hfsh : Mono (TopCat.Sheaf.zeroOutsideInt.openHom
      (le_top : V ≤ (⊤ : Opens X))) := by
    infer_instance
  haveI : Mono ((TopCat.Sheaf.zeroOutsideInt.openHom
      (le_top : V ≤ (⊤ : Opens X))).val) := by
    exact (Sheaf.Hom.mono_iff_presheaf_mono
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u})
      (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ (⊤ : Opens X)))).1 hfsh
  have hTop : Subsingleton (Sheaf.H (TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X)) (m + 1)) := by
    let F : TopCat.Presheaf AddCommGrpCat.{u} X :=
      (TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X)).val
    have hF : F.IsSheaf := by
      simpa [F] using (TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X)).cond
    letI : IsFlasqueSheaf ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
      simpa [F, hF] using isFlasqueSheaf_zeroOutsideInt_top X
    simpa [F, hF] using
      (sheafH_subsingleton_of_flasque_presheaf (X := X) (F := F) hF m)
  exact sheafH_dimension_shift_of_mono_presheaf
    (F := (TopCat.Sheaf.zeroOutsideInt V).val)
    (G := (TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X)).val)
    (hF := (TopCat.Sheaf.zeroOutsideInt V).cond)
    (hG := (TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X)).cond)
    (f := (TopCat.Sheaf.zeroOutsideInt.openHom
      (le_top : V ≤ (⊤ : Opens X))).val)
    (n := m)
    hCoker hTop

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
  let C := Limits.cokernel (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤))
  -- m ≠ 0 (since m > dim X ≥ 0), write m = m' + 1
  have hm_ne : m ≠ 0 := by
    intro h; subst h; exact absurd hm (not_lt.mpr topologicalKrullDim_nonneg)
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne
  have hVcompl_lt_succ :
      topologicalKrullDim (Set.compl (V : Set X)) < ↑↑(m' + 1 : ℕ) :=
    topologicalKrullDim_subspace_lt_of_lt (X := X) (Set.compl (V : Set X))
      (by simpa [gt_iff_lt] using hm)
  have hVcompl_lt_top : topologicalKrullDim (Set.compl (V : Set X)) < ⊤ :=
    topologicalKrullDim_lt_top_of_lt_nat hVcompl_lt_succ
  have hVcompl_lt_X : topologicalKrullDim (Set.compl (V : Set X)) < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed
      V.2.isClosed_compl
      (Set.compl_ne_univ.mpr (Set.nonempty_iff_ne_empty.mpr
        (Opens.coe_eq_empty.not.mpr hV)))
      hVcompl_lt_top
  have hVcompl_lt_m' : topologicalKrullDim (Set.compl (V : Set X)) < ↑↑(m' : ℕ) :=
    topologicalKrullDim_lt_nat_of_lt_of_lt_nat_succ hVcompl_lt_X
      (by simpa [gt_iff_lt] using hm)
  -- Step 2: apply zeroOutsideInt_vanishing, reducing to cokernel vanishing at m'
  apply zeroOutsideInt_vanishing V m'
  -- Cokernel vanishing at m': use closedComplementVanishing with m' > dim Vᶜ
  exact closedComplementVanishing V hV (C := C.val) C.cond m' ih
    (by simpa [gt_iff_lt] using hVcompl_lt_m')
    (fun x hxV a => cokernel_stalk_zero_of_stalk_surj
      (F := (TopCat.Sheaf.zeroOutsideInt V).val)
      (G := (TopCat.Sheaf.zeroOutsideInt ⊤).val)
      (hF := (TopCat.Sheaf.zeroOutsideInt V).cond)
      (hG := (TopCat.Sheaf.zeroOutsideInt ⊤).cond)
      (f := (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤)).val)
      (x := x)
      (hf := sheafifyMap_zeroOutside_openHom_stalk_surj Presheaf.constZ le_top x hxV) a)

/-- `zeroOutsideInt ⊥` is the zero sheaf (all stalks vanish). -/
theorem isZero_zeroOutsideInt_bot (X : TopCat.{u}) :
    IsZero (TopCat.Sheaf.zeroOutsideInt (⊥ : Opens X)) := by
  let F := TopCat.Sheaf.zeroOutsideInt (⊥ : Opens X)
  have hF_zero : IsZero ((⟨F.val, F.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) :=
    sheaf_isZero_of_zero_stalks X F.cond (fun x a =>
      stalk_zeroOutsideInt_zero_outside ⊥ x (Opens.mem_bot.not.mpr (fun h => h.elim)) a)
  simpa [F] using hF_zero

/-- A nonzero subsheaf of `zeroOutsideInt V` has a nonzero stalk at some point of `V`. -/
theorem exists_nonzero_stalk_in_V
    {X : TopCat.{u}} (V : Opens X)
    {R : TopCat.Presheaf AddCommGrpCat.{u} X} (hRsh : R.IsSheaf)
    (i : R ⟶ (TopCat.Sheaf.zeroOutsideInt V).val)
    [Mono i]
    (hR : ¬ IsZero R) :
    ∃ (x : X) (_ : x ∈ V)
      (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj R),
      a ≠ 0 := by
  let Rsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨R, hRsh⟩
  by_contra! h; apply hR
  have hRsh_zero : IsZero Rsh :=
    sheaf_isZero_of_zero_stalks X hRsh (fun x a => by
      by_cases hx : (x : X) ∈ (V : Set X)
      · exact h x hx a
      · have hi_inj : Function.Injective
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map i) :=
          TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective (f := i)
            (fun U =>
              (ConcreteCategory.mono_iff_injective_of_preservesPullback (i.app (op U))).mp
                ((NatTrans.mono_iff_mono_app i).mp inferInstance (op U))) x
        exact hi_inj ((stalk_zeroOutsideInt_zero_outside V x hx _).trans (map_zero _).symm)
      )
  refine Functor.isZero R ?_
  intro U
  have hforget_eval :
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U).PreservesZeroMorphisms := by
    refine ⟨?_⟩
    intro A B
    rfl
  simpa using Functor.map_isZero
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U) hRsh_zero

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
  obtain ⟨n, hn⟩ :=
    TopCat.Presheaf.zeroOutside.presheaf_stalk_zeroOutside_eq_zsmul_generator V x hx q
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
    TopCat.Presheaf.zeroOutside.resGen_eqToHom_eq_one V hWV hObjW
  -- Transfer hEq to ULift ℤ and extract n = m
  have hEq_ULift : n • (1 : ULift ℤ) = m • (1 : ULift ℤ) := by
    have := congrArg (AddCommGrpCat.Hom.hom (eqToHom hObjW)) hEq
    rwa [map_zsmul, map_zsmul, hresGen_val] at this
  simpa using congrArg ULift.down hEq_ULift
