import Aristotle.GrothendieckVanishing.main.ClosedImmersionCohomology
import Aristotle.GrothendieckVanishing.main.ConstantSheafFlasque
import Aristotle.GrothendieckVanishing.main.FinitelyGeneratedVanishing
import Aristotle.GrothendieckVanishing.main.FlasqueVanishing
import Aristotle.GrothendieckVanishing.main.TopologicalKrullDim
import Aristotle.GrothendieckVanishing.main.ZeroOutside

/-!
  IrreducibleStep.lean — Assembly: irreducible positive-dimension vanishing

  Key results:
  - exists_nonzero_stalk_in_V: PROVED — a nonzero subsheaf of `zeroOutsideInt V`
    has a nonzero stalk at some point of `V`
  - exists_section_generating_stalks: PROVED — uses Nat.find to choose x₀ with minimal
    image subgroup generator d, then divisibility d | d_x follows from minimality.
  - exists_good_section: PROVED — via exists_section_generating_stalks + sHom_stalk_bijective_at
  - closedComplementVanishing: Step 4/5 support lemma for sheaves supported on a closed
    complement, kept here with the irreducible-step vanishing assembly that uses it
  - zeroOutsideInt_vanishing / zeroOutsideInt_cohomology_vanishing: Step 5 vanishing
    assembled where it is consumed
  - IrreduciblePosVanishing: assembles the positive-dimensional irreducible step

  Supporting `zeroOutsideInt` stalk lemmas remain in `ZeroOutside.lean`; the
  one-off nonzero-stalk entry lemma lives here immediately before the shrinking step
  that uses it.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-- The stalk map of `sHom s` at `x ∈ U` is bijective when every stalk element of R at x
    is an integer multiple of `germ(s, x)`, and R embeds into `zeroOutsideInt V`
    (providing torsion-freeness needed for injectivity). -/
theorem sHom_stalk_bijective_at
    {X : TopCat.{u}} {V U : Opens X} (hUV : U ≤ V)
    {R : TopCat.Presheaf AddCommGrpCat.{u} X} (hRsh : R.IsSheaf)
    (i : R ⟶ (TopCat.Sheaf.zeroOutsideInt V).val) [Mono i]
    (s : R.obj (op U))
    (x : X) (hxU : x ∈ U)
    -- germ(s, x) ≠ 0 (needed for injectivity; without this, stalk(R,x) could be 0
    -- while stalk(zeroOutsideInt U, x) ≅ ℤ, making the map non-injective)
    (hs_ne : R.germ U x hxU s ≠ 0)
    -- Every stalk element of R at x is an integer multiple of germ(s, x)
    (hgen : ∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj R),
      ∃ k : ℤ, a = k • R.germ U x hxU s) :
    Function.Bijective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (TopCat.Sheaf.zeroOutsideInt.sHomVal hRsh s))) := by
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let sHom_x := ConcreteCategory.hom (T.map (TopCat.Sheaf.zeroOutsideInt.sHomVal hRsh s))
  let i_x := ConcreteCategory.hom (T.map i)
  have hi_inj : Function.Injective i_x :=
    TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective (f := i)
      (fun U =>
        (ConcreteCategory.mono_iff_injective_of_preservesPullback (i.app (op U))).mp
          ((NatTrans.mono_iff_mono_app i).mp inferInstance (op U))) x
  have hi_s_ne : i_x (R.germ U x hxU s) ≠ 0 :=
    fun h => hs_ne (hi_inj (h.trans (map_zero i_x).symm))
  obtain ⟨c, hc⟩ := stalk_zeroOutsideInt_eq_zsmul_generator V x (hUV hxU)
    (i_x (R.germ U x hxU s))
  have hc_ne : c ≠ 0 := fun hc0 => by rw [hc0, zero_smul] at hc; exact hi_s_ne hc
  have h_sHom_app :
      (TopCat.Sheaf.zeroOutsideInt.sHomVal hRsh s).app (op U)
        (TopCat.Sheaf.zeroOutsideInt.generator U) = s :=
    TopCat.Sheaf.zeroOutsideInt.sHomVal_app_generator hRsh s
  have h_sHom_gen : sHom_x ((TopCat.Sheaf.zeroOutsideInt U).presheaf.germ U x hxU
      (TopCat.Sheaf.zeroOutsideInt.generator U)) = R.germ U x hxU s := by
    show T.map (TopCat.Sheaf.zeroOutsideInt.sHomVal hRsh s) _ = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    simpa using congrArg (R.germ U x hxU) h_sHom_app
  have h_surj : Function.Surjective sHom_x := by
    intro a; obtain ⟨k, hk⟩ := hgen a
    exact ⟨k • (TopCat.Sheaf.zeroOutsideInt U).presheaf.germ U x hxU
      (TopCat.Sheaf.zeroOutsideInt.generator U), by rw [map_zsmul, h_sHom_gen, hk]⟩
  have h_inj : Function.Injective sHom_x := by
    intro a b hab
    obtain ⟨n, rfl⟩ := stalk_zeroOutsideInt_eq_zsmul_generator U x hxU a
    obtain ⟨m, rfl⟩ := stalk_zeroOutsideInt_eq_zsmul_generator U x hxU b
    simp only [map_zsmul, h_sHom_gen] at hab
    have h_i : n • i_x (R.germ U x hxU s) =
        m • i_x (R.germ U x hxU s) := by rw [← map_zsmul, ← map_zsmul, hab]
    rw [hc, smul_comm n, smul_comm m, ← mul_smul, ← mul_smul] at h_i
    rw [mul_left_cancel₀ hc_ne (zsmul_generator_injective V x (hUV hxU) h_i)]
  exact ⟨h_inj, h_surj⟩

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
  by_contra! h
  apply hR
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
        exact hi_inj ((stalk_zeroOutsideInt_zero_outside V x hx _).trans (map_zero _).symm))
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

/-- At each point `x ∈ V`, the image of the stalk of `R` under `i` is a subgroup of
    `stalk(zeroOutsideInt V, x) ≅ ULift ℤ`. Transporting to `ℤ` and applying
    `Int.subgroup_cyclic`, if this image is nonzero, it has a positive generator `d_x`.
    The "index" `d_x` measures how deeply
    `R` sits inside `zeroOutsideInt V` at `x`.

    This lemma produces `V' ≤ V`, `V' ≠ ⊥`, and `s ∈ R(V')` such that for all `x ∈ V'`:
    (1) `germ(s, x) ≠ 0`
    (2) every stalk element of `R` at `x` is an integer multiple of `germ(s, x)`.
    This is the hard "Noetherian shrinking" step of Hartshorne III.2.7, Step 4. -/
theorem exists_section_generating_stalks
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    {V : Opens X} {R : TopCat.Presheaf AddCommGrpCat.{u} X} (hRsh : R.IsSheaf)
    (i : R ⟶ (TopCat.Sheaf.zeroOutsideInt V).val)
    [Mono i]
    (hR : ¬ IsZero R) :
    ∃ (V' : Opens X) (_ : V' ≤ V) (_ : V' ≠ ⊥)
      (s : R.obj (op V')),
      ∀ (x : X) (hx : x ∈ V'),
        (R.germ V' x hx s ≠ 0) ∧
        (∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj R),
          ∃ k : ℤ, a = k • R.germ V' x hx s) := by
  let i_x (x : X) := ConcreteCategory.hom ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map i)
  have hi_inj : ∀ (x : X), Function.Injective (i_x x) := fun x =>
    Presheaf.stalkFunctor_map_injective_of_app_injective (f := i) (fun U =>
      (ConcreteCategory.mono_iff_injective_of_preservesPullback (i.app (op U))).mp
        ((NatTrans.mono_iff_mono_app i).mp inferInstance (op U))) x
  let gen_at (x : X) (hx : x ∈ V) := (Sheaf.zeroOutsideInt V).presheaf.germ V x hx (Sheaf.zeroOutsideInt.generator V)
  let H_at (x : X) (hx : x ∈ V) : AddSubgroup ℤ :=
    (i_x x).range.comap (AddMonoidHom.mk' (fun n : ℤ => n • gen_at x hx) fun m n => add_smul m n _)
  have cyclic_generator_of_coeff {x : X} {hx : x ∈ V} {d : ℤ} {a}
      (hd : d ≠ 0) (ha : i_x x a = d • gen_at x hx) :
      ∃ e : ℕ, 0 < e ∧ (e : ℤ) ∈ H_at x hx ∧ ∀ h ∈ H_at x hx, (e : ℤ) ∣ h := by
    obtain ⟨e, he⟩ := Int.subgroup_cyclic (H_at x hx)
    refine ⟨e.natAbs, Int.natAbs_pos.mpr ?_, by simp [he], fun h hh => ?_⟩
    · exact fun he0 => (show H_at x hx ≠ ⊥ from AddSubgroup.ne_bot_iff_exists_ne_zero.mpr ⟨⟨d, ⟨a, ha⟩⟩, fun h => hd (by simpa using congrArg Subtype.val h)⟩) (by simpa [he0, AddSubgroup.closure_singleton_zero] using he)
    · exact Int.natAbs_dvd.mpr (by simpa [he, AddSubgroup.mem_closure_singleton, dvd_def, zsmul_eq_mul, mul_comm, eq_comm] using hh)
  -- Step 1: P(n) holds if n > 0 and some x ∈ V has image subgroup generated by n
  let P : ℕ → Prop := fun n => 0 < n ∧ ∃ (x : X) (hx : x ∈ V),
    (n : ℤ) ∈ H_at x hx ∧ ∀ h ∈ H_at x hx, (n : ℤ) ∣ h
  have hP : ∃ n, P n := by
    obtain ⟨x₀', hx₀'V, a₀', ha₀'⟩ := exists_nonzero_stalk_in_V V hRsh i hR
    obtain ⟨n, hn⟩ := stalk_zeroOutsideInt_eq_zsmul_generator V x₀' hx₀'V (i_x x₀' a₀')
    exact (cyclic_generator_of_coeff (fun hn0 => ha₀' <| hi_inj x₀' <| by simpa [hn0] using hn) hn).imp fun _ he => ⟨he.1, x₀', hx₀'V, he.2.1, he.2.2⟩
  classical
  let d : ℤ := Nat.find hP
  obtain ⟨hd_nat_pos, x₀, hx₀V, ⟨a₁, ha₁⟩, _⟩ := Nat.find_spec hP
  have hd_pos : 0 < d := Int.ofNat_lt.mpr hd_nat_pos
  obtain ⟨W₀, hx₀W₀, s₀, hs₀⟩ := Presheaf.germ_exist R x₀ a₁
  let V₁ := W₀ ⊓ V
  have hV₁V : V₁ ≤ V := inf_le_right
  set s₁ := ConcreteCategory.hom (R.map (homOfLE (inf_le_left : V₁ ≤ W₀)).op) s₀
  -- Step 5: Shrink to where germ coefficient is constant via germ_eq
  obtain ⟨W, hx₀W, iW1, _, hW_eq⟩ :=
    Presheaf.germ_eq (Sheaf.zeroOutsideInt V).val x₀ (show x₀ ∈ V₁ from ⟨hx₀W₀, hx₀V⟩) (show x₀ ∈ V₁ from ⟨hx₀W₀, hx₀V⟩) (i.app (op V₁) s₁)
      (d • ConcreteCategory.hom ((Sheaf.zeroOutsideInt V).val.map (homOfLE hV₁V).op) (Sheaf.zeroOutsideInt.generator V)) (by
      rw [← Presheaf.stalkFunctor_map_germ_apply V₁ x₀ (show x₀ ∈ V₁ from ⟨hx₀W₀, hx₀V⟩) i s₁,
        (Presheaf.germ_res_apply R (homOfLE inf_le_left) x₀ (show x₀ ∈ V₁ from ⟨hx₀W₀, hx₀V⟩) s₀).trans hs₀,
        ha₁, AddMonoidHom.mk'_apply, map_zsmul, Presheaf.germ_res_apply (Sheaf.zeroOutsideInt V).val (homOfLE hV₁V)])
  have hWV : W ≤ V := le_trans (leOfHom iW1) hV₁V
  refine ⟨W, hWV, fun h => (Opens.mem_bot (x := x₀)).mp (h ▸ hx₀W), ConcreteCategory.hom (R.map (homOfLE (leOfHom iW1 : W ≤ V₁)).op) s₁, fun x hxW => ?_⟩
  have hcoeff_x : i_x x (R.germ W x hxW (ConcreteCategory.hom (R.map (homOfLE (leOfHom iW1 : W ≤ V₁)).op) s₁)) = d • gen_at x (hWV hxW) := by
    simpa [i_x, gen_at, map_zsmul, Presheaf.germ_res_apply, Presheaf.stalkFunctor_map_germ_apply] using congrArg ((Sheaf.zeroOutsideInt V).presheaf.germ W x hxW) hW_eq
  refine ⟨fun h_zero => ne_of_gt hd_pos (zsmul_generator_injective V x (hWV hxW) (by simpa [h_zero] using hcoeff_x.symm)), fun a => ?_⟩
  obtain ⟨n, hn⟩ := stalk_zeroOutsideInt_eq_zsmul_generator V x (hWV hxW) (i_x x a)
  obtain ⟨d_x, hd_x_pos, hd_x_mem, hd_x_gen⟩ := cyclic_generator_of_coeff (ne_of_gt hd_pos) hcoeff_x
  obtain ⟨k₀, rfl⟩ := hd_x_gen n ⟨a, hn⟩
  exact ⟨k₀, hi_inj x (by rw [map_zsmul, hn, le_antisymm (Int.le_of_dvd hd_pos (hd_x_gen d ⟨_, hcoeff_x⟩)) <| Int.ofNat_le.mpr (Nat.find_min' hP ⟨hd_x_pos, x, hWV hxW, hd_x_mem, hd_x_gen⟩), mul_comm, mul_smul, ← hcoeff_x])⟩

/-- Core construction for Step 4: find V' ≤ V, V' ≠ ⊥, and a section s ∈ R(V') such that
    `sHom s : zeroOutsideInt V' ⟶ R` is a stalk-isomorphism on V'.
    Uses: minimum-index point, generator section, locally constant germ shrinking. -/
theorem exists_good_section
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    {V : Opens X} {R : TopCat.Presheaf AddCommGrpCat.{u} X} (hRsh : R.IsSheaf)
    (i : R ⟶ (TopCat.Sheaf.zeroOutsideInt V).val)
    [Mono i]
    (hR : ¬ IsZero R) :
    ∃ (V' : Opens X) (_ : V' ≤ V) (_ : V' ≠ ⊥)
      (s : R.obj (op V')),
      ∀ (x : X) (_ : x ∈ V'),
        Function.Bijective (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (TopCat.Sheaf.zeroOutsideInt.sHomVal hRsh s))) := by
  obtain ⟨V', hV'V, hV'ne, s, hgen⟩ := exists_section_generating_stalks (R := R) hRsh i hR
  exact ⟨V', hV'V, hV'ne, s, fun x hx =>
    sHom_stalk_bijective_at (R := R) hV'V hRsh i s x hx (hgen x hx).1 (hgen x hx).2⟩

/-- **Structure lemma** (Hartshorne Step 4 core): a nonzero subsheaf of `zeroOutsideInt V`
    contains `zeroOutsideInt V'` for some nonempty open `V' ⊆ V`, with the inclusion
    being a stalk-isomorphism on `V'`. This follows from: stalks of `Z_V` are `ℤ` or `0`,
    stalks of `R` are `d_x·ℤ ⊆ ℤ`, and after shrinking to an open where the multiplicity
    `d_x` is constant and minimal, `R` restricts to `d·Z_{V'}` ≅ `Z_{V'}`. -/
theorem subsheaf_contains_zeroOutsideInt
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    {V : Opens X} {R : TopCat.Presheaf AddCommGrpCat.{u} X} (hRsh : R.IsSheaf)
    (i : R ⟶ (TopCat.Sheaf.zeroOutsideInt V).val)
    [Mono i]
    (hR : ¬ IsZero R) :
    ∃ (V' : Opens X) (_ : V' ≤ V) (_ : V' ≠ ⊥)
      (j : (TopCat.Sheaf.zeroOutsideInt V').val ⟶ R),
      Mono j ∧
      (∀ (x : X) (_ : x ∈ V'),
        Function.Bijective (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map j))) := by
  obtain ⟨V', hle, hne, s, hbij⟩ :=
    exists_good_section (R := R) hRsh i hR
  let j : (TopCat.Sheaf.zeroOutsideInt V').val ⟶ R :=
    TopCat.Sheaf.zeroOutsideInt.sHomVal hRsh s
  have hj_bij : ∀ (x : X) (_ : x ∈ V'),
      Function.Bijective (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map j)) := by
    simpa [j] using hbij
  refine ⟨V', hle, hne, j, ?_, hj_bij⟩
  haveI : ∀ x, Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      j) := fun y => by
    apply (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr
    by_cases hy : y ∈ V'
    · exact (hj_bij y hy).1
    · intro a b _
      exact (stalk_zeroOutsideInt_zero_outside V' y hy a).trans
        (stalk_zeroOutsideInt_zero_outside V' y hy b).symm
  exact (NatTrans.mono_iff_mono_app j).2 fun U =>
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).2
      (TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective j U.unop
        fun x _hx =>
          (ConcreteCategory.mono_iff_injective_of_preservesPullback _).1 inferInstance)

/-! ## Step 4/5 vanishing assembly -/

/-- The induction hypothesis for Grothendieck vanishing: vanishing holds for all
    sheaf-valued presheaves on all spaces of strictly smaller Krull dimension than X. -/
abbrev VanishingIH (dimX : WithBot ℕ∞) : Prop :=
  ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
    (m : ℕ) {G : TopCat.Presheaf AddCommGrpCat.{u} Y} (hG : G.IsSheaf),
    topologicalKrullDim Y < dimX →
    m > topologicalKrullDim Y →
    Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} Y) m)

/-- Vanishing for a sheaf supported on the complement of an open `V`, via the
    closed-immersion SES on `Y = Vᶜ`. This is the support-vanishing input used by the
    Step 5 irreducible-space assembly immediately below. -/
theorem closedComplementVanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (hV : V ≠ ⊥)
    {C : TopCat.Presheaf AddCommGrpCat.{u} X} (hC : C.IsSheaf) (n : ℕ)
    (ih : VanishingIH.{u} (topologicalKrullDim X))
    (hn : ↑n > topologicalKrullDim (Set.compl (V : Set X)))
    (hStalksOnV : ∀ x ∈ V,
      ∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj C), a = 0) :
    Subsingleton (Sheaf.H (⟨C, hC⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) n) := by
  let Csh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨C, hC⟩
  set Y := (V : Set X)ᶜ
  have hYcl : IsClosed Y := V.2.isClosed_compl
  have hY_dim_lt_top : topologicalKrullDim Y < ⊤ :=
    topologicalKrullDim_lt_top_of_lt_nat (by simpa [gt_iff_lt] using hn)
  have hY_dim_lt : topologicalKrullDim Y < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl
      (Set.compl_ne_univ.mpr (Set.nonempty_iff_ne_empty.mpr (Opens.coe_eq_empty.not.mpr hV)))
      hY_dim_lt_top
  let closedIncl := TopCat.closedIncl hYcl
  let CY := ((TopCat.Sheaf.pullback AddCommGrpCat.{u} closedIncl).obj Csh)
  let S := closedImmersionSES (Z := Y) (hZ := hYcl) Csh
  have hSE := closedImmersionSES_shortExact (Z := Y) (hZ := hYcl) Csh
  have hSX₁_zero : IsZero S.X₁ := by
    exact sheaf_isZero_of_zero_stalks X S.X₁.cond (fun x a => by
      by_cases hxY : x ∈ Y
      · haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val) := by
          simpa [S, closedImmersionSES, closedIncl, Csh] using
            (TopCat.closedIncl_unit_stalk_isIso (C := AddCommGrpCat.{u})
              (hs := hYcl) Csh ⟨x, hxY⟩)
        exact stalk_zero_of_ses_g_iso S hSE x inferInstance a
      · exact stalk_zero_of_shortExact_kernel S hSE x
          (fun b => hStalksOnV x (by rwa [Set.mem_compl_iff, not_not] at hxY) b)
          a)
  exact subsingleton_sheafH_of_closedImmersion_middle
    (Z := Y) (hZ := hYcl) Csh n
    (by
      simpa [S] using sheafH_subsingleton_of_isZero hSX₁_zero n)
    (by
      simpa [closedIncl, Csh, CY] using
        ih (TopCat.of Y) n (G := CY.val) CY.cond hY_dim_lt hn)

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
  have hTop : Subsingleton (Sheaf.H (TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X)) (m + 1)) := by
    simpa using
      sheafH_subsingleton_of_flasque X (TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X))
        (fun i => isFlasqueSheaf_zeroOutsideInt_top X i) m
  exact sheafH_dimension_shift_of_mono
    (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ (⊤ : Opens X))) m
    hCoker hTop

/-- **Step 5** (Hartshorne III.2.7): `zeroOutsideInt V` has vanishing cohomology in every
    degree `m > dim X` on an irreducible Noetherian space.
    Proof: write `m = m' + 1`, apply `zeroOutsideInt_vanishing` (SES + flasque), then prove
    cokernel vanishing at `m'` via the closed-immersion middle-term API, which transports
    cohomology along the `PushforwardHIso` closed-inclusion comparison. -/
theorem zeroOutsideInt_cohomology_vanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (hV : V ≠ ⊥)
    (ih : VanishingIH.{u} (topologicalKrullDim X))
    (m : ℕ) (hm : m > topologicalKrullDim X) :
    Subsingleton (Sheaf.H (TopCat.Sheaf.zeroOutsideInt V) m) := by
  let C := Limits.cokernel (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤))
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
  apply zeroOutsideInt_vanishing V m'
  exact closedComplementVanishing V hV (C := C.val) C.cond m' ih
    (by simpa [gt_iff_lt] using hVcompl_lt_m')
    (fun x hxV a => cokernel_stalk_zero_of_stalk_surj
      (f := TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤))
      (x := x)
      (hf := sheafifyMap_zeroOutside_openHom_stalk_surj Presheaf.constZ le_top x hxV) a)

/-- **Step 4** (Hartshorne III.2.7): any subsheaf of `zeroOutsideInt V` has vanishing
    cohomology in degree `m > dim X`. Uses `subsheaf_contains_zeroOutsideInt` to find
    `V' ⊆ V` with `Z_{V'} ↪ R` (stalk-iso on `V'`). The cokernel is supported on `(V')^c`
    (dim < dim X), so vanishes by the IH. Middle-term LES gives `H^m(R) = 0`. -/
theorem subsheaf_zeroOutsideInt_vanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    {V : Opens X} {R : TopCat.Presheaf AddCommGrpCat.{u} X} (hRsh : R.IsSheaf)
    (i : R ⟶ (TopCat.Sheaf.zeroOutsideInt V).val)
    [Mono i]
    (ih : VanishingIH.{u} (topologicalKrullDim X))
    (m : ℕ) (hm : m > topologicalKrullDim X) :
    Subsingleton (Sheaf.H (⟨R, hRsh⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m) := by
  by_cases hR : IsZero (⟨R, hRsh⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
  · simpa using sheafH_subsingleton_of_isZero hR m
  · obtain ⟨V', hV'le, hV'ne, j, hj_mono, hj_stalk⟩ :=
      (by
        exact subsheaf_contains_zeroOutsideInt (R := R) hRsh i (by
        intro hR0
        exact hR (IsZero.of_full_of_faithful_of_isZero
          (TopCat.Sheaf.forget AddCommGrpCat.{u} X)
          (⟨R, hRsh⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) hR0)))
    haveI : Mono j := hj_mono
    let jsh : TopCat.Sheaf.zeroOutsideInt V' ⟶
        (⟨R, hRsh⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := Sheaf.Hom.mk j
    haveI : Mono jsh := by
      exact (Sheaf.Hom.mono_iff_presheaf_mono
        (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) jsh).2 inferInstance
    let C : TopCat.Sheaf AddCommGrpCat.{u} X :=
      cokernel jsh
    have hC : Subsingleton (Sheaf.H C m) := by
      have hV'compl_lt_nat :
          topologicalKrullDim (Set.compl (V' : Set X)) < ↑↑(m : ℕ) :=
        topologicalKrullDim_subspace_lt_of_lt (X := X) (Set.compl (V' : Set X))
          hm
      have hV'compl_lt_top : topologicalKrullDim (Set.compl (V' : Set X)) < ⊤ :=
        topologicalKrullDim_lt_top_of_lt_nat hV'compl_lt_nat
      have hV'compl_lt_X :
          topologicalKrullDim (Set.compl (V' : Set X)) < topologicalKrullDim X :=
        topologicalKrullDim_lt_of_isIrreducible_of_isClosed
          V'.2.isClosed_compl
          (Set.compl_ne_univ.mpr (Set.nonempty_iff_ne_empty.mpr
            (Opens.coe_eq_empty.not.mpr hV'ne)))
          hV'compl_lt_top
      exact closedComplementVanishing V' hV'ne (C := C.val) C.cond m ih
        (by simpa [gt_iff_lt] using lt_trans hV'compl_lt_X hm)
        (fun x hxV' b => cokernel_stalk_zero_of_stalk_surj
          (F := TopCat.Sheaf.zeroOutsideInt V')
          (G := (⟨R, hRsh⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
          (f := jsh) (x := x) (hf := (hj_stalk x hxV').2) b)
    exact subsingleton_sheafH_of_shortExact_middle jsh m
      (zeroOutsideInt_cohomology_vanishing V' hV'ne ih m hm)
      (by simpa [C] using hC)

/-- **Steps 3C + 4 + LES** (Hartshorne III.2.7): any locally surjective image of
    `zeroOutsideInt V` has vanishing cohomology in degree `m > dim X`. Uses third-term LES with
    `zeroOutsideInt_cohomology_vanishing` (Step 5) and
    `subsheaf_zeroOutsideInt_vanishing` (Step 4). -/
theorem epiImage_zeroOutsideInt_vanishing_of_locallySurjective
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    {V : Opens X} {G : TopCat.Presheaf AddCommGrpCat.{u} X} (hG : G.IsSheaf)
    (f : (TopCat.Sheaf.zeroOutsideInt V).val ⟶ G)
    (hf : TopCat.Presheaf.IsLocallySurjective f)
    (ih : VanishingIH.{u} (topologicalKrullDim X))
    (m : ℕ) (hm : m > topologicalKrullDim X) :
    Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m) := by
  letI : Balanced (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) := balanced_of_strongEpiCategory
  by_cases hV : V = ⊥
  · subst hV
    haveI : Epi (show TopCat.Sheaf.zeroOutsideInt (⊥ : Opens X) ⟶
        (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) from Sheaf.Hom.mk f) := by
      rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
        (show TopCat.Sheaf.zeroOutsideInt (⊥ : Opens X) ⟶
          (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) from Sheaf.Hom.mk f)]
      simpa using hf
    have hZero : IsZero ((⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) :=
      (isZero_zeroOutsideInt_bot X).of_epi (show TopCat.Sheaf.zeroOutsideInt (⊥ : Opens X) ⟶
        (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) from Sheaf.Hom.mk f)
    simpa using sheafH_subsingleton_of_isZero hZero m
  · let fsh : TopCat.Sheaf.zeroOutsideInt V ⟶
        (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := Sheaf.Hom.mk f
    have hkernel : Subsingleton (Sheaf.H (kernel fsh) (m + 1)) := by
      haveI : Mono (kernel.ι fsh).val :=
        Functor.map_mono (TopCat.Sheaf.forget AddCommGrpCat.{u} X) (kernel.ι fsh)
      simpa [fsh] using
        subsheaf_zeroOutsideInt_vanishing
          (R := (kernel fsh).val) (kernel fsh).cond (kernel.ι fsh).val
          ih (m + 1) (lt_trans hm (by exact_mod_cast Nat.lt_succ_of_le le_rfl))
    simpa using
      sheafH_dimension_shift_X₃_of_locallySurjective fsh (by simpa [fsh] using hf) m
        (zeroOutsideInt_cohomology_vanishing V hV ih m hm)
        hkernel

-- Filtered diagram infrastructure, finitely generated vanishing, and
-- directLimit_cohomology_vanishing are in FinitelyGeneratedVanishing.lean.

/-- **Irreducible positive-dimensional vanishing** (Hartshorne III.2.7, irreducible case).
    Uses the closed immersion step and induction on a proper closed subset. -/
theorem IrreduciblePosVanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    (hpos : topologicalKrullDim X > 0)
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (ih : VanishingIH.{u} (topologicalKrullDim X)) :
    Subsingleton (Sheaf.H (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) n) := by
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  change Subsingleton (Sheaf.H Fsh n)
  have hX_lt_top : topologicalKrullDim X < ⊤ :=
    topologicalKrullDim_lt_top_of_lt_nat (by simpa [gt_iff_lt] using hn)
  obtain ⟨Z, hZ_closed, _, hZ_dim⟩ :=
    exists_closed_subset_lt_topologicalKrullDim_of_irreducible_pos (X := X) hpos hX_lt_top
  have hn_Z : n > topologicalKrullDim (TopCat.of Z) := by
    simpa [gt_iff_lt] using lt_trans hZ_dim (by simpa [gt_iff_lt] using hn)
  let i := TopCat.closedIncl hZ_closed
  let FZ := ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj Fsh)
  let S := closedImmersionSES (Z := Z) (hZ := hZ_closed) Fsh
  have hKer : Subsingleton (Sheaf.H S.X₁ n) :=
    directLimit_cohomology_vanishing (K := S.X₁.val) S.X₁.cond n
      (fun {G} (hG : G.IsSheaf) {V}
        (f : (TopCat.Sheaf.zeroOutsideInt V).val ⟶ G) hf => by
        exact epiImage_zeroOutsideInt_vanishing_of_locallySurjective
          (V := V) (G := G) hG f hf ih n hn)
  exact subsingleton_sheafH_of_closedImmersion_middle
    (Z := Z) (hZ := hZ_closed) Fsh n
    (by simpa [S] using hKer)
    (by simpa [i, Fsh, FZ] using ih (TopCat.of Z) n (G := FZ.val) FZ.cond hZ_dim hn_Z)
