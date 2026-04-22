import Aristotle.GrothendieckVanishing.main.ClosedImmersionCohomology
import Aristotle.GrothendieckVanishing.main.ConstantSheafFlasque
import Aristotle.GrothendieckVanishing.main.FiniteGeneratorReduction
import Aristotle.GrothendieckVanishing.main.FlasqueCohomology
import Aristotle.GrothendieckVanishing.main.SheafStalkAlgebra
import Aristotle.GrothendieckVanishing.main.TopologicalKrullDim
import Aristotle.GrothendieckVanishing.main.ZeroOutside

/-!
  IrreducibleStep.lean — Assembly: irreducible positive-dimension vanishing

  Key results:
  - exists_section_generating_stalks: PROVED — uses Nat.find to choose x₀ with minimal
    image subgroup generator d, then divisibility d | d_x follows from minimality.
  - exists_good_section: PROVED — via exists_section_generating_stalks + sHom_stalk_bijective_at
  - zeroOutsideInt_vanishing / zeroOutsideInt_cohomology_vanishing: Step 5 vanishing
    assembled where it is consumed
  - IrreduciblePosVanishing: assembles all pieces (FULLY PROVED)

  Supporting stalk lemmas remain in `ZeroOutside.lean` and `SheafStalkAlgebra.lean`.
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

/-- At each point `x ∈ V`, the image of the stalk of `R` under `i` is a subgroup of
    `stalk(zeroOutsideInt V, x) ≅ ULift ℤ`. By `ulift_int_subgroup_cyclic`, if this image
    is nonzero, it has a positive generator `d_x`. The "index" `d_x` measures how deeply
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
  let i_x (x : X) := ConcreteCategory.hom
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map i)
  have hi_inj : ∀ (x : X), Function.Injective (i_x x) := fun x => by
    exact TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective (f := i)
      (fun U =>
        (ConcreteCategory.mono_iff_injective_of_preservesPullback (i.app (op U))).mp
          ((NatTrans.mono_iff_mono_app i).mp inferInstance (op U))) x
  let gen_at (x : X) (hx : x ∈ V) := (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V x hx
    (TopCat.Sheaf.zeroOutsideInt.generator V)
  let H_at (x : X) (hx : x ∈ V) : AddSubgroup (ULift.{u} ℤ) := {
    carrier := {n | n.down • gen_at x hx ∈ Set.range (i_x x)}
    add_mem' := fun ⟨ra, hra⟩ ⟨rb, hrb⟩ =>
      ⟨ra + rb, by rw [ULift.add_down, add_smul, map_add, hra, hrb]⟩
    zero_mem' := ⟨0, by simp [ULift.zero_down]⟩
    neg_mem' := fun ⟨ra, hra⟩ => ⟨-ra, by rw [ULift.neg_down, neg_smul, map_neg, hra]⟩ }
  -- Step 1: P(n) holds if n > 0 and some x ∈ V has image subgroup generated by n
  let P : ℕ → Prop := fun n => 0 < n ∧ ∃ (x : X) (hx : x ∈ V),
    (↑n : ℤ) • gen_at x hx ∈ Set.range (i_x x) ∧
    ∀ (m : ℤ), m • gen_at x hx ∈ Set.range (i_x x) → (↑n : ℤ) ∣ m
  have mk_P : ∀ (x : X) (hx : x ∈ V) (d : ULift.{u} ℤ),
      d.down > 0 → d.down • gen_at x hx ∈ Set.range (i_x x) →
      (∀ h ∈ H_at x hx, ∃ k : ℤ, h = ⟨k * d.down⟩) → P d.down.toNat := by
    intro x hx d hpos hrange hgen
    refine ⟨Int.pos_iff_toNat_pos.mp hpos, x, hx, by rwa [Int.toNat_of_nonneg (le_of_lt hpos)],
      fun m hm => by rw [Int.toNat_of_nonneg (le_of_lt hpos)]
                     obtain ⟨k, hk⟩ := hgen ⟨m⟩ hm
                     exact ⟨k, by simpa [mul_comm] using congrArg ULift.down hk⟩⟩
  have hP : ∃ n, P n := by
    obtain ⟨x₀', hx₀'V, a₀', ha₀'⟩ := exists_nonzero_stalk_in_V V hRsh i hR
    have hH'_ne : H_at x₀' hx₀'V ≠ ⊥ := by
      rw [ne_eq, AddSubgroup.eq_bot_iff_forall]; push_neg
      obtain ⟨n, hn⟩ := stalk_zeroOutsideInt_eq_zsmul_generator V x₀' hx₀'V (i_x x₀' a₀')
      exact ⟨⟨n⟩, ⟨a₀', hn⟩, fun h => by
        simp only [ULift.ext_iff, ULift.zero_down] at h
        rw [h, zero_smul] at hn; exact ha₀' (hi_inj x₀' (hn.trans (map_zero (i_x x₀')).symm))⟩
    obtain ⟨d', hd'_mem, hd'_pos, hd'_gen⟩ := ulift_int_subgroup_cyclic _ hH'_ne
    exact ⟨_, mk_P x₀' hx₀'V d' hd'_pos hd'_mem hd'_gen⟩
  haveI : DecidablePred P := Classical.decPred P
  set d_nat := Nat.find (p := P) hP
  obtain ⟨hd_nat_pos, x₀, hx₀V, hd_in_range, hd_divides⟩ := Nat.find_spec (p := P) hP
  have h_minimal : ∀ n, P n → d_nat ≤ n := fun n hn => Nat.find_min' (p := P) hP hn
  set d : ULift.{u} ℤ := ⟨(d_nat : ℤ)⟩ with hd_def
  have hd_pos : d.down > 0 := by simp [hd_def]; exact_mod_cast hd_nat_pos
  let H := H_at x₀ hx₀V
  have hH_ne : H ≠ ⊥ := by
    rw [ne_eq, AddSubgroup.eq_bot_iff_forall]; push_neg
    exact ⟨d, hd_in_range, by rw [ne_eq, ULift.ext_iff, ULift.zero_down]; omega⟩
  have hd_gen : ∀ h ∈ H, ∃ k : ℤ, h = ⟨k * d.down⟩ := by
    intro h hh
    obtain ⟨k, hk⟩ := hd_divides h.down hh
    exact ⟨k, by ext; simp only [hd_def]; rw [hk, mul_comm]⟩
  obtain ⟨a₁, ha₁⟩ : d.down • gen_at x₀ hx₀V ∈ Set.range (i_x x₀) := hd_in_range
  have ha₁_ne : a₁ ≠ 0 := by
    intro h; rw [h, map_zero] at ha₁
    exact absurd (zsmul_generator_injective V x₀ hx₀V ((zero_smul _ _).trans ha₁)).symm
      (by omega)
  have ha₁_gen : ∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).obj R),
      ∃ k : ℤ, a = k • a₁ := by
    intro a; obtain ⟨n, hn⟩ := stalk_zeroOutsideInt_eq_zsmul_generator V x₀ hx₀V (i_x x₀ a)
    obtain ⟨k, hk⟩ := hd_gen ⟨n⟩ ⟨a, hn⟩
    have hn_eq : n = k * d.down := by simpa [mul_comm] using congrArg ULift.down hk
    exact ⟨k, hi_inj x₀ (by rw [map_zsmul, hn, hn_eq, mul_smul, ← ha₁])⟩
  obtain ⟨W₀, hx₀W₀, s₀, hs₀⟩ := TopCat.Presheaf.germ_exist R x₀ a₁
  set V₁ := W₀ ⊓ V with hV₁_def
  have hV₁V : V₁ ≤ V := inf_le_right
  have hx₀V₁ : x₀ ∈ V₁ := ⟨hx₀W₀, hx₀V⟩
  set s₁ := ConcreteCategory.hom (R.map (homOfLE (inf_le_left : V₁ ≤ W₀)).op) s₀
  have hs₁_germ : R.germ V₁ x₀ hx₀V₁ s₁ = a₁ :=
    (TopCat.Presheaf.germ_res_apply R (homOfLE inf_le_left) x₀ hx₀V₁ s₀).trans hs₀
  -- Step 5: Shrink to where germ coefficient is constant via germ_eq
  set is₁ := i.app (op V₁) s₁ with his₁_def
  set d_gen_res := d.down • ConcreteCategory.hom
    ((TopCat.Sheaf.zeroOutsideInt V).val.map (homOfLE hV₁V).op)
    (TopCat.Sheaf.zeroOutsideInt.generator V) with hd_gen_res_def
  obtain ⟨W, hx₀W, iW1, _, hW_eq⟩ :=
    TopCat.Presheaf.germ_eq (TopCat.Sheaf.zeroOutsideInt V).val x₀ hx₀V₁ hx₀V₁ is₁ d_gen_res (by
      rw [his₁_def, show (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V₁ x₀ hx₀V₁
          (i.app (op V₁) s₁) = i_x x₀ (R.germ V₁ x₀ hx₀V₁ s₁) from
        (TopCat.Presheaf.stalkFunctor_map_germ_apply V₁ x₀ hx₀V₁ i s₁).symm,
        hs₁_germ, ha₁, hd_gen_res_def, map_zsmul,
        TopCat.Presheaf.germ_res_apply (TopCat.Sheaf.zeroOutsideInt V).val (homOfLE hV₁V)])
  have hWV₁ : W ≤ V₁ := leOfHom iW1
  have hWV : W ≤ V := le_trans hWV₁ hV₁V
  have hW_ne : W ≠ ⊥ := fun h => (Opens.mem_bot (x := x₀)).mp (h ▸ hx₀W)
  -- Key: at every x ∈ W, i_x(germ(s₁|_W, x)) = d.down • gen_at x
  have hcoeff_const : ∀ (x : X) (hxW : x ∈ W),
      i_x x (R.germ W x hxW
        (ConcreteCategory.hom (R.map (homOfLE hWV₁).op) s₁)) =
      d.down • gen_at x (hWV hxW) := by
    intro x hxW
    rw [TopCat.Presheaf.germ_res_apply,
      show i_x x (R.germ V₁ x (hWV₁ hxW) s₁) =
        (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V₁ x (hWV₁ hxW) is₁ from
        his₁_def ▸ TopCat.Presheaf.stalkFunctor_map_germ_apply V₁ x (hWV₁ hxW) i s₁,
      ← TopCat.Presheaf.germ_res_apply (TopCat.Sheaf.zeroOutsideInt V).val
        (homOfLE hWV₁) x hxW is₁,
      show (TopCat.Sheaf.zeroOutsideInt V).val.map (homOfLE hWV₁).op is₁ =
        (TopCat.Sheaf.zeroOutsideInt V).val.map (homOfLE hWV₁).op d_gen_res from hW_eq,
      TopCat.Presheaf.germ_res_apply, hd_gen_res_def, map_zsmul,
      TopCat.Presheaf.germ_res_apply]
  refine ⟨W, hWV, hW_ne, ConcreteCategory.hom (R.map (homOfLE hWV₁).op) s₁,
    fun x hxW => ?_⟩
  have hcoeff_x := hcoeff_const x hxW
  constructor
  · intro h_zero; rw [h_zero, map_zero] at hcoeff_x
    exact absurd (zsmul_generator_injective V x (hWV hxW)
      ((zero_smul _ _).trans hcoeff_x)).symm (by omega)
  · -- d_nat is minimal, so at every x ∈ W the generator d_x = d.down
    intro a; obtain ⟨n, hn⟩ := stalk_zeroOutsideInt_eq_zsmul_generator V x (hWV hxW) (i_x x a)
    have hd_in_Hx : d.down • gen_at x (hWV hxW) ∈ Set.range (i_x x) := ⟨_, hcoeff_x⟩
    have hHx_ne : H_at x (hWV hxW) ≠ ⊥ := by
      rw [ne_eq, AddSubgroup.eq_bot_iff_forall]; push_neg
      exact ⟨d, hd_in_Hx, by rw [ne_eq, ULift.ext_iff, ULift.zero_down]; omega⟩
    obtain ⟨d_x, hd_x_mem, hd_x_pos, hd_x_gen⟩ := ulift_int_subgroup_cyclic _ hHx_ne
    have hd_x_eq : d_x.down = d.down := by
      have h_le : (d_nat : ℤ) ≤ d_x.down := by
        rw [← Int.toNat_of_nonneg (le_of_lt hd_x_pos)]
        exact_mod_cast h_minimal _ (mk_P x (hWV hxW) d_x hd_x_pos hd_x_mem hd_x_gen)
      obtain ⟨k, hk⟩ := hd_x_gen d hd_in_Hx
      exact le_antisymm (Int.le_of_dvd hd_pos
        ⟨k, by simpa [mul_comm] using congrArg ULift.down hk⟩) h_le
    obtain ⟨k₀, hk₀⟩ := hd_x_gen ⟨n⟩ ⟨a, hn⟩
    have hn_eq : n = k₀ * d.down := by simpa [hd_x_eq] using congrArg ULift.down hk₀
    exact ⟨k₀, hi_inj x (by rw [map_zsmul, hn, hn_eq, mul_smul, ← hcoeff_x])⟩

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
      (F := (TopCat.Sheaf.zeroOutsideInt V).val)
      (G := (TopCat.Sheaf.zeroOutsideInt ⊤).val)
      (hF := (TopCat.Sheaf.zeroOutsideInt V).cond)
      (hG := (TopCat.Sheaf.zeroOutsideInt ⊤).cond)
      (f := (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤)).val)
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
  · simpa using sheafH_subsingleton_of_isZero_presheaf hRsh hR m
  · obtain ⟨V', hV'le, hV'ne, j, hj_mono, hj_stalk⟩ :=
      (by
        exact subsheaf_contains_zeroOutsideInt (R := R) hRsh i (by
        intro hR0
        exact hR (IsZero.of_full_of_faithful_of_isZero
          (TopCat.Sheaf.forget AddCommGrpCat.{u} X)
          (⟨R, hRsh⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) hR0)))
    haveI : Mono j := hj_mono
    let C : TopCat.Sheaf AddCommGrpCat.{u} X :=
      cokernel (show (TopCat.Sheaf.zeroOutsideInt V') ⟶
          (⟨R, hRsh⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) from
            Sheaf.Hom.mk j)
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
          (F := (TopCat.Sheaf.zeroOutsideInt V').val) (G := R)
          (hF := (TopCat.Sheaf.zeroOutsideInt V').cond) (hG := hRsh)
          (f := j) (x := x) (hf := (hj_stalk x hxV').2) b)
    exact subsingleton_sheafH_of_shortExact_middle_presheaf
      (hF := (TopCat.Sheaf.zeroOutsideInt V').cond) (hG := hRsh)
      (f := j) m
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
    simpa using sheafH_subsingleton_of_isZero_presheaf hG hZero m
  · have hkernel :
        Subsingleton (Sheaf.H
          (kernel (Sheaf.Hom.mk f :
            TopCat.Sheaf.zeroOutsideInt V ⟶
              (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)))
          (m + 1)) := by
      let fsh : TopCat.Sheaf.zeroOutsideInt V ⟶
          (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := Sheaf.Hom.mk f
      haveI : Mono (kernel.ι fsh).val :=
        Functor.map_mono (TopCat.Sheaf.forget AddCommGrpCat.{u} X) (kernel.ι fsh)
      simpa [fsh] using
        subsheaf_zeroOutsideInt_vanishing
          (R := (kernel fsh).val) (kernel fsh).cond (kernel.ι fsh).val
          ih (m + 1) (lt_trans hm (by exact_mod_cast Nat.lt_succ_of_le le_rfl))
    simpa using
      sheafH_dimension_shift_X₃_of_locallySurjective_presheaf
        (hF := (TopCat.Sheaf.zeroOutsideInt V).cond) (hG := hG)
        f hf m
        (zeroOutsideInt_cohomology_vanishing V hV ih m hm)
        hkernel

theorem epiImage_zeroOutsideInt_vanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    {V : Opens X} {G : TopCat.Presheaf AddCommGrpCat.{u} X} (hG : G.IsSheaf)
    (f : (TopCat.Sheaf.zeroOutsideInt V).val ⟶ G) [Epi f]
    (ih : VanishingIH.{u} (topologicalKrullDim X))
    (m : ℕ) (hm : m > topologicalKrullDim X) :
    Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m) := by
  let Gsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨G, hG⟩
  let fsh : TopCat.Sheaf.zeroOutsideInt V ⟶ Gsh := Sheaf.Hom.mk f
  haveI : Epi fsh := by
    exact Sheaf.Hom.epi_of_presheaf_epi
      (J := Opens.grothendieckTopology X) (A := AddCommGrpCat.{u}) fsh
  letI : Balanced (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) := balanced_of_strongEpiCategory
  have hf : TopCat.Presheaf.IsLocallySurjective f := by
    simpa [fsh] using
      (show Sheaf.IsLocallySurjective fsh from
        (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} fsh).mpr inferInstance)
  exact epiImage_zeroOutsideInt_vanishing_of_locallySurjective
    (V := V) (G := G) hG f hf ih m hm

-- Filtered diagram infrastructure, finitely generated vanishing, and
-- directLimit_cohomology_vanishing are in FiniteGeneratorReduction.lean.

/-- **Irreducible vanishing** (Hartshorne III.2.7, irreducible case).
    Covers both dim > 0 (closed immersion + induction) and dim ≤ 0 (flasque). -/
theorem IrreduciblePosVanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (ih : VanishingIH.{u} (topologicalKrullDim X)) :
    Subsingleton (Sheaf.H (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) n) := by
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  change Subsingleton (Sheaf.H Fsh n)
  by_cases hpos : topologicalKrullDim X > 0
  · obtain ⟨Z, hZ_closed, _, hZ_dim⟩ :=
      exists_closed_subset_lt_topologicalKrullDim_of_irreducible_pos (X := X) hpos <|
        by simpa [gt_iff_lt] using hn
    have hn_Z : n > topologicalKrullDim (TopCat.of Z) := by
      simpa [gt_iff_lt] using lt_trans hZ_dim (by simpa [gt_iff_lt] using hn)
    let i := TopCat.closedIncl hZ_closed
    let FZ := ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj Fsh)
    let S := closedImmersionSES (Z := Z) (hZ := hZ_closed) (F := F) hF
    have hKer : Subsingleton (Sheaf.H S.X₁ n) :=
      directLimit_cohomology_vanishing (K := S.X₁.val) S.X₁.cond n
        (fun {G} (hG : G.IsSheaf) {V}
          (f : (TopCat.Sheaf.zeroOutsideInt V).val ⟶ G) hf => by
          exact epiImage_zeroOutsideInt_vanishing_of_locallySurjective
            (V := V) (G := G) hG f hf ih n hn)
    exact subsingleton_sheafH_of_closedImmersion_middle_presheaf
      (Z := Z) (hZ := hZ_closed) (F := F) hF n
      (by simpa [S] using hKer)
      (by simpa [i, Fsh, FZ] using ih (TopCat.of Z) n (G := FZ.val) FZ.cond hZ_dim hn_Z)
  · -- dim ≤ 0: F is flasque on irreducible dim-0 space, use FlasqueVanishing
    push_neg at hpos
    haveI : IsFlasqueSheaf Fsh := ⟨fun {U V} i => by
      rcases opens_eq_bot_or_top_of_irreducibleSpace_dim_zero hpos U with rfl | rfl
      · exact Fsh.isTerminalOfEmpty.isZero.epi _
      · have hV := le_antisymm le_top (homOfLE le_top ≫ i |>.le); subst hV
        rw [Subsingleton.elim i (𝟙 ⊤), op_id, F.map_id]; infer_instance⟩
    have hm_ne : n ≠ 0 := fun h => by
      subst h; exact absurd hn (not_lt.mpr topologicalKrullDim_nonneg)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne
    exact sheafH_subsingleton_of_flasque_presheaf X hF m
