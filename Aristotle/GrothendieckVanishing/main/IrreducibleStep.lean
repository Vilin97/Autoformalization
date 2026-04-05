/-
  IrreducibleStep.lean — Assembly: irreducible positive-dimension vanishing

  Key results (unique to this file; stalk algebra lemmas are in StalkGeneratorAlgebra.lean):
  - exists_section_generating_stalks: PROVED — uses Nat.find to choose x₀ with minimal
    image subgroup generator d, then divisibility d | d_x follows from minimality.
  - exists_good_section: PROVED — via exists_section_generating_stalks + sHom_stalk_bijective_at
  - IrreduciblePosVanishing: assembles all pieces (FULLY PROVED)
-/
import Aristotle.GrothendieckVanishing.main.StalkGeneratorAlgebra

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

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
  have hi_s_ne : i_x (R.presheaf.germ U x hxU s) ≠ 0 :=
    fun h => hs_ne (hi_inj (h.trans (map_zero i_x).symm))
  -- i_x(germ(s,x)) = c • gen_V for some c ≠ 0
  obtain ⟨c, hc⟩ := stalk_zeroOutsideInt_eq_zsmul_generator V x (hUV hxU)
    (i_x (R.presheaf.germ U x hxU s))
  have hc_ne : c ≠ 0 := fun hc0 => by rw [hc0, zero_smul] at hc; exact hi_s_ne hc
  -- Key: sHom_x(germ(gen_U, x)) = germ(s, x)
  have h_sHom_gen : sHom_x ((TopCat.Sheaf.zeroOutsideInt U).presheaf.germ U x hxU
      (TopCat.Sheaf.zeroOutsideInt.generator U)) = R.presheaf.germ U x hxU s := by
    show T.map (TopCat.Sheaf.zeroOutsideInt.sHom s).val _ = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    congr 1; exact TopCat.Sheaf.zeroOutsideInt.sHom_app_generator s
  -- Surjectivity
  have h_surj : Function.Surjective sHom_x := by
    intro a; obtain ⟨k, hk⟩ := hgen a
    exact ⟨k • (TopCat.Sheaf.zeroOutsideInt U).presheaf.germ U x hxU
      (TopCat.Sheaf.zeroOutsideInt.generator U), by rw [map_zsmul, h_sHom_gen, hk]⟩
  -- Injectivity: n • germ(s,x) = m • germ(s,x) → n = m (using torsion-freeness via i)
  have h_inj : Function.Injective sHom_x := by
    intro a b hab
    obtain ⟨n, rfl⟩ := stalk_zeroOutsideInt_eq_zsmul_generator U x hxU a
    obtain ⟨m, rfl⟩ := stalk_zeroOutsideInt_eq_zsmul_generator U x hxU b
    simp only [map_zsmul, h_sHom_gen] at hab
    -- hab : n • germ(s, x) = m • germ(s, x) in stalk(R, x)
    -- Apply i_x then use torsion-freeness: n • c • gen_V = m • c • gen_V → n = m
    have h_i : n • i_x (R.presheaf.germ U x hxU s) =
        m • i_x (R.presheaf.germ U x hxU s) := by rw [← map_zsmul, ← map_zsmul, hab]
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
  -- Stalk map at any point x
  let i_x (x : X) := ConcreteCategory.hom
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map i.val)
  -- i_x is injective at all points
  have hi_inj : ∀ (x : X), Function.Injective (i_x x) := by
    intro x
    let FT := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    haveI := TopCat.Presheaf.stalkFunctor_preserves_mono (C := AddCommGrpCat.{u}) (X := X) x
    haveI : Mono (FT.map i) := Functor.map_mono FT i
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback (FT.map i)).mp inferInstance
  -- Abbreviation for germ of generator at x ∈ V
  let gen_at (x : X) (hx : x ∈ V) := (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V x hx
    (TopCat.Sheaf.zeroOutsideInt.generator V)
  -- Helper: build image subgroup at any point x ∈ V
  let H_at (x : X) (hx : x ∈ V) : AddSubgroup (ULift.{u} ℤ) := {
    carrier := {n | n.down • gen_at x hx ∈ Set.range (i_x x)}
    add_mem' := by
      intro a b ha hb; obtain ⟨ra, hra⟩ := ha; obtain ⟨rb, hrb⟩ := hb
      exact ⟨ra + rb, by rw [ULift.add_down, add_smul, map_add, hra, hrb]⟩
    zero_mem' := ⟨0, by simp [ULift.zero_down]⟩
    neg_mem' := by
      intro a ha; obtain ⟨ra, hra⟩ := ha
      exact ⟨-ra, by rw [ULift.neg_down, neg_smul, map_neg, hra]⟩
  }
  -- Step 1: Choose x₀ ∈ V with MINIMAL image subgroup generator.
  -- P(n): n > 0 and some x ∈ V has image subgroup generated by n
  let P : ℕ → Prop := fun n => 0 < n ∧ ∃ (x : X) (hx : x ∈ V),
    (↑n : ℤ) • gen_at x hx ∈ Set.range (i_x x) ∧
    ∀ (m : ℤ), m • gen_at x hx ∈ Set.range (i_x x) → (↑n : ℤ) ∣ m
  have hP : ∃ n, P n := by
    obtain ⟨x₀', hx₀'V, a₀', ha₀'⟩ := exists_nonzero_stalk_in_V V R i hR
    have hH'_ne : H_at x₀' hx₀'V ≠ ⊥ := by
      rw [ne_eq, AddSubgroup.eq_bot_iff_forall]; push_neg
      obtain ⟨n, hn⟩ := stalk_zeroOutsideInt_eq_zsmul_generator V x₀' hx₀'V (i_x x₀' a₀')
      exact ⟨⟨n⟩, ⟨a₀', hn⟩, fun h => by
        simp only [ULift.ext_iff, ULift.zero_down] at h
        rw [h, zero_smul] at hn; exact ha₀' (hi_inj x₀' (hn.trans (map_zero (i_x x₀')).symm))⟩
    obtain ⟨d', hd'_mem, hd'_pos, hd'_gen⟩ := ulift_int_subgroup_cyclic _ hH'_ne
    refine ⟨d'.down.toNat, Int.pos_iff_toNat_pos.mp hd'_pos, x₀', hx₀'V, ?_, ?_⟩
    · rwa [Int.toNat_of_nonneg (le_of_lt hd'_pos)]
    · intro m hm
      obtain ⟨k, hk⟩ := hd'_gen ⟨m⟩ hm
      rw [Int.toNat_of_nonneg (le_of_lt hd'_pos)]
      exact ⟨k, by simpa [mul_comm] using congrArg ULift.down hk⟩
  -- d_nat is the minimal positive generator among all points of V
  haveI : DecidablePred P := Classical.decPred P
  set d_nat := Nat.find (p := P) hP
  obtain ⟨hd_nat_pos, x₀, hx₀V, hd_in_range, hd_divides⟩ := Nat.find_spec (p := P) hP
  -- Minimality of d_nat
  have h_minimal : ∀ n, P n → d_nat ≤ n := fun n hn => Nat.find_min' (p := P) hP hn
  -- Convert to ULift ℤ
  set d : ULift.{u} ℤ := ⟨(d_nat : ℤ)⟩ with hd_def
  have hd_pos : d.down > 0 := by simp [hd_def]; exact_mod_cast hd_nat_pos
  -- Step 2: Build image subgroup at x₀ and derive generator properties
  let H := H_at x₀ hx₀V
  have hH_ne : H ≠ ⊥ := by
    rw [ne_eq, AddSubgroup.eq_bot_iff_forall]; push_neg
    refine ⟨d, hd_in_range, ?_⟩
    rw [ne_eq, ULift.ext_iff, ULift.zero_down]; omega
  have hd_gen : ∀ h ∈ H, ∃ k : ℤ, h = ⟨k * d.down⟩ := by
    intro h hh
    obtain ⟨k, hk⟩ := hd_divides h.down hh
    exact ⟨k, by ext; simp only [hd_def]; rw [hk, mul_comm]⟩
  -- Step 3: Find a₁ generating stalk(R, x₀)
  obtain ⟨a₁, ha₁⟩ : d.down • gen_at x₀ hx₀V ∈ Set.range (i_x x₀) := hd_in_range
  have ha₁_ne : a₁ ≠ 0 := by
    intro h; rw [h, map_zero] at ha₁
    exact absurd (zsmul_generator_injective V x₀ hx₀V ((zero_smul _ _).trans ha₁)).symm
      (by omega)
  have ha₁_gen : ∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).obj R.val),
      ∃ k : ℤ, a = k • a₁ := by
    intro a; obtain ⟨n, hn⟩ := stalk_zeroOutsideInt_eq_zsmul_generator V x₀ hx₀V (i_x x₀ a)
    obtain ⟨k, hk⟩ := hd_gen ⟨n⟩
      (show (⟨n⟩ : ULift.{u} ℤ) ∈ H from ⟨a, show i_x x₀ a = (⟨n⟩ : ULift.{u} ℤ).down •
        gen_at x₀ hx₀V from hn⟩)
    have hn_eq : n = k * d.down := by simpa [mul_comm] using congrArg ULift.down hk
    exact ⟨k, hi_inj x₀ (by rw [map_zsmul, hn, hn_eq, mul_smul, ← ha₁])⟩
  -- Step 4: Represent a₁ by section s, restrict to W₀ ⊓ V
  obtain ⟨W₀, hx₀W₀, s₀, hs₀⟩ := TopCat.Presheaf.germ_exist R.val x₀ a₁
  set V₁ := W₀ ⊓ V with hV₁_def
  have hV₁V : V₁ ≤ V := inf_le_right
  have hx₀V₁ : x₀ ∈ V₁ := ⟨hx₀W₀, hx₀V⟩
  set s₁ := ConcreteCategory.hom (R.val.map (homOfLE (inf_le_left : V₁ ≤ W₀)).op) s₀
  have hs₁_germ : R.presheaf.germ V₁ x₀ hx₀V₁ s₁ = a₁ :=
    (TopCat.Presheaf.germ_res_apply R.val (homOfLE inf_le_left) x₀ hx₀V₁ s₀).trans hs₀
  -- Step 5: Shrink to where germ coefficient is constant
  -- i(s₁) is a section of zeroOutsideInt V over V₁. Its germ at x₀ is d.down • gen_at x₀.
  -- The section d.down • (restriction of gen_V to V₁) has the same germ at x₀.
  -- By germ_eq, they agree on some W ≤ V₁.
  set is₁ := i.val.app (op V₁) s₁ with his₁_def
  set gen_V_res := ConcreteCategory.hom
    ((TopCat.Sheaf.zeroOutsideInt V).val.map (homOfLE hV₁V).op)
    (TopCat.Sheaf.zeroOutsideInt.generator V) with hgen_V_res_def
  set d_gen_res := d.down • gen_V_res with hd_gen_res_def
  -- Germ of is₁ at x₀ = d.down • gen_at x₀
  have his₁_germ : (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V₁ x₀ hx₀V₁ is₁ =
      d.down • gen_at x₀ hx₀V := by
    rw [his₁_def,
      show (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V₁ x₀ hx₀V₁
        (i.val.app (op V₁) s₁) =
      i_x x₀ (R.presheaf.germ V₁ x₀ hx₀V₁ s₁) from
      (TopCat.Presheaf.stalkFunctor_map_germ_apply V₁ x₀ hx₀V₁ i.val s₁).symm,
      hs₁_germ, ha₁]
  -- Germ of d_gen_res at x₀ = d.down • gen_at x₀
  have hd_gen_res_germ :
      (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V₁ x₀ hx₀V₁ d_gen_res =
      d.down • gen_at x₀ hx₀V := by
    rw [hd_gen_res_def, map_zsmul, hgen_V_res_def]; congr 1
    exact TopCat.Presheaf.germ_res_apply (TopCat.Sheaf.zeroOutsideInt V).val
      (homOfLE hV₁V) x₀ hx₀V₁ (TopCat.Sheaf.zeroOutsideInt.generator V)
  obtain ⟨W, hx₀W, iW1, _, _⟩ :=
    TopCat.Presheaf.germ_eq (TopCat.Sheaf.zeroOutsideInt V).val x₀ hx₀V₁ hx₀V₁
      is₁ d_gen_res (his₁_germ.trans hd_gen_res_germ.symm)
  -- W ≤ V₁ ≤ V
  have hWV₁ : W ≤ V₁ := leOfHom iW1
  have hWV : W ≤ V := le_trans hWV₁ hV₁V
  -- W ≠ ⊥ (contains x₀)
  have hW_ne : W ≠ ⊥ := fun h => (Opens.mem_bot (x := x₀)).mp (h ▸ hx₀W)
  -- Key: at every x ∈ W, i_x(germ(s₁|_W, x)) = d.down • gen_at x
  -- This follows because is₁|_W = d_gen_res|_W (from hW_eq), and germs respect restriction
  have hcoeff_const : ∀ (x : X) (hxW : x ∈ W),
      i_x x (R.presheaf.germ W x hxW
        (ConcreteCategory.hom (R.val.map (homOfLE hWV₁).op) s₁)) =
      d.down • gen_at x (hWV hxW) := by
    intro x hxW
    -- Use: i_x(germ(s|_W, x)) = i_x(germ(s, x at V₁)) = germ(i(s), x at V₁)
    --   = germ(is₁, x at V₁) = germ(is₁|_W, x) ... = germ(d_gen_res|_W, x) = ...
    -- Simplify via: everything factors through germ_res_apply + stalkFunctor_map_germ
    calc i_x x (R.presheaf.germ W x hxW
          (ConcreteCategory.hom (R.val.map (homOfLE hWV₁).op) s₁))
        = i_x x (R.presheaf.germ V₁ x (hWV₁ hxW) s₁) := by
          congr 1
          exact TopCat.Presheaf.germ_res_apply R.val (homOfLE hWV₁) x hxW s₁
      _ = (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V₁ x (hWV₁ hxW) is₁ := by
          rw [his₁_def]
          show ConcreteCategory.hom
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map i.val)
              (ConcreteCategory.hom (TopCat.Presheaf.germ R.val V₁ x (hWV₁ hxW)) s₁) =
            ConcreteCategory.hom (TopCat.Presheaf.germ
              (TopCat.Sheaf.zeroOutsideInt V).val V₁ x (hWV₁ hxW))
              (ConcreteCategory.hom (i.val.app (op V₁)) s₁)
          exact TopCat.Presheaf.stalkFunctor_map_germ_apply V₁ x (hWV₁ hxW) i.val s₁
      _ = (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V₁ x (hWV₁ hxW) d_gen_res := by
          rw [← TopCat.Presheaf.germ_res_apply
              (TopCat.Sheaf.zeroOutsideInt V).val (homOfLE hWV₁) x hxW is₁,
            ← TopCat.Presheaf.germ_res_apply
              (TopCat.Sheaf.zeroOutsideInt V).val (homOfLE hWV₁) x hxW d_gen_res]; congr 1
      _ = d.down • gen_at x (hWV hxW) := by
          rw [hd_gen_res_def, map_zsmul, hgen_V_res_def]; congr 1
          exact TopCat.Presheaf.germ_res_apply (TopCat.Sheaf.zeroOutsideInt V).val
            (homOfLE hV₁V) x (hWV₁ hxW) (TopCat.Sheaf.zeroOutsideInt.generator V)
  -- Restrict s₁ to W
  set s_W := ConcreteCategory.hom (R.val.map (homOfLE hWV₁).op) s₁ with hs_W_def
  refine ⟨W, hWV, hW_ne, s_W, fun x hxW => ?_⟩
  -- At x ∈ W: i_x(germ(s_W, x)) = d.down • gen_at x (from hcoeff_const)
  have hcoeff_x := hcoeff_const x hxW
  rw [hs_W_def] at hcoeff_x ⊢
  constructor
  · -- germ(s_W, x) ≠ 0: since i_x(germ(s_W, x)) = d.down • gen_at x ≠ 0, and i_x injective
    intro h_zero; rw [h_zero, map_zero] at hcoeff_x
    exact absurd (zsmul_generator_injective V x (hWV hxW)
      ((zero_smul _ _).trans hcoeff_x)).symm (by omega)
  · -- Every stalk element a is a multiple of germ(s_W, x).
    -- Strategy: d.down generates the image subgroup at x (not just at x₀),
    -- because d_nat was chosen MINIMAL via Nat.find. At x, the generator d_x
    -- satisfies d_x | d.down (since d.down ∈ image at x from hcoeff_x) and
    -- d.down ≤ d_x (minimality), forcing d_x = d.down.
    intro a; obtain ⟨n, hn⟩ := stalk_zeroOutsideInt_eq_zsmul_generator V x (hWV hxW) (i_x x a)
    -- d.down • gen_at x ∈ range(i_x x) (from hcoeff_x)
    have hd_in_Hx : d.down • gen_at x (hWV hxW) ∈ Set.range (i_x x) := ⟨_, hcoeff_x⟩
    have hHx_ne : H_at x (hWV hxW) ≠ ⊥ := by
      rw [ne_eq, AddSubgroup.eq_bot_iff_forall]; push_neg
      exact ⟨d, hd_in_Hx, by rw [ne_eq, ULift.ext_iff, ULift.zero_down]; omega⟩
    -- Get generator d_x of image subgroup at x
    obtain ⟨d_x, hd_x_mem, hd_x_pos, hd_x_gen⟩ := ulift_int_subgroup_cyclic _ hHx_ne
    -- d_x generates image subgroup at x, so P(d_x.down.toNat) holds
    have hP_dx : P d_x.down.toNat := by
      refine ⟨Int.pos_iff_toNat_pos.mp hd_x_pos, x, hWV hxW, ?_, ?_⟩
      · rwa [Int.toNat_of_nonneg (le_of_lt hd_x_pos)]
      · intro m hm
        obtain ⟨k, hk⟩ := hd_x_gen ⟨m⟩ hm
        rw [Int.toNat_of_nonneg (le_of_lt hd_x_pos)]
        exact ⟨k, by simpa [mul_comm] using congrArg ULift.down hk⟩
    -- Minimality: d_nat ≤ d_x.down.toNat
    have h_le : d_nat ≤ d_x.down.toNat := h_minimal _ hP_dx
    -- Also d_x | d.down (since d.down ∈ image subgroup at x)
    obtain ⟨k_div, hk_div⟩ := hd_x_gen d hd_in_Hx
    have hd_eq_k_dx : d.down = k_div * d_x.down := by
      simpa using congrArg ULift.down hk_div
    -- d.down ≤ d_x.down (from minimality) and d.down = k_div * d_x.down
    -- Forces k_div = 1 and d_x.down = d.down
    have hd_x_eq : d_x.down = d.down := by
      have h1 : (d_nat : ℤ) ≤ d_x.down := by
        rw [← Int.toNat_of_nonneg (le_of_lt hd_x_pos)]; exact_mod_cast h_le
      have hk_pos : 0 < k_div := by
        by_contra! hle; linarith [mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hd_x_pos)]
      have : k_div = 1 := le_antisymm (by
        by_contra! hgt; linarith [mul_lt_mul_of_pos_right hgt hd_x_pos]) hk_pos
      rw [this, one_mul] at hd_eq_k_dx; linarith
    -- Now d.down | n (since d_x generates at x and d_x.down = d.down)
    have hn_mem : (⟨n⟩ : ULift.{u} ℤ) ∈ H_at x (hWV hxW) :=
      ⟨a, show i_x x a = (⟨n⟩ : ULift.{u} ℤ).down • gen_at x (hWV hxW) from hn⟩
    obtain ⟨k₀, hk₀⟩ := hd_x_gen ⟨n⟩ hn_mem
    have hn_eq : n = k₀ * d.down := by simpa [hd_x_eq] using congrArg ULift.down hk₀
    exact ⟨k₀, hi_inj x (by rw [map_zsmul, hn, hn_eq, mul_smul, ← hcoeff_x])⟩

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
      ∀ (x : X) (_ : x ∈ V'),
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
      (∀ (x : X) (_ : x ∈ V'),
        Function.Bijective (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map j.val))) := by
  obtain ⟨V', hle, hne, s, hbij⟩ := exists_good_section V R i hR
  refine ⟨V', hle, hne, TopCat.Sheaf.zeroOutsideInt.sHom s, ?_, hbij⟩
  apply sheaf_mono_of_stalk_injective
  intro y; by_cases hy : y ∈ V'
  · exact (hbij y hy).1
  · intro a b _
    exact (stalk_zeroOutsideInt_zero_outside V' y hy a).trans
      (stalk_zeroOutsideInt_zero_outside V' y hy b).symm

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
    have hSE : S.ShortExact := shortExact_of_mono j
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
        compl_ne_univ_of_ne_bot hV'ne
      have hY_dim_lt : topologicalKrullDim Y < topologicalKrullDim X :=
        topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl hY_ne_univ
          (lt_of_le_of_lt (topologicalKrullDim_subspace_le (X := (↑X : Type u)) Y)
            (lt_of_lt_of_le hm le_top))
      -- Build SES via ClosedImmersionSES on (V')^c with CJ
      let ci : TopCat.of Y ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} ci).unit.app CJ
      haveI : Epi η := epi_unit_of_closedImmersion Y hYcl CJ
      let S' := ShortComplex.mk (kernel.ι η) η (kernel.condition η)
      have hSE' : S'.ShortExact := shortExact_of_epi η
      have hPush : Subsingleton (Sheaf.H S'.X₃ m) :=
        PushforwardHVanishing Y hYcl _ m (@ih (TopCat.of Y) _ m _ hY_dim_lt (lt_trans hY_dim_lt hm))
      -- Kernel vanishing: zero stalks everywhere → IsZero → vanishing
      have hKer : Subsingleton (Sheaf.H S'.X₁ m) := by
        apply subsingleton_sheafH_of_isZero'; apply sheaf_isZero_of_zero_stalks X; intro x a
        by_cases hxY : x ∈ Y
        · -- At points in (V')^c: closedIncl_unit_stalk_isIso gives S'.g iso → kernel stalk = 0
          haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S'.g.val) :=
            closedIncl_unit_stalk_isIso hYcl CJ ⟨x, hxY⟩
          exact stalk_zero_of_ses_g_iso hSE' x inferInstance a
        · exact stalk_zero_of_shortExact_kernel hSE' x (fun b =>
            cokernel_stalk_zero_of_stalk_surj j x
              (hj_stalk x (by rwa [hY_def, Set.mem_compl_iff, not_not] at hxY)).2 b) a
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
    have hSE : S.ShortExact := shortExact_of_epi f
    have hZV : Subsingleton (Sheaf.H S.X₂ m) :=
      zeroOutsideInt_cohomology_vanishing X ih hpos V hV m hm
    have hKer : Subsingleton (Sheaf.H S.X₁ (m + 1)) :=
      subsheaf_zeroOutsideInt_vanishing X ih hpos V (kernel f) (kernel.ι f) (m + 1)
        (lt_trans hm (by exact_mod_cast Nat.lt_succ_of_le le_rfl))
    exact subsingleton_sheafH_of_shortExact_third hSE m hZV hKer

-- Filtered diagram infrastructure, finitely generated vanishing, and
-- directLimit_cohomology_vanishing are in FiniteGeneratorReduction.lean.

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
    (_Z : Set X) (_hZ_closed : IsClosed _Z) (_ : _Z ≠ Set.univ)
    (_ : topologicalKrullDim (TopCat.of _Z) < topologicalKrullDim X)
    (_ : ↑n > topologicalKrullDim (TopCat.of _Z))
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (_ : S.ShortExact) (_ : S.X₂ = F)
    (_ : S.X₃ = (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl _hZ_closed)).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
          (TopCat.closedIncl _hZ_closed)).obj F)) :
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

