/-
  IrreducibleStep.lean — Assembly: irreducible positive-dimension vanishing

  Split from the original IrreducibleStep.lean. Contains:
  - zmul_bijective_of_index_match: algebra helper for stalk bijectivity
  - sHom_stalk_bijective_at: key stalk bijectivity at a point
  - exists_section_generating_stalks: finds section generating all stalks
  - exists_good_section: produces V' ⊆ V with stalk-bijective section
  - subsheaf_contains_zeroOutsideInt: subsheaf contains a zeroOutsideInt V'
  - subsheaf_zeroOutsideInt_vanishing: vanishing for subsheaves of zeroOutsideInt
  - epiImage_zeroOutsideInt_vanishing: vanishing for epi images
  - irreduciblePos_kernel_subsingleton: kernel vanishing
  - IrreduciblePosVanishing: main irreducible positive-dimension theorem
    (3 sorry's in FiniteGeneratorReduction.lean)
-/
import Aristotle.GrothendieckVanishing.main.SheafStalkAlgebra

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

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
      exact ⟨k, by have := congrArg ULift.down hk; simp at this; linarith⟩
  -- d_nat is the minimal positive generator among all points of V
  have hP_dec : DecidablePred P := Classical.decPred P
  set d_nat := Nat.find (p := P) hP with hd_nat_def
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
  have hd_mem : d.down • gen_at x₀ hx₀V ∈ Set.range (i_x x₀) := hd_in_range
  have hd_gen : ∀ h ∈ H, ∃ k : ℤ, h = ⟨k * d.down⟩ := by
    intro h hh
    obtain ⟨k, hk⟩ := hd_divides h.down hh
    exact ⟨k, by ext; simp only [hd_def]; rw [hk, mul_comm]⟩
  -- Step 3: Find a₁ generating stalk(R, x₀)
  obtain ⟨a₁, ha₁⟩ : d.down • gen_at x₀ hx₀V ∈ Set.range (i_x x₀) := hd_mem
  have ha₁_ne : a₁ ≠ 0 := by
    intro h; rw [h, map_zero] at ha₁
    -- ha₁ : 0 = d.down • gen_at x₀ hx₀V
    have : (0 : ℤ) = d.down :=
      zsmul_generator_injective V x₀ hx₀V ((zero_smul _ _).trans ha₁)
    linarith
  have ha₁_gen : ∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).obj R.val),
      ∃ k : ℤ, a = k • a₁ := by
    intro a
    obtain ⟨n, hn⟩ := stalk_zeroOutsideInt_eq_zsmul_generator V x₀ hx₀V (i_x x₀ a)
    obtain ⟨k, hk⟩ := hd_gen ⟨n⟩
      (show (⟨n⟩ : ULift.{u} ℤ) ∈ H from ⟨a, show i_x x₀ a = (⟨n⟩ : ULift.{u} ℤ).down •
        gen_at x₀ hx₀V from hn⟩)
    have hn_eq : n = k * d.down := by simpa using congrArg ULift.down hk
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
    rw [hd_gen_res_def, map_zsmul, hgen_V_res_def]
    congr 1
    exact TopCat.Presheaf.germ_res_apply (TopCat.Sheaf.zeroOutsideInt V).val
      (homOfLE hV₁V) x₀ hx₀V₁ (TopCat.Sheaf.zeroOutsideInt.generator V)
  -- Equal germs at x₀ → agree on some W ≤ V₁
  have hgerms_eq : (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V₁ x₀ hx₀V₁ is₁ =
      (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V₁ x₀ hx₀V₁ d_gen_res := by
    rw [his₁_germ, hd_gen_res_germ]
  obtain ⟨W, hx₀W, iW1, iW2, hW_eq⟩ :=
    TopCat.Presheaf.germ_eq (TopCat.Sheaf.zeroOutsideInt V).val x₀ hx₀V₁ hx₀V₁
      is₁ d_gen_res hgerms_eq
  -- W ≤ V₁ ≤ V
  have hWV₁ : W ≤ V₁ := leOfHom iW1
  have hWV : W ≤ V := le_trans hWV₁ hV₁V
  -- W ≠ ⊥ (contains x₀)
  have hW_ne : W ≠ ⊥ := by
    intro h; exact (Opens.mem_bot (x := x₀)).mp (h ▸ hx₀W)
  -- On W, the sections is₁|_W and d_gen_res|_W agree (from hW_eq)
  have hiW : iW1 = iW2 := Subsingleton.elim _ _
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
          -- is₁ and d_gen_res have equal germs at x (from hW_eq via germ_res)
          have h_eq_sec : ConcreteCategory.hom
              ((TopCat.Sheaf.zeroOutsideInt V).val.map iW1.op) is₁ =
            ConcreteCategory.hom
              ((TopCat.Sheaf.zeroOutsideInt V).val.map iW1.op) d_gen_res := by
            rw [hW_eq, hiW]
          -- Both sides are germ_res from V₁ to W; use germ_res_apply in reverse
          have hg1 := TopCat.Presheaf.germ_res_apply
            (TopCat.Sheaf.zeroOutsideInt V).val (homOfLE hWV₁) x hxW is₁
          have hg2 := TopCat.Presheaf.germ_res_apply
            (TopCat.Sheaf.zeroOutsideInt V).val (homOfLE hWV₁) x hxW d_gen_res
          rw [← hg1, ← hg2]; congr 1
      _ = d.down • (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V₁ x (hWV₁ hxW) gen_V_res := by
          rw [hd_gen_res_def, map_zsmul]
      _ = d.down • gen_at x (hWV hxW) := by
          congr 1; rw [hgen_V_res_def]
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
    intro h_zero
    rw [h_zero, map_zero] at hcoeff_x
    -- hcoeff_x : 0 = d.down • gen_at x (hWV hxW)
    have : (0 : ℤ) = d.down :=
      zsmul_generator_injective V x (hWV hxW) ((zero_smul _ _).trans hcoeff_x)
    linarith
  · -- Every stalk element a is a multiple of germ(s_W, x).
    -- Strategy: d.down generates the image subgroup at x (not just at x₀),
    -- because d_nat was chosen MINIMAL via Nat.find. At x, the generator d_x
    -- satisfies d_x | d.down (since d.down ∈ image at x from hcoeff_x) and
    -- d.down ≤ d_x (minimality), forcing d_x = d.down.
    intro a
    obtain ⟨n, hn⟩ := stalk_zeroOutsideInt_eq_zsmul_generator V x (hWV hxW) (i_x x a)
    -- d.down • gen_at x ∈ range(i_x x) (from hcoeff_x)
    have hd_in_Hx : d.down • gen_at x (hWV hxW) ∈ Set.range (i_x x) :=
      ⟨_, hcoeff_x⟩
    -- Image subgroup at x is nonzero (contains d.down)
    have hHx_ne : H_at x (hWV hxW) ≠ ⊥ := by
      rw [ne_eq, AddSubgroup.eq_bot_iff_forall]; push_neg
      refine ⟨d, hd_in_Hx, ?_⟩
      rw [ne_eq, ULift.ext_iff, ULift.zero_down]; omega
    -- Get generator d_x of image subgroup at x
    obtain ⟨d_x, hd_x_mem, hd_x_pos, hd_x_gen⟩ := ulift_int_subgroup_cyclic _ hHx_ne
    -- d_x generates image subgroup at x, so P(d_x.down.toNat) holds
    have hP_dx : P d_x.down.toNat := by
      refine ⟨Int.pos_iff_toNat_pos.mp hd_x_pos, x, hWV hxW, ?_, ?_⟩
      · rwa [Int.toNat_of_nonneg (le_of_lt hd_x_pos)]
      · intro m hm
        obtain ⟨k, hk⟩ := hd_x_gen ⟨m⟩ hm
        rw [Int.toNat_of_nonneg (le_of_lt hd_x_pos)]
        exact ⟨k, by have := congrArg ULift.down hk; simp at this; linarith⟩
    -- Minimality: d_nat ≤ d_x.down.toNat
    have h_le : d_nat ≤ d_x.down.toNat := h_minimal _ hP_dx
    -- Also d_x | d.down (since d.down ∈ image subgroup at x)
    have hd_mem_Hx : (d : ULift.{u} ℤ) ∈ H_at x (hWV hxW) := hd_in_Hx
    obtain ⟨k_div, hk_div⟩ := hd_x_gen d hd_mem_Hx
    have hd_eq_k_dx : d.down = k_div * d_x.down := by
      have := congrArg ULift.down hk_div; simp at this; linarith
    -- d.down ≤ d_x.down (from minimality) and d.down = k_div * d_x.down
    -- Forces k_div = 1 and d_x.down = d.down
    have hd_x_eq : d_x.down = d.down := by
      have h1 : (d_nat : ℤ) ≤ d_x.down := by
        have := Int.toNat_of_nonneg (le_of_lt hd_x_pos)
        rw [← this]; exact_mod_cast h_le
      -- h1 : d.down ≤ d_x.down (since d.down = ↑d_nat)
      -- hd_eq_k_dx : d.down = k_div * d_x.down
      -- hd_x_pos : d_x.down > 0, hd_pos : d.down > 0
      -- k_div > 0 (since d.down > 0 and d_x.down > 0)
      -- k_div * d_x.down ≤ d_x.down, so (k_div - 1) * d_x.down ≤ 0
      -- combined with d_x.down > 0 gives k_div ≤ 1, so k_div = 1
      have hk_pos : 0 < k_div := by
        by_contra hle; push_neg at hle
        have := mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hd_x_pos)
        linarith
      have hk_le1 : k_div ≤ 1 := by
        by_contra hgt; push_neg at hgt
        have : 1 * d_x.down < k_div * d_x.down :=
          mul_lt_mul_of_pos_right hgt hd_x_pos
        linarith
      have hk_eq : k_div = 1 := le_antisymm hk_le1 hk_pos
      rw [hk_eq, one_mul] at hd_eq_k_dx; linarith
    -- Now d.down | n (since d_x generates at x and d_x.down = d.down)
    have hn_mem : (⟨n⟩ : ULift.{u} ℤ) ∈ H_at x (hWV hxW) :=
      ⟨a, show i_x x a = (⟨n⟩ : ULift.{u} ℤ).down • gen_at x (hWV hxW) from hn⟩
    obtain ⟨k₀, hk₀⟩ := hd_x_gen ⟨n⟩ hn_mem
    have hn_eq : n = k₀ * d.down := by
      have h1 := congrArg ULift.down hk₀
      simp at h1; rw [hd_x_eq] at h1; linarith
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

-- ext_comm_filtered_colimit_mono, filtered diagram infrastructure, finitely generated
-- vanishing, and directLimit_cohomology_vanishing are in FiniteGeneratorReduction.lean.

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

