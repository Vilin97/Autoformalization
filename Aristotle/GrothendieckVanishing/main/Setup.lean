/-
  Setup.lean -- Category instances and flasque acyclicity for Grothendieck vanishing

  Provides:
  1. Categorical infrastructure for sheaf cohomology on AddCommGrpCat
  2. FlasqueVanishing (PROVED from 4 sub-lemmas adapting Brian Nugent's Mathlib PR #35790)
  3. ReducibleVanishing (sorry -- needs j_! extension by zero)
  4. IrreduciblePosVanishing (sorry -- needs j_! or Prop 2.9)

  The proof of FlasqueVanishing follows Brian Nugent's approach:
  - Base case (H^1 = 0): Ext LES + associativity of Ext composition + Zorn surjectivity
  - Induction step: injective presentation + quotient-preserves-flasque + dimension shift

  Sub-lemmas (sorry):
  - epi_app_of_shortExact_flasque: Zorn argument for surjectivity of sections
  - isFlasque_X₃_of_shortExact: quotient of flasques is flasque
  - isFlasque_of_injective: injective sheaves are flasque
  - ext_zero_map_surjective: Ext(Z,I,0) -> Ext(Z,Q,0) surjective via adjunction
-/
import Mathlib
import Aristotle.GrothendieckVanishing.main.Auxiliary

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

instance : HasSeparator AddCommGrpCat.{u} where
  hasSeparator := by
    use AddCommGrpCat.of (ULift ℤ)
    intro A B f g h
    simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq',
      ULift.forall]
    intro x
    specialize h (AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun y => y • x) fun y z => by simp only [add_smul])) 1
    aesop

instance : IsGrothendieckAbelian.{u} AddCommGrpCat.{u} where

instance (X : TopCat.{u}) : Abelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

/-! ## Flasque sheaf sub-lemmas

The four sub-lemmas below are adapted from Brian Nugent's Mathlib PR #35790.
Together they imply `FlasqueVanishing` (proved below). Each is a self-contained
statement that can be attacked independently.
-/

/-- A sheaf of abelian groups is **flasque** if all restriction maps are epi.
    This is equivalent to surjectivity of restriction on sections. -/
def IsFlasqueSheaf {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op)

/-! ### Helper: sections functor and evaluated exactness -/

/-- The sections-at-V functor: Sheaf → AddCommGrpCat. -/
private noncomputable def sectionsAt {X : TopCat.{u}} (V : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op V)

-- Typeclass resolution for the composite functor needs extra heartbeats.
set_option maxHeartbeats 800000 in
private noncomputable instance sectionsAt_preservesZeroMorphisms
    {X : TopCat.{u}} (V : Opens X) :
    (sectionsAt (X := X) V).PreservesZeroMorphisms :=
  inferInstanceAs
    ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op V)).PreservesZeroMorphisms)

-- The sections functor preserves left homology of a SES with mono f:
-- it preserves the kernel of g (limit-preserving) and the coimage of f
-- (f is mono ⟹ the coimage map is an iso, whose cokernel is trivially preserved).
set_option maxHeartbeats 1600000 in
private lemma sectionsAt_preservesLeftHomologyOf {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (V : Opens X) :
    (sectionsAt V).PreservesLeftHomologyOf S := by
  constructor; intro h; constructor
  · -- sectionsAt V preserves the kernel of S.g (it preserves all limits)
    show PreservesLimit _ (sheafToPresheaf _ _ ⋙ _)
    infer_instance
  · -- sectionsAt V preserves the cokernel of h.f'
    -- Since S is exact with mono f, h.f' is an iso (epi + mono),
    -- so its cokernel is 0, which is trivially preserved.
    haveI : Mono S.f := hS.mono_f
    haveI : Mono h.f' := by
      constructor; intro Z a b hab
      have : a ≫ S.f = b ≫ S.f := by
        rw [← h.f'_i, ← Category.assoc, hab, Category.assoc]
      exact (cancel_mono S.f).mp this
    haveI : Epi h.f' := hS.exact.epi_f' h
    haveI : IsIso h.f' := isIso_of_mono_of_epi h.f'
    haveI hz1 : IsZero (cokernel h.f') := isZero_cokernel_of_epi h.f'
    haveI hz2 : IsZero
        ((sectionsAt (X := X) V).obj (cokernel h.f')) :=
      Functor.map_isZero _ hz1
    haveI hz3 : IsZero
        (cokernel ((sectionsAt (X := X) V).map h.f')) :=
      isZero_cokernel_of_epi _
    -- cokernelComparison : cokernel(F(f')) ⟶ F(cokernel(f'))
    -- Both sides are zero, so it's an iso.
    haveI : IsIso
        (cokernelComparison h.f' (sectionsAt (X := X) V)) :=
      ⟨⟨hz2.to_ _, hz3.eq_of_src _ _, hz2.eq_of_src _ _⟩⟩
    exact PreservesCokernel.of_iso_comparison _ _

-- For a SES of sheaves, the evaluated sequence at V is exact:
-- if g_V(x) = 0, then x is in the image of f_V.
set_option maxHeartbeats 1600000 in
private lemma sections_exact_of_shortExact {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (V : Opens X)
    (x : S.X₂.val.obj (op V))
    (hx : ConcreteCategory.hom (S.g.val.app (op V)) x = 0) :
    ∃ a : S.X₁.val.obj (op V),
      ConcreteCategory.hom (S.f.val.app (op V)) a = x := by
  have hexact : (S.map (sectionsAt V)).Exact := by
    haveI := sectionsAt_preservesLeftHomologyOf hS V
    exact hS.exact.map_of_preservesLeftHomologyOf (sectionsAt V)
  exact (ShortComplex.ab_exact_iff _).mp hexact x hx

/-! ### Zero condition and mono for the evaluated short complex -/

private lemma eval_comp_zero {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) (V : Opens X) :
    S.f.val.app (op V) ≫ S.g.val.app (op V) = 0 := by
  have h1 : S.f.val.app (op V) ≫ S.g.val.app (op V) =
      (S.f.val ≫ S.g.val).app (op V) := by simp
  rw [h1]; change (S.f ≫ S.g).val.app (op V) = 0; rw [S.zero]; aesop_cat

set_option maxHeartbeats 400000 in
private lemma mono_f_app {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (V : Opens X) :
    Mono (S.f.val.app (op V)) := by
  haveI : Mono S.f := hS.mono_f
  haveI : Mono S.f.val := by
    change Mono ((sheafToPresheaf _ _).map S.f); infer_instance
  exact (NatTrans.mono_iff_mono_app S.f.val).mp ‹_› (op V)

-- In a thin category (Opens X), any two parallel morphisms are equal,
-- so presheaf restriction maps agree regardless of which morphism is used.
private lemma presheaf_map_eq {X : TopCat.{u}}
    (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {U V : Opens X} (f g : U ⟶ V) (s : F.obj (op V)) :
    F.map f.op s = F.map g.op s := by
  have : f = g := Subsingleton.elim _ _; rw [this]

-- Extension preorder on partial lifts (V, t):
-- (V₁,t₁) ≤ (V₂,t₂) iff V₁ ≤ V₂ and t₂|_{V₁} = t₁.
private noncomputable instance sigmaPreorder {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) :
    Preorder (Σ V : Opens X, S.X₂.val.obj (op V)) where
  le p q := ∃ h : p.1 ≤ q.1,
    ConcreteCategory.hom (S.X₂.val.map (homOfLE h).op) q.2 = p.2
  le_refl p := ⟨le_refl _, by simp⟩
  le_trans p q r := fun ⟨h₁, ht₁⟩ ⟨h₂, ht₂⟩ =>
    ⟨le_trans h₁ h₂, by
      have : (homOfLE (le_trans h₁ h₂)).op =
          (homOfLE h₂).op ≫ (homOfLE h₁).op := rfl
      simp only [this, Functor.map_comp, AddCommGrpCat.hom_comp,
        AddMonoidHom.coe_comp, Function.comp_apply, ht₂, ht₁]⟩

-- Binary gluing: given compatible sections on V₀ and W, produce a section on V₀ ⊔ W.
set_option maxHeartbeats 3200000 in
private lemma binaryGlue_exists {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {V₀ W : Opens X} (t₀ : F.val.obj (op V₀)) (t'' : F.val.obj (op W))
    (hcompat : ConcreteCategory.hom (F.val.map (homOfLE inf_le_right).op) t'' =
      ConcreteCategory.hom (F.val.map (homOfLE inf_le_left).op) t₀) :
    ∃ t_new : F.val.obj (op (V₀ ⊔ W)),
      ConcreteCategory.hom (F.val.map (homOfLE le_sup_left).op) t_new = t₀ ∧
      ConcreteCategory.hom (F.val.map (homOfLE le_sup_right).op) t_new = t'' := by
  let BU : Bool → Opens X := fun | false => V₀ | true => W
  let Bsf : (b : Bool) → F.val.obj (op (BU b)) := fun | false => t₀ | true => t''
  have hcover : V₀ ⊔ W ≤ ⨆ b, BU b := by
    intro y hy; simp only [Opens.mem_iSup]
    rcases hy with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  have hsup_eq : ⨆ b, BU b = V₀ ⊔ W :=
    le_antisymm (iSup_le fun b => by cases b <;> simp [BU]) hcover
  have hcompat_glue : TopCat.Presheaf.IsCompatible F.val BU Bsf := by
    intro i j; match i, j with
    | false, false => rfl
    | false, true => exact hcompat.symm
    | true, false =>
      rw [show (W).infLELeft V₀ = eqToHom (inf_comm W V₀) ≫ homOfLE inf_le_right
            from Subsingleton.elim _ _,
          show (W).infLERight V₀ = eqToHom (inf_comm W V₀) ≫ homOfLE inf_le_left
            from Subsingleton.elim _ _,
          op_comp, Functor.map_comp, CategoryTheory.comp_apply,
          op_comp, Functor.map_comp, CategoryTheory.comp_apply, hcompat]
    | true, true => rfl
  obtain ⟨t_new, ht_new, _⟩ := TopCat.Sheaf.existsUnique_gluing' F BU (V₀ ⊔ W)
    (fun b => homOfLE (by cases b <;> simp [BU])) (hsup_eq ▸ le_rfl) Bsf hcompat_glue
  have h0 := ht_new false; simp only [BU, Bsf] at h0
  have h1 := ht_new true; simp only [BU, Bsf] at h1
  exact ⟨t_new, h0, h1⟩

-- Zorn argument for surjectivity of sections (Nugent, PR #35790).
-- Given s : X₃(U), Zorn on P = {(V,t) | V ≤ U, g(t) = s|_V}.
-- Maximal V₀ = U by local surjectivity + exactness + flasqueness.
-- Two sorry's remain: (1) chain upper bound via sheaf gluing, (2) binary gluing
-- + contradiction. All other ingredients (exactness of evaluated SES, naturality,
-- flasque extension, compatibility) are proved above.
set_option maxHeartbeats 12800000 in
theorem epi_app_of_shortExact_flasque {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (hFlasque₁ : IsFlasqueSheaf S.X₁) (U : Opens X) :
    Epi (S.g.val.app (op U)) := by
  rw [AddCommGrpCat.epi_iff_surjective]; intro s
  haveI : Epi S.g := hS.epi_g
  -- The set P of partial lifts: (V, t) with V ≤ U, g(t) = s|_V
  let P : Set (Σ V : Opens X, S.X₂.val.obj (op V)) := fun p =>
    ∃ h : p.1 ≤ U, ConcreteCategory.hom (S.g.val.app (op p.1)) p.2 =
      ConcreteCategory.hom (S.X₃.val.map (homOfLE h).op) s
  -- P is nonempty: (⊥, 0) ∈ P
  have hbot : (⟨⊥, 0⟩ : Σ V : Opens X, S.X₂.val.obj (op V)) ∈ P := by
    refine ⟨bot_le, ?_⟩
    have ht := isTerminal_sheaf_bot S.X₃
    have hsub : ∀ (a b : S.X₃.val.obj (op ⊥)), a = b := by
      intro a b
      have h₁ : a = (0 : S.X₃.val.obj (op ⊥)) := by
        have := congr_arg (fun f => (ConcreteCategory.hom f) a)
          (show (𝟙 _ : S.X₃.val.obj (op ⊥) ⟶ _) = 0 from ht.hom_ext _ _)
        simpa using this
      have h₂ : b = (0 : S.X₃.val.obj (op ⊥)) := by
        have := congr_arg (fun f => (ConcreteCategory.hom f) b)
          (show (𝟙 _ : S.X₃.val.obj (op ⊥) ⟶ _) = 0 from ht.hom_ext _ _)
        simpa using this
      rw [h₁, h₂]
    exact hsub _ _
  -- Local surjectivity
  have hls : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} S.g).mpr inferInstance
  -- Extension preorder
  let ext_le : (Σ V : Opens X, S.X₂.val.obj (op V)) →
      (Σ V : Opens X, S.X₂.val.obj (op V)) → Prop :=
    fun p q => ∃ h : p.1 ≤ q.1, S.X₂.val.map (homOfLE h).op q.2 = p.2
  have ext_le_refl : ∀ p, ext_le p p := fun _ => ⟨le_refl _, by simp⟩
  have ext_le_trans : ∀ p q r, ext_le p q → ext_le q r → ext_le p r :=
    fun _ _ _ ⟨h₁, e₁⟩ ⟨h₂, e₂⟩ => ⟨h₁.trans h₂, by
      rw [show (homOfLE (h₁.trans h₂) : _ ⟶ _) = homOfLE h₁ ≫ homOfLE h₂ from rfl,
        op_comp, Functor.map_comp, CategoryTheory.comp_apply, e₂, e₁]⟩
  let myPO : Preorder (Σ V : Opens X, S.X₂.val.obj (op V)) :=
    { le := ext_le, le_refl := ext_le_refl, le_trans := ext_le_trans,
      lt := fun p q => ext_le p q ∧ ¬ext_le q p, lt_iff_le_not_ge := fun _ _ => Iff.rfl }
  -- Zorn
  obtain ⟨⟨V₀, t₀⟩, ⟨hV₀U, ht₀⟩, hmax⟩ :=
    @zorn_le₀ _ myPO {p | p ∈ P} (fun c hcP hchain => by
    by_cases hc : c.Nonempty
    · set Vsup := ⨆ (p : c), (p : Σ V : Opens X, S.X₂.val.obj (op V)).1
      have hVsup_le : Vsup ≤ U := iSup_le fun ⟨_, hp⟩ => (hcP hp).choose
      have hcompat : TopCat.Presheaf.IsCompatible S.X₂.val
          (fun (p : c) => (p : Σ V : Opens X, S.X₂.val.obj (op V)).1)
          (fun (p : c) => (p : Σ V : Opens X, S.X₂.val.obj (op V)).2) := by
        intro ⟨p, hp⟩ ⟨q, hq⟩
        rcases hchain.total hp hq with ⟨h, e⟩ | ⟨h, e⟩
        · rw [show (p.1).infLERight q.1 = (p.1).infLELeft q.1 ≫ homOfLE h from rfl,
            op_comp, Functor.map_comp, CategoryTheory.comp_apply, e]
        · rw [show (p.1).infLELeft q.1 = (p.1).infLERight q.1 ≫ homOfLE h from rfl,
            op_comp, Functor.map_comp, CategoryTheory.comp_apply, e]
      obtain ⟨t_gl, ht_gl, _⟩ := TopCat.Sheaf.existsUnique_gluing' S.X₂
          (fun (p : c) => (p : Σ V : Opens X, S.X₂.val.obj (op V)).1) Vsup
          (fun p => homOfLE (le_iSup (fun (q : c) =>
            (q : Σ V : Opens X, S.X₂.val.obj (op V)).1) p))
          le_rfl
          (fun (p : c) => (p : Σ V : Opens X, S.X₂.val.obj (op V)).2) hcompat
      refine ⟨⟨Vsup, t_gl⟩, ⟨hVsup_le, ?_⟩, fun ⟨p, hp⟩ hpP =>
        ⟨le_iSup (fun (q : c) =>
          (q : Σ V : Opens X, S.X₂.val.obj (op V)).1) ⟨⟨p, hp⟩, hpP⟩,
          ht_gl ⟨⟨p, hp⟩, hpP⟩⟩⟩
      apply TopCat.Sheaf.eq_of_locally_eq' S.X₃
        (fun (p : c) => (p : Σ V : Opens X, S.X₂.val.obj (op V)).1) Vsup
        (fun p => homOfLE (le_iSup (fun (q : c) =>
          (q : Σ V : Opens X, S.X₂.val.obj (op V)).1) p))
        le_rfl
      intro ⟨p, hp⟩
      rw [← S.g.val.naturality_apply _ t_gl, ht_gl ⟨p, hp⟩, (hcP hp).choose_spec]
      simp only [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
      exact presheaf_map_eq S.X₃.val _ _ s
    · exact ⟨⟨⊥, 0⟩, hbot, fun _ hz => absurd ⟨_, hz⟩ hc⟩)
  -- Maximal V₀ = U
  suffices V₀ = U by subst this; exact ⟨t₀, by rw [ht₀]; simp⟩
  by_contra hne
  have hlt : V₀ < U := lt_of_le_of_ne hV₀U hne
  obtain ⟨x, hxU, hxV₀⟩ := Set.not_subset.mp hlt.2
  obtain ⟨W, iWU, ⟨t', ht'⟩, hxW⟩ := (hls.imageSieve_mem s) x hxU
  have hWU : W ≤ U := leOfHom iWU
  have hdiff_ker : S.g.val.app (op (V₀ ⊓ W))
      (S.X₂.val.map (homOfLE inf_le_left).op t₀ -
       S.X₂.val.map (homOfLE inf_le_right).op t') = 0 := by
    simp only [map_sub]
    rw [S.g.val.naturality_apply _ t₀, ht₀, S.g.val.naturality_apply _ t', ht', sub_eq_zero]
    simp only [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact presheaf_map_eq S.X₃.val _ _ s
  obtain ⟨a, ha⟩ := sections_exact_of_shortExact hS (V₀ ⊓ W) _ hdiff_ker
  have hfl := hFlasque₁ (homOfLE inf_le_right : V₀ ⊓ W ⟶ W)
  rw [AddCommGrpCat.epi_iff_surjective] at hfl
  obtain ⟨ahat, hahat⟩ := hfl a
  set t'' := t' + S.f.val.app (op W) ahat with ht''_def
  have hgt'' : S.g.val.app (op W) t'' = S.X₃.val.map (homOfLE hWU).op s := by
    simp only [ht''_def, map_add]
    have hgf : S.g.val.app (op W) (S.f.val.app (op W) ahat) = 0 := by
      change (S.f.val.app (op W) ≫ S.g.val.app (op W)) ahat = 0
      rw [eval_comp_zero]; simp
    rw [hgf, add_zero, ht']; exact presheaf_map_eq S.X₃.val _ _ s
  have hcompat_patch : S.X₂.val.map (homOfLE inf_le_right).op t'' =
      S.X₂.val.map (homOfLE inf_le_left).op t₀ := by
    simp only [ht''_def, map_add]
    rw [show S.X₂.val.map (homOfLE inf_le_right).op (S.f.val.app (op W) ahat) =
      S.f.val.app (op (V₀ ⊓ W)) (S.X₁.val.map (homOfLE inf_le_right).op ahat) from
      (S.f.val.naturality_apply (homOfLE inf_le_right).op ahat).symm, hahat, ha]; abel
  let BU : Bool → Opens X := fun b => match b with | false => V₀ | true => W
  let Bsf : (b : Bool) → S.X₂.val.obj (op (BU b)) :=
    fun b => match b with | false => t₀ | true => t''
  have hsup_eq : ⨆ b, BU b = V₀ ⊔ W := le_antisymm
    (iSup_le fun b => by cases b <;> simp [BU])
    (by intro y hy; simp only [Opens.mem_iSup]; rcases hy with h | h;
        exact ⟨false, h⟩; exact ⟨true, h⟩)
  have hcompat_glue : TopCat.Presheaf.IsCompatible S.X₂.val BU Bsf := by
    intro i j; match i, j with
    | false, false => rfl
    | false, true => exact hcompat_patch.symm
    | true, false =>
      show S.X₂.val.map (W.infLELeft V₀).op t'' = S.X₂.val.map (W.infLERight V₀).op t₀
      rw [show (W).infLELeft V₀ = eqToHom (inf_comm W V₀) ≫ homOfLE inf_le_right
            from Subsingleton.elim _ _,
          show (W).infLERight V₀ = eqToHom (inf_comm W V₀) ≫ homOfLE inf_le_left
            from Subsingleton.elim _ _,
        op_comp, Functor.map_comp, CategoryTheory.comp_apply,
          op_comp, Functor.map_comp, CategoryTheory.comp_apply,
          hcompat_patch]
    | true, true => rfl
  obtain ⟨t_new, ht_new, _⟩ := TopCat.Sheaf.existsUnique_gluing' S.X₂ BU (V₀ ⊔ W)
    (fun b => homOfLE (by cases b <;> simp [BU])) (hsup_eq ▸ le_rfl) Bsf hcompat_glue
  have h_new_inP : (⟨V₀ ⊔ W, t_new⟩ : Σ V : Opens X, S.X₂.val.obj (op V)) ∈ P := by
    refine ⟨sup_le hV₀U hWU, ?_⟩
    apply TopCat.Sheaf.eq_of_locally_eq' S.X₃ BU (V₀ ⊔ W)
      (fun b => homOfLE (by cases b <;> simp [BU])) (hsup_eq ▸ le_rfl)
    intro b; cases b
    · rw [← S.g.val.naturality_apply _ t_new]; simp only [BU, Bsf]
      have h0 := ht_new false; simp only [BU, Bsf] at h0; rw [h0, ht₀]
      simp only [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
      exact presheaf_map_eq S.X₃.val _ _ s
    · rw [← S.g.val.naturality_apply _ t_new]; simp only [BU, Bsf]
      have h1 := ht_new true; simp only [BU, Bsf] at h1; rw [h1, hgt'']
      simp only [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
      exact presheaf_map_eq S.X₃.val _ _ s
  have h_ext : @LE.le _ myPO.toLE ⟨V₀, t₀⟩ ⟨V₀ ⊔ W, t_new⟩ := by
    refine ⟨le_sup_left, ?_⟩
    have h0 := ht_new false; simp only [BU, Bsf] at h0; exact h0
  exact hxV₀ ((hmax h_new_inP h_ext).1 (Or.inr hxW))

/-- **Quotient preserves flasqueness** (Nugent, PR #35790).
    If `F'` and `G` are flasque in `0 -> F' -> G -> H -> 0`, then `H` is flasque.
    Follows from `epi_app_of_shortExact_flasque`: the restriction map for `H` factors
    through the epi `G(U) -> H(U)` composed with the restriction of `G`. -/
theorem isFlasque_X₃_of_shortExact {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (h₁ : IsFlasqueSheaf S.X₁) (h₂ : IsFlasqueSheaf S.X₂) :
    IsFlasqueSheaf S.X₃ := by
  intro U V j
  have hg_U : Epi (S.g.val.app (op U)) := epi_app_of_shortExact_flasque hS h₁ U
  have hres₂ : Epi (S.X₂.val.map j.op) := h₂ j
  rw [AddCommGrpCat.epi_iff_surjective] at hg_U hres₂ ⊢
  intro z
  obtain ⟨w, hw⟩ := hg_U z
  obtain ⟨x, hx⟩ := hres₂ w
  refine ⟨ConcreteCategory.hom (S.g.val.app (op V)) x, ?_⟩
  have : ConcreteCategory.hom (S.X₂.val.map j.op ≫ S.g.val.app (op U)) x =
         ConcreteCategory.hom (S.g.val.app (op V) ≫ S.X₃.val.map j.op) x := by
    rw [S.g.val.naturality j.op]
  simp only [AddCommGrpCat.hom_comp] at this
  exact this.symm.trans (by simp [hx, hw])

/-! ### Free abelian sheaf construction for injective → flasque (Aristotle 8f42abaa) -/

noncomputable section FreeAbSheaf

variable {X : TopCat.{u}}

private def freeAbPresheaf (U : Opens X) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  yoneda.obj U ⋙ AddCommGrpCat.free

private def freeAbSheaf (U : Opens X) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology (T := X)) AddCommGrpCat.{u}).obj
    (freeAbPresheaf U)

private def freeAbSheafMap {U V : Opens X} (i : U ⟶ V) : freeAbSheaf U ⟶ freeAbSheaf V :=
  (presheafToSheaf (Opens.grothendieckTopology (T := X)) AddCommGrpCat.{u}).map
    (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)

private def freeAbSheafHomEquiv (U : Opens X) (I : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (freeAbSheaf U ⟶ I) ≃ (forget AddCommGrpCat).obj (I.val.obj (op U)) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology (T := X)) AddCommGrpCat.{u}).homEquiv
    (freeAbPresheaf U) I).trans <|
  ((AddCommGrpCat.adj.whiskerRight _).homEquiv (yoneda.obj U)
    (sheafToPresheaf _ _ |>.obj I)).trans <|
  yonedaEquiv

private lemma freeAbSheafHomEquiv_naturality {U V : Opens X} (i : U ⟶ V)
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) (f : freeAbSheaf V ⟶ I) :
    freeAbSheafHomEquiv U I (freeAbSheafMap i ≫ f) =
      (I.val.map i.op) (freeAbSheafHomEquiv V I f) := by
  simp [freeAbSheafHomEquiv, freeAbSheafMap]
  erw [Adjunction.homEquiv_naturality_left]
  erw [Adjunction.homEquiv_naturality_left]
  simp +decide [yonedaEquiv]
  convert (NatTrans.naturality
    ((Adjunction.whiskerRight (Opens X)ᵒᵖ AddCommGrpCat.adj).homEquiv
      (yoneda.obj V) I.val
      ((sheafificationAdjunction (Opens.grothendieckTopology X)
        AddCommGrpCat).homEquiv (freeAbPresheaf V) I f))
    i.op) using 1
  constructor <;> intro h
  · exact (NatTrans.naturality
      ((Adjunction.whiskerRight (Opens X)ᵒᵖ AddCommGrpCat.adj).homEquiv
        (yoneda.obj V) I.val
        ((sheafificationAdjunction (Opens.grothendieckTopology X)
          AddCommGrpCat).homEquiv (freeAbPresheaf V) I f)) i.op)
  · convert congr_arg (fun g => g (𝟙 V)) h using 1

set_option synthInstance.maxHeartbeats 40000 in
private instance freeAbSheafMap_mono {U V : Opens X} (i : U ⟶ V) :
    Mono (freeAbSheafMap i) := by
  have : ∀ (F G : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (f : F ⟶ G),
      Mono f → Mono ((presheafToSheaf (Opens.grothendieckTopology (T := X))
        AddCommGrpCat).map f) :=
    fun _ _ f _ => Functor.map_mono _ f
  exact this _ _ _ (instMonoFunctorWhiskerRightOfPreservesMonomorphisms
    (yoneda.map i) AddCommGrpCat.free)

end FreeAbSheaf

-- Injective sheaves are flasque (proved by Aristotle 8f42abaa).
-- Uses free abelian sheaf + Yoneda identification + Injective.factors.
theorem isFlasque_of_injective {X : TopCat.{u}}
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] : IsFlasqueSheaf I := by
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  set g := (freeAbSheafHomEquiv U I).symm s
  obtain ⟨h, hh⟩ : ∃ h : freeAbSheaf V ⟶ I, freeAbSheafMap i ≫ h = g :=
    Injective.factors g (freeAbSheafMap i)
  refine ⟨freeAbSheafHomEquiv V I h, ?_⟩
  rw [← freeAbSheafHomEquiv_naturality i I h, hh]
  simp [g]

private lemma epi_of_natIso_epi {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ≅ G) {X Y : C} (f : X ⟶ Y)
    (h : Epi (F.map f)) : Epi (G.map f) := by
  have : G.map f = α.inv.app X ≫ F.map f ≫ α.hom.app Y := by
    conv_lhs => rw [← Category.id_comp (G.map f), ← Iso.inv_hom_id_app α X]
    rw [Category.assoc, ← α.hom.naturality f, ← Category.assoc]
  rw [this]; exact epi_comp _ _

-- Surjectivity of Ext map at degree 0 (base case input).
-- For a SES 0 -> F -> I -> Q -> 0 with F flasque, the induced map
-- Ext(Z_X, I, 0) -> Ext(Z_X, Q, 0) is surjective for Z_X = constant sheaf.
-- Proof: reduce to Hom via addEquiv₀, then use constantSheafΓAdj + projectivity
-- of ULift ℤ + epi_app_of_shortExact_flasque.
set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 40000 in
theorem ext_zero_map_surjective {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (hFlasque₁ : IsFlasqueSheaf S.X₁) :
    ∀ y : Ext ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) S.X₃ 0,
      ∃ z : Ext ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) S.X₂ 0,
        z.comp (Ext.mk₀ S.g) (add_zero 0) = y := by
  intro y
  -- Convert from Ext⁰ to Hom via addEquiv₀
  suffices ∃ ψ : _ ⟶ S.X₂, ψ ≫ S.g = Ext.addEquiv₀ y by
    obtain ⟨ψ, hψ⟩ := this
    exact ⟨Ext.mk₀ ψ, by rw [Ext.mk₀_comp_mk₀, hψ, Ext.mk₀_addEquiv₀_apply]⟩
  -- Γ(g) is epi (from g epi at ⊤, via Γ ≅ sheafSections at ⊤)
  have hΓg : Epi ((Sheaf.Γ (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).map S.g) :=
    epi_of_natIso_epi (Sheaf.ΓNatIsoSheafSections _ _ Limits.isTerminalTop).symm S.g
      (epi_app_of_shortExact_flasque hS hFlasque₁ ⊤)
  -- Lift through adjunction + projectivity of ULift ℤ
  let adj := constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let M := AddCommGrpCat.of (ULift.{u} ℤ)
  haveI : Projective M := ulift_int_projective
  refine ⟨(adj.homEquiv M S.X₂).symm (Projective.factorThru
    ((adj.homEquiv M S.X₃) (Ext.addEquiv₀ y))
    ((Sheaf.Γ _ _).map S.g)), ?_⟩
  apply (adj.homEquiv M S.X₃).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Projective.factorThru_comp]

/-! ## Proved infrastructure -/

/-- **Dimension shifting** via injective presentation.
    For `0 -> F -> I -> Q -> 0` with `I` injective, `Subsingleton (H Q n)`
    implies `Subsingleton (H F (n+1))`. Uses the covariant Ext LES:
    `Ext(Z, Q, n) -> Ext(Z, F, n+1) -> Ext(Z, I, n+1) = 0`
    so every element of `Ext(Z, F, n+1)` lifts to `Ext(Z, Q, n)`. -/
private theorem sheafH_dimension_shift {X : TopCat.{u}}
    {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (ip : InjectivePresentation F) (n : ℕ)
    (hQ : Subsingleton (Sheaf.H ip.shortComplex.X₃ n)) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  have hSE := ip.shortExact_shortComplex
  constructor; intro a b
  -- Since I is injective, a and b map to 0 in Ext(Z, I, n+1)
  have ha : a.comp (Ext.mk₀ ip.shortComplex.f) rfl = 0 := Ext.eq_zero_of_injective _
  have hb : b.comp (Ext.mk₀ ip.shortComplex.f) rfl = 0 := Ext.eq_zero_of_injective _
  -- By the LES, they lift to Ext(Z, Q, n) which is subsingleton
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hSE a ha rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hSE b hb rfl
  rw [← hc, ← hd]; congr 1; exact @Subsingleton.elim _ hQ c d

/-- **Base case**: `H^1(F) = 0` for flasque `F`.
    Uses `ext_zero_map_surjective` to show the connecting map
    `Ext(Z, Q, 0) -> Ext(Z, F, 1)` is zero (by associativity of Ext composition
    and `ShortExact.comp_extClass`), then exactness forces `Ext(Z, F, 1) = 0`. -/
private theorem sheafH_one_of_flasque {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (h : IsFlasqueSheaf F) :
    Subsingleton (Sheaf.H F 1) := by
  obtain ⟨ip⟩ := EnoughInjectives.presentation F
  have hSE := ip.shortExact_shortComplex
  have h_surj := ext_zero_map_surjective hSE h
  constructor; intro a b
  -- Since I is injective, a and b map to 0 in Ext(Z, I, 1)
  have ha : a.comp (Ext.mk₀ ip.shortComplex.f) rfl = 0 := Ext.eq_zero_of_injective _
  have hb : b.comp (Ext.mk₀ ip.shortComplex.f) rfl = 0 := Ext.eq_zero_of_injective _
  -- By the LES, they lift to Ext(Z, Q, 0)
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hSE a ha rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hSE b hb rfl
  -- By surjectivity, c and d lift further to Ext(Z, I, 0)
  obtain ⟨c', hc'⟩ := h_surj c
  obtain ⟨d', hd'⟩ := h_surj d
  -- The connecting map kills images of the restriction map (LES zero condition):
  -- comp(mk₀ g, extClass) = 0, so by associativity, (_.comp mk₀ g).comp extClass = 0
  have zero_c : c.comp hSE.extClass rfl = 0 := by
    rw [← hc', Ext.comp_assoc_of_second_deg_zero c' (Ext.mk₀ ip.shortComplex.g)
      hSE.extClass rfl, hSE.comp_extClass, Ext.comp_zero c' _ 1 1 rfl]
  have zero_d : d.comp hSE.extClass rfl = 0 := by
    rw [← hd', Ext.comp_assoc_of_second_deg_zero d' (Ext.mk₀ ip.shortComplex.g)
      hSE.extClass rfl, hSE.comp_extClass, Ext.comp_zero d' _ 1 1 rfl]
  rw [← hc, ← hd, zero_c, zero_d]

/-! ## Main theorems -/

set_option synthInstance.maxHeartbeats 80000 in
/-- **Flasque sheaves have vanishing higher cohomology** (Nugent, PR #35790).

    The proof is by induction on `n`:
    - Base: `H^1(F) = 0` by `sheafH_one_of_flasque` (Ext LES + Zorn surjectivity).
    - Step: embed `F` into injective `I`, form `0 -> F -> I -> Q -> 0`.
      Since `I` is injective hence flasque, and `F` is flasque, `Q` is also flasque
      by `isFlasque_X₃_of_shortExact`. By dimension shifting, `H^{n+2}(F) = H^{n+1}(Q)`,
      and the latter vanishes by the induction hypothesis. -/
theorem FlasqueVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (h : ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op))
    (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  induction n generalizing F with
  | zero => exact sheafH_one_of_flasque F h
  | succ n ih =>
    obtain ⟨ip⟩ := EnoughInjectives.presentation F
    have hSE := ip.shortExact_shortComplex
    -- I is injective hence flasque; F and I flasque implies Q flasque
    have hI_flasque : IsFlasqueSheaf ip.shortComplex.X₂ := isFlasque_of_injective _
    have hQ_flasque : IsFlasqueSheaf ip.shortComplex.X₃ :=
      isFlasque_X₃_of_shortExact hSE h hI_flasque
    -- By dimension shifting: H^{n+2}(F) = 0 because H^{n+1}(Q) = 0 by IH
    exact sheafH_dimension_shift ip (n + 1) (ih ip.shortComplex.X₃ hQ_flasque)

/-! ## Building blocks for the closed-open decomposition

ReducibleVanishing and IrreduciblePosVanishing require two building blocks:

1. PushforwardHVanishing: pushforward along closed immersion preserves vanishing
   (adjunction + mono preservation + exactness of i_*)
2. ClosedImmersionSES: the adjunction unit F -> i_*(i^*F) gives a short exact sequence
-/

-- Pushforward preserves flasqueness for any continuous map.
theorem pushforward_preserves_flasque {Y : TopCat.{u}} (f : TopCat.of Y ⟶ X)
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Y)) (hG : IsFlasqueSheaf G) :
    IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj G) :=
  fun i => by change Epi (G.val.map ((Opens.map f).op.map i.op)); exact hG _

-- Pushforward along a closed immersion preserves cohomological vanishing.
-- KEY: Γ_X(i_*G) = G(⊤_Z) by rfl, and i_* preserves flasqueness.
-- The proof uses FlasqueVanishing + LES + Γ equality + induction on n.
-- Requires: i_* is exact for closed immersions (sorry'd sub-lemma).
set_option synthInstance.maxHeartbeats 80000 in
theorem PushforwardHVanishing
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    [NoetherianSpace X]
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)) (n : ℕ)
    (h : Subsingleton (Sheaf.H G n)) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) n) := by
  sorry

-- The adjunction unit F → i_*(i^*F) is epi for closed immersions.
-- Proof: stalkwise surjective (identity on Z, maps to 0 outside Z).
-- Requires: stalkPushforward_iso_of_isInducing + stalk of i_*G = 0 outside Z.
-- epi via surjective on stalks
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 80000 in
theorem epi_unit_of_closedImmersion
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    [NoetherianSpace X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i
    Epi (adj.unit.app F) := by
  intro i adj
  rw [← (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} (adj.unit.app F))]
  rw [show Sheaf.IsLocallySurjective (adj.unit.app F) =
    TopCat.Presheaf.IsLocallySurjective (adj.unit.app F).val from rfl]
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x
  by_cases hxZ : (x : X) ∈ Z
  · -- x ∈ Z: stalk map is surjective (it's an iso via stalkPushforward_iso_of_isInducing)
    sorry
  · -- x ∉ Z: target stalk is 0 (pushforward has zero stalk outside closed Z)
    sorry

-- Short exact sequence from closed immersion.
-- Uses epi_unit_of_closedImmersion to form 0 → ker(η) → F → i_*(i^*F) → 0.
set_option synthInstance.maxHeartbeats 80000 in
theorem ClosedImmersionSES
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    [NoetherianSpace X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    let Y := TopCat.of Z
    let i : Y ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    ∃ (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)),
      S.ShortExact ∧ S.X₂ = F ∧
      S.X₃ = (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj F) := by
  intro Y i
  have hE := epi_unit_of_closedImmersion Z hZ F
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i
  let η := adj.unit.app F
  haveI : Epi η := hE
  exact ⟨ShortComplex.mk (kernel.ι η) η (kernel.condition η),
    ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel η))
      inferInstance inferInstance,
    rfl, rfl⟩

/-! ## Main vanishing theorems -/

set_option synthInstance.maxHeartbeats 80000 in
/-- **Reducible vanishing** (Stacks Project Tag 01X8, Step 1).
    For a non-irreducible Noetherian space `X`, cohomology vanishing above the dimension
    follows from vanishing on all irreducible spaces of dim ≤ dim X.

    **Proof**: Iterate `ClosedImmersionSES` over the irreducible components `Z₁, …, Zₖ`
    (k ≥ 2 since X is reducible). At each step, the pushforward term
    `i_*(i^*K)` vanishes by `PushforwardHVanishing` + `ih_irred`. By
    `subsingleton_ext_of_ses_middle`, vanishing of F reduces to vanishing of K.
    After all k components are peeled, the kernel has zero stalks on
    `Z₁ ∪ ⋯ ∪ Zₖ = X`, hence is the zero sheaf. -/
theorem ReducibleVanishing
    (X : TopCat.{u}) [NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hNotIrred : ¬ IrreducibleSpace X) [Nonempty X]
    (ih_irred : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      [IrreducibleSpace Y] (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      n > topologicalKrullDim Y → Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) := by
  sorry

set_option synthInstance.maxHeartbeats 80000 in
/-- **Irreducible positive-dimension vanishing** (Stacks Project Tag 01X8, Step 2).
    For an irreducible Noetherian space `X` of dim ≥ 1, cohomology vanishing above
    the dimension follows from vanishing on all spaces of strictly smaller dimension.

    **Proof**: Fix `n > dim X = d ≥ 1`. Take a proper closed `Z₁ ⊊ X` (exists since
    `d ≥ 1`). By `ClosedImmersionSES`: `0 → K₁ → F → i_*(i^*F) → 0`. Since `X` is
    irreducible, `dim Z₁ < d`, so `PushforwardHVanishing` + `ih` give vanishing of
    the pushforward term. By `subsingleton_ext_of_ses_middle`:
    `Subsingleton(Ext^n(K₁)) → Subsingleton(Ext^n(F))`.

    Now iterate: take `Z₂ ⊋ Z₁` (proper closed), apply the SES to `K₁`, getting `K₂`
    with zero stalks on `Z₂ ⊇ Z₁`. The ascending chain `Z₁ ⊊ Z₂ ⊊ ⋯` must stabilize
    at `X` by the Noetherian condition (at each step we add a new point's closure, and
    the chain terminates only when it reaches `X`).
    At termination: `K_m = 0`, so `Ext^n(K_m) = 0`, and backtracking gives `Ext^n(F) = 0`. -/
theorem IrreduciblePosVanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X) (hpos : topologicalKrullDim X > 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      n > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) := by
  sorry
