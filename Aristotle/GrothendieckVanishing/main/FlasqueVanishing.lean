import Mathlib
import Aristotle.GrothendieckVanishing.main.TopologicalKrullDim
import Aristotle.GrothendieckVanishing.main.ClosedImmersion
import Aristotle.GrothendieckVanishing.main.ZeroOutside

/-!
  FlasqueVanishing.lean -- Flasque sheaf theory and infrastructure

  Provides:
  1. Categorical infrastructure for sheaf cohomology on `AddCommGrpCat`
  2. `IsFlasqueSheaf`, `epi_app_of_shortExact_flasque`, `isFlasque_X₃_of_shortExact`
  3. `isFlasque_of_injective` (injective sheaves are flasque)

  General stalk/zero-sheaf lemmas (`sheaf_isZero_of_zero_stalks`, `stalk_zero_of_ses_g_iso`,
  `stalk_zero_of_shortExact_kernel`) are in `CohomologyAPI.lean`.

  `FlasqueVanishing` itself is in `FlasqueCohomology.lean`.
  Split from SetupCore.lean for compilation performance.
-/

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

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

instance {C : Type*} [Category C] {D : Type*} [Category D] [Preadditive D] :
    (Functor.const Cᵒᵖ : D ⥤ Cᵒᵖ ⥤ D).Additive where

instance {C : Type*} [Category C] [Preadditive C] {X : TopCat.{u}} :
    Preadditive (TopCat.Presheaf C X) := by
  delta TopCat.Presheaf
  infer_instance

instance {X : TopCat.{u}} :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive :=
  inferInstanceAs ((Functor.const (Opens X)ᵒᵖ ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive)

/-! ## Projective ULift ℤ in AddCommGrpCat -/

/-- `ULift ℤ` is projective in `AddCommGrpCat` (via the equivalence with `ModuleCat ℤ`). -/
noncomputable instance ulift_int_projective :
    Projective (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  set e := (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence with he
  have : e.inverse.PreservesEpimorphisms :=
    ⟨fun f _ => e.symm.functor.map_epi f⟩
  have hp := e.toAdjunction.map_projective _
    (inferInstance : Projective (ModuleCat.of ℤ (ULift.{u} ℤ)))
  simp only [he, Functor.asEquivalence, ModuleCat.forget₂_obj] at hp
  exact hp

noncomputable instance sheafHasExt (X : TopCat.{u}) :
    HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  hasExt_of_enoughInjectives _

/-! ## Flasque sheaf sub-lemmas

The four sub-lemmas below are adapted from Brian Nugent's Mathlib PR #35790.
Together they imply `FlasqueVanishing` (proved in FlasqueCohomology.lean). Each is a self-contained
statement that can be attacked independently.
-/

/-- A sheaf of abelian groups is **flasque** if all restriction maps are epi.
    This is equivalent to surjectivity of restriction on sections. -/
class IsFlasqueSheaf {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop where
  epi_map : ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op)

private def sheafShortComplexOfPresheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk
    (Sheaf.Hom.mk f : (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶ ⟨F₂, h₂⟩)
    (Sheaf.Hom.mk g : (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶ ⟨F₃, h₃⟩)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg)

@[simp] private lemma sheafShortComplexOfPresheaf_f_val {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    {h₁ : F₁.IsSheaf} {h₂ : F₂.IsSheaf} {h₃ : F₃.IsSheaf}
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} {hfg : f ≫ g = 0} :
    (sheafShortComplexOfPresheaf h₁ h₂ h₃ (f := f) (g := g) hfg).f.val = f := rfl

@[simp] private lemma sheafShortComplexOfPresheaf_g_val {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    {h₁ : F₁.IsSheaf} {h₂ : F₂.IsSheaf} {h₃ : F₃.IsSheaf}
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} {hfg : f ≫ g = 0} :
    (sheafShortComplexOfPresheaf h₁ h₂ h₃ (f := f) (g := g) hfg).g.val = g := rfl

private lemma shortComplex_val_zero {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} :
    S.f.val ≫ S.g.val = (0 : S.X₁.val ⟶ S.X₃.val) :=
  congrArg Sheaf.Hom.val S.zero

private lemma sheafShortComplexOfPresheaf_shortExact_of_shortExact {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) :
    (sheafShortComplexOfPresheaf S.X₁.cond S.X₂.cond S.X₃.cond
      (f := S.f.val) (g := S.g.val) (shortComplex_val_zero (S := S))).ShortExact := by
  simpa [sheafShortComplexOfPresheaf] using hS

-- For a SES of sheafified presheaves, the evaluated sequence at V is exact:
-- if g_V(x) = 0, then x is in the image of f_V.
lemma sections_exact_of_shortExact_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃}
    (hfg : f ≫ g = 0)
    (hS : (sheafShortComplexOfPresheaf h₁ h₂ h₃ (f := f) (g := g) hfg).ShortExact)
    (V : Opens X) (x : F₂.obj (op V))
    (hx : ConcreteCategory.hom (g.app (op V)) x = 0) :
    ∃ a : F₁.obj (op V),
      ConcreteCategory.hom (f.app (op V)) a = x := by
  let Ssh := sheafShortComplexOfPresheaf h₁ h₂ h₃ (f := f) (g := g) hfg
  have hSsh : Ssh.ShortExact := hS
  let sectV := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op V)
  haveI : sectV.PreservesZeroMorphisms :=
    inferInstanceAs ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op V)).PreservesZeroMorphisms)
  haveI : PreservesLimit (parallelPair Ssh.g 0) sectV :=
    show PreservesLimit _ (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op V)) from inferInstance
  have hexact : (Ssh.map sectV).Exact :=
    hSsh.exact.map_of_mono_of_preservesKernel sectV hSsh.mono_f inferInstance
  simpa [Ssh, sheafShortComplexOfPresheaf] using
    (ShortComplex.ab_exact_iff _).mp hexact x hx

-- For a SES of sheaves, the evaluated sequence at V is exact:
-- if g_V(x) = 0, then x is in the image of f_V.
lemma sections_exact_of_shortExact {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (V : Opens X)
    (x : S.X₂.val.obj (op V))
    (hx : ConcreteCategory.hom (S.g.val.app (op V)) x = 0) :
    ∃ a : S.X₁.val.obj (op V),
      ConcreteCategory.hom (S.f.val.app (op V)) a = x := by
  simpa using sections_exact_of_shortExact_presheaf
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val) (shortComplex_val_zero (S := S))
    (hS := sheafShortComplexOfPresheaf_shortExact_of_shortExact hS)
    V x hx

/-! ### Zero condition and mono for the evaluated short complex -/

-- Extension preorder on partial lifts (V, t):
-- (V₁,t₁) ≤ (V₂,t₂) iff V₁ ≤ V₂ and t₂|_{V₁} = t₁.
private noncomputable instance sigmaPreorder {X : TopCat.{u}}
    {F₂ : TopCat.Presheaf AddCommGrpCat.{u} X} :
    Preorder (Σ V : Opens X, F₂.obj (op V)) where
  le p q := ∃ h : p.1 ≤ q.1,
    ConcreteCategory.hom (F₂.map (homOfLE h).op) q.2 = p.2
  le_refl p := ⟨le_refl _, by simp⟩
  le_trans p q r := fun ⟨h₁, ht₁⟩ ⟨h₂, ht₂⟩ =>
    ⟨le_trans h₁ h₂, by
      simp only [show (homOfLE (le_trans h₁ h₂)).op = (homOfLE h₂).op ≫ (homOfLE h₁).op from rfl,
        Functor.map_comp, AddCommGrpCat.hom_comp,
        AddMonoidHom.coe_comp, Function.comp_apply, ht₂, ht₁]⟩

/-! ### Partial lift sub-lemmas for the Zorn surjectivity argument -/

/-- A partial lift: `(V, t)` with `V ≤ U` and `g(t) = s|_V`. -/
private def IsPartialLift {X : TopCat.{u}}
    {F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X} {g : F₂ ⟶ F₃}
    (U : Opens X) (s : F₃.obj (op U))
    (p : Σ V : Opens X, F₂.obj (op V)) : Prop :=
  ∃ h : p.1 ≤ U, ConcreteCategory.hom (g.app (op p.1)) p.2 =
    ConcreteCategory.hom (F₃.map (homOfLE h).op) s

-- Chain of partial lifts has an upper bound via sheaf gluing.
private lemma partialLift_chain_ub {X : TopCat.{u}}
    {F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {g : F₂ ⟶ F₃}
    {U : Opens X} {s : F₃.obj (op U)}
    {c : Set (Σ V : Opens X, F₂.obj (op V))}
    (hcP : ∀ p ∈ c, IsPartialLift (F₃ := F₃) (g := g) U s p)
    (hchain : @IsChain _ (sigmaPreorder (F₂ := F₂)).le c) :
    ∃ ub ∈ {p | IsPartialLift (F₃ := F₃) (g := g) U s p},
      ∀ p ∈ c, (sigmaPreorder (F₂ := F₂)).le p ub := by
  by_cases hc : c.Nonempty
  · let cV (p : c) := (p : Σ V : Opens X, F₂.obj (op V)).1
    let cs (p : c) := (p : Σ V : Opens X, F₂.obj (op V)).2
    set Vsup := ⨆ p, cV p
    have hVsup_le : Vsup ≤ U := iSup_le fun ⟨_, hp⟩ => (hcP _ hp).choose
    have hcompat : TopCat.Presheaf.IsCompatible F₂ cV cs := by
      intro ⟨p, hp⟩ ⟨q, hq⟩
      rcases hchain.total hp hq with ⟨h, e⟩ | ⟨h, e⟩
      · rw [show (p.1).infLERight q.1 = (p.1).infLELeft q.1 ≫ homOfLE h from rfl,
          op_comp, Functor.map_comp, CategoryTheory.comp_apply, e]
      · rw [show (p.1).infLELeft q.1 = (p.1).infLERight q.1 ≫ homOfLE h from rfl,
          op_comp, Functor.map_comp, CategoryTheory.comp_apply, e]
    obtain ⟨t_gl, ht_gl, _⟩ := h₂.isSheafUniqueGluing cV cs hcompat
    let gs (p : c) : F₃.obj (op (cV p)) :=
      ConcreteCategory.hom (F₃.map (homOfLE ((hcP p.1 p.2).choose)).op) s
    have hcompat_gs : TopCat.Presheaf.IsCompatible F₃ cV gs := by
      intro p q
      dsimp [gs]
      rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
        ← F₃.map_comp, ← F₃.map_comp]
      exact congr_arg (F₃.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim _ _))
    obtain ⟨_, _, hu_gl_uniq⟩ := h₃.isSheafUniqueGluing cV gs hcompat_gs
    refine ⟨⟨Vsup, t_gl⟩, ⟨hVsup_le, ?_⟩, fun ⟨p, hp⟩ hpP =>
      ⟨le_iSup cV ⟨⟨p, hp⟩, hpP⟩, ht_gl ⟨⟨p, hp⟩, hpP⟩⟩⟩
    have hg_gl : TopCat.Presheaf.IsGluing F₃ cV gs
        (ConcreteCategory.hom (g.app (op Vsup)) t_gl) := by
      intro p
      rw [← g.naturality_apply _ t_gl, ht_gl p]
      simpa [gs] using (hcP p.1 p.2).choose_spec
    have hs_gl : TopCat.Presheaf.IsGluing F₃ cV gs
        (ConcreteCategory.hom (F₃.map (homOfLE hVsup_le).op) s) := by
      intro p
      dsimp [gs]
      rw [← CategoryTheory.comp_apply, ← F₃.map_comp]
      exact congr_arg (F₃.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim _ _))
    exact (hu_gl_uniq _ hg_gl).trans (hu_gl_uniq _ hs_gl).symm
  · exact ⟨⟨⊥, 0⟩, ⟨bot_le, @Subsingleton.elim _
      (AddCommGrpCat.subsingleton_of_isZero
        ((TopCat.Sheaf.isTerminalOfEmpty
          (F := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))).isZero)) _ _⟩,
      fun _ hz => absurd ⟨_, hz⟩ hc⟩

-- Maximal partial lift must cover all of U.
-- If V₀ < U, find x ∈ U \ V₀, get a local lift on W ∋ x, adjust for compatibility
-- using exactness + flasqueness, glue to get a strictly larger partial lift.
private lemma partialLift_maximal_eq_U {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃}
    (hfg : f ≫ g = 0)
    (hS : (sheafShortComplexOfPresheaf h₁ h₂ h₃ (f := f) (g := g) hfg).ShortExact)
    (hX₁_epi : ∀ {U V : Opens X} (i : U ⟶ V), Epi (F₁.map i.op))
    {U : Opens X} {s : F₃.obj (op U)}
    {V₀ : Opens X} {t₀ : F₂.obj (op V₀)}
    (hV₀U : V₀ ≤ U)
    (ht₀ : ConcreteCategory.hom (g.app (op V₀)) t₀ =
      ConcreteCategory.hom (F₃.map (homOfLE hV₀U).op) s)
    (hls : TopCat.Presheaf.IsLocallySurjective g)
    (hmax : ∀ (p : Σ V : Opens X, F₂.obj (op V)),
      IsPartialLift (F₃ := F₃) (g := g) U s p →
      (sigmaPreorder (F₂ := F₂)).le ⟨V₀, t₀⟩ p →
      (sigmaPreorder (F₂ := F₂)).le p ⟨V₀, t₀⟩) :
    V₀ = U := by
  by_contra hne
  have hlt : V₀ < U := lt_of_le_of_ne hV₀U hne
  obtain ⟨x, hxU, hxV₀⟩ := Set.not_subset.mp hlt.2
  obtain ⟨W, iWU, ⟨t', ht'⟩, hxW⟩ := (hls.imageSieve_mem s) x hxU
  have hWU : W ≤ U := leOfHom iWU
  have hdiff_ker : g.app (op (V₀ ⊓ W))
      (F₂.map (homOfLE inf_le_left).op t₀ -
       F₂.map (homOfLE inf_le_right).op t') = 0 := by
    simp only [map_sub]
    rw [g.naturality_apply _ t₀, ht₀, g.naturality_apply _ t', ht', sub_eq_zero]
    simp only [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact congr_arg (F₃.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim _ _))
  obtain ⟨a, ha⟩ := sections_exact_of_shortExact_presheaf
    (F₁ := F₁) (F₂ := F₂) (F₃ := F₃) h₁ h₂ h₃ hfg hS (V₀ ⊓ W) _ hdiff_ker
  obtain ⟨ahat, hahat⟩ := (AddCommGrpCat.epi_iff_surjective _).mp
    (hX₁_epi (homOfLE inf_le_right : V₀ ⊓ W ⟶ W)) a
  have hfg_app : f.app (op W) ≫ g.app (op W) = 0 := by
    simpa using congrArg (fun α => α.app (op W)) hfg
  set t'' := t' + f.app (op W) ahat with ht''_def
  have hgt'' : g.app (op W) t'' = F₃.map (homOfLE hWU).op s := by
    simp only [ht''_def, map_add, show g.app (op W) (f.app (op W) ahat) = 0 from by
      show (f.app (op W) ≫ g.app (op W)) ahat = 0
      rw [hfg_app]; simp,
      add_zero, ht']; exact congr_arg (F₃.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim _ _))
  have hcompat_patch : F₂.map (homOfLE inf_le_right).op t'' =
      F₂.map (homOfLE inf_le_left).op t₀ := by
    simp only [ht''_def, map_add]
    rw [show F₂.map (homOfLE inf_le_right).op (f.app (op W) ahat) =
      f.app (op (V₀ ⊓ W)) (F₁.map (homOfLE inf_le_right).op ahat) from
      (f.naturality_apply (homOfLE inf_le_right).op ahat).symm, hahat, ha]; abel
  -- Binary glue t₀ and t'' to get t_new on V₀ ⊔ W
  let BU : Bool → Opens X | false => V₀ | true => W
  let Bsf : (b : Bool) → F₂.obj (op (BU b)) | false => t₀ | true => t''
  have hsup_eq : ⨆ b, BU b = V₀ ⊔ W := le_antisymm
    (iSup_le fun b => by cases b <;> simp [BU])
    (by intro y hy; simp only [Opens.mem_iSup]; rcases hy with h | h;
        exact ⟨false, h⟩; exact ⟨true, h⟩)
  have hcompat_glue : TopCat.Presheaf.IsCompatible F₂ BU Bsf := by
    intro i j; match i, j with
    | false, false | true, true => rfl
    | false, true => exact hcompat_patch.symm
    | true, false =>
      show F₂.map (W.infLELeft V₀).op t'' = F₂.map (W.infLERight V₀).op t₀
      rw [show (W).infLELeft V₀ = eqToHom (inf_comm W V₀) ≫ homOfLE inf_le_right
            from Subsingleton.elim _ _,
          show (W).infLERight V₀ = eqToHom (inf_comm W V₀) ≫ homOfLE inf_le_left
            from Subsingleton.elim _ _,
        op_comp, Functor.map_comp, CategoryTheory.comp_apply,
          op_comp, Functor.map_comp, CategoryTheory.comp_apply,
          hcompat_patch]
  obtain ⟨t_gl, ht_gl, _⟩ := h₂.isSheafUniqueGluing BU Bsf hcompat_glue
  let t_new : F₂.obj (op (V₀ ⊔ W)) :=
    ConcreteCategory.hom (F₂.map (eqToHom hsup_eq.symm).op) t_gl
  have hBU_le : ∀ b, BU b ≤ V₀ ⊔ W := by
    intro b
    cases b <;> simp [BU]
  have ht_new : ∀ b,
      ConcreteCategory.hom (F₂.map (homOfLE (hBU_le b)).op) t_new = Bsf b := by
    intro b
    dsimp [t_new]
    rw [← ConcreteCategory.comp_apply, ← F₂.map_comp]
    have hle_b : homOfLE (hBU_le b) ≫ eqToHom hsup_eq.symm = Opens.leSupr BU b := by
      cases b <;> exact Subsingleton.elim _ _
    rw [show (eqToHom hsup_eq.symm).op ≫ (homOfLE (hBU_le b)).op = (Opens.leSupr BU b).op by
      simpa using congr_arg Quiver.Hom.op hle_b]
    exact ht_gl b
  have h_new_inP : IsPartialLift (F₃ := F₃) (g := g) U s ⟨V₀ ⊔ W, t_new⟩ := by
    refine ⟨sup_le hV₀U hWU, ?_⟩
    let Bs : (b : Bool) → F₃.obj (op (BU b))
      | false => ConcreteCategory.hom (F₃.map (homOfLE hV₀U).op) s
      | true => ConcreteCategory.hom (F₃.map (homOfLE hWU).op) s
    have hcompat_Bs : TopCat.Presheaf.IsCompatible F₃ BU Bs := by
      intro i j
      cases i <;> cases j <;> dsimp [Bs, BU]
      all_goals
        rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
          ← F₃.map_comp, ← F₃.map_comp]
        exact congr_arg (F₃.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim _ _))
    have hBUU : iSup BU ≤ U := by
      rw [hsup_eq]
      exact sup_le hV₀U hWU
    obtain ⟨_, _, hu_gl_uniq⟩ := h₃.isSheafUniqueGluing BU Bs hcompat_Bs
    have hg_gl : TopCat.Presheaf.IsGluing F₃ BU Bs
        (ConcreteCategory.hom (g.app (op (iSup BU))) t_gl) := by
      intro b
      rw [← g.naturality_apply _ t_gl, ht_gl b]
      cases b <;> simp only [BU, Bsf, Bs]
      · exact ht₀
      · exact hgt''
    have hs_gl : TopCat.Presheaf.IsGluing F₃ BU Bs
        (ConcreteCategory.hom (F₃.map (homOfLE hBUU).op) s) := by
      intro b
      cases b <;>
        (simp only [BU, Bs]
         rw [← CategoryTheory.comp_apply, ← F₃.map_comp]
         exact congr_arg (F₃.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim _ _)))
    have h_gl_eq :
        ConcreteCategory.hom (g.app (op (iSup BU))) t_gl =
          ConcreteCategory.hom (F₃.map (homOfLE hBUU).op) s := by
      exact (hu_gl_uniq _ hg_gl).trans (hu_gl_uniq _ hs_gl).symm
    have h_gl_eq' := congrArg
      (ConcreteCategory.hom (F₃.map (eqToHom hsup_eq.symm).op)) h_gl_eq
    have hnat :
        ConcreteCategory.hom (g.app (op (V₀ ⊔ W))) t_new =
          ConcreteCategory.hom (F₃.map (eqToHom hsup_eq.symm).op)
            (ConcreteCategory.hom (g.app (op (iSup BU))) t_gl) := by
      change ConcreteCategory.hom
          (F₂.map (eqToHom hsup_eq.symm).op ≫ g.app (op (V₀ ⊔ W))) t_gl =
        ConcreteCategory.hom
          (g.app (op (iSup BU)) ≫ F₃.map (eqToHom hsup_eq.symm).op) t_gl
      have hnat_fun :
          ConcreteCategory.hom (F₂.map (eqToHom hsup_eq.symm).op ≫ g.app (op (V₀ ⊔ W))) =
            ConcreteCategory.hom (g.app (op (iSup BU)) ≫ F₃.map (eqToHom hsup_eq.symm).op) := by
        simpa using g.naturality (eqToHom hsup_eq.symm).op
      have := congrArg (fun φ => φ t_gl) hnat_fun
      simpa using this
    have hcomp : eqToHom hsup_eq.symm ≫ homOfLE hBUU = homOfLE (sup_le hV₀U hWU) := by
      exact Subsingleton.elim _ _
    have h_rhs :
        ConcreteCategory.hom (F₃.map (eqToHom hsup_eq.symm).op)
            (ConcreteCategory.hom (F₃.map (homOfLE hBUU).op) s) =
          ConcreteCategory.hom (F₃.map (homOfLE (sup_le hV₀U hWU)).op) s := by
      rw [← ConcreteCategory.comp_apply, ← F₃.map_comp]
      exact congrArg (fun α => ConcreteCategory.hom (F₃.map α) s) <| by
        simpa using congr_arg Quiver.Hom.op hcomp
    exact hnat.trans (h_gl_eq'.trans h_rhs)
  exact hxV₀ ((hmax _ h_new_inP ⟨le_sup_left, by
    have h0 := ht_new false; simp only [BU, Bsf] at h0; exact h0⟩).1 (Or.inr hxW))

/-- If `0 → X₁ → X₂ → X₃ → 0` is short exact and every restriction map of the
underlying presheaf `S.X₁.val` is epi, then `g(U) : X₂(U) → X₃(U)` is epi. -/
theorem epi_app_of_shortExact_of_epi_restrictions_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃}
    (hfg : f ≫ g = 0)
    (hS : (sheafShortComplexOfPresheaf h₁ h₂ h₃ (f := f) (g := g) hfg).ShortExact)
    (hX₁_epi : ∀ {U V : Opens X} (i : U ⟶ V), Epi (F₁.map i.op))
    (U : Opens X) :
    Epi (g.app (op U)) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  let Ssh := sheafShortComplexOfPresheaf h₁ h₂ h₃ (f := f) (g := g) hfg
  have hSsh : Ssh.ShortExact := hS
  haveI : Epi Ssh.g := by
    simpa [Ssh] using hSsh.epi_g
  have hls : TopCat.Presheaf.IsLocallySurjective g := by
    simpa [Ssh] using
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} Ssh.g).mpr inferInstance
  obtain ⟨⟨V₀, t₀⟩, ⟨hV₀U, ht₀⟩, hmax⟩ :=
    @zorn_le₀ _ (sigmaPreorder (F₂ := F₂)) {p | IsPartialLift (F₃ := F₃) (g := g) U s p}
      (fun c hcP hchain =>
        partialLift_chain_ub (F₂ := F₂) (F₃ := F₃) h₂ h₃
          (U := U) (s := s) (fun p hp => hcP hp) hchain)
  have := partialLift_maximal_eq_U
    (F₁ := F₁) (F₂ := F₂) (F₃ := F₃) h₁ h₂ h₃ hfg hS hX₁_epi hV₀U ht₀ hls hmax
  subst this
  exact ⟨t₀, by rw [ht₀]; simp⟩

/-- If `0 → X₁ → X₂ → X₃ → 0` is short exact and every restriction map of the
underlying presheaf `S.X₁.val` is epi, then `g(U) : X₂(U) → X₃(U)` is epi. -/
theorem epi_app_of_shortExact_of_epi_restrictions {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (hX₁_epi : ∀ {U V : Opens X} (i : U ⟶ V), Epi (S.X₁.val.map i.op))
    (U : Opens X) :
    Epi (S.g.val.app (op U)) := by
  simpa using epi_app_of_shortExact_of_epi_restrictions_presheaf
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val) (shortComplex_val_zero (S := S))
    (hS := sheafShortComplexOfPresheaf_shortExact_of_shortExact hS)
    hX₁_epi U

-- Zorn argument for surjectivity of sections (Nugent, PR #35790).
theorem epi_app_of_shortExact_flasque {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) [IsFlasqueSheaf S.X₁] (U : Opens X) :
    Epi (S.g.val.app (op U)) :=
  epi_app_of_shortExact_of_epi_restrictions hS (fun {_ _} i => IsFlasqueSheaf.epi_map i) U

/-- Presheaf-boundary form of quotient-preserves-flasqueness:
    if `0 → F₁ → F₂ → F₃ → 0` is short exact on the associated sheaves and
    `⟨F₁, h₁⟩`, `⟨F₂, h₂⟩` are flasque, then `⟨F₃, h₃⟩` is flasque. -/
theorem isFlasque_X₃_of_shortExact_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃}
    (hfg : f ≫ g = 0)
    (hS : (sheafShortComplexOfPresheaf h₁ h₂ h₃ (f := f) (g := g) hfg).ShortExact)
    [IsFlasqueSheaf (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)]
    [IsFlasqueSheaf (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)] :
    IsFlasqueSheaf (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := by
  constructor
  intro U V j
  have hg_U : Epi (g.app (op U)) :=
    epi_app_of_shortExact_of_epi_restrictions_presheaf
      (F₁ := F₁) (F₂ := F₂) (F₃ := F₃) h₁ h₂ h₃ hfg hS
      (fun {_ _} i => by
        simpa using
          (IsFlasqueSheaf.epi_map
            (F := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) i)) U
  have hres₂ : Epi (F₂.map j.op) := by
    simpa using
      (IsFlasqueSheaf.epi_map
        (F := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) j)
  rw [AddCommGrpCat.epi_iff_surjective] at hg_U hres₂ ⊢
  intro z
  obtain ⟨w, hw⟩ := hg_U z
  obtain ⟨x, hx⟩ := hres₂ w
  exact ⟨ConcreteCategory.hom (g.app (op V)) x, by
    have := congrArg (· x) (g.naturality j.op)
    simp only [AddCommGrpCat.hom_comp] at this
    exact this.symm.trans (by simp [hx, hw])⟩

/-- **Quotient preserves flasqueness** (Nugent, PR #35790).
    If `F'` and `G` are flasque in `0 -> F' -> G -> H -> 0`, then `H` is flasque.
    Follows from `epi_app_of_shortExact_flasque`: the restriction map for `H` factors
    through the epi `G(U) -> H(U)` composed with the restriction of `G`. -/
theorem isFlasque_X₃_of_shortExact {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) [IsFlasqueSheaf S.X₁] [IsFlasqueSheaf S.X₂] :
    IsFlasqueSheaf S.X₃ := by
  letI : IsFlasqueSheaf (⟨S.X₁.val, S.X₁.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := by
    simpa using (inferInstance : IsFlasqueSheaf S.X₁)
  letI : IsFlasqueSheaf (⟨S.X₂.val, S.X₂.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := by
    simpa using (inferInstance : IsFlasqueSheaf S.X₂)
  simpa using isFlasque_X₃_of_shortExact_presheaf
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val) (shortComplex_val_zero (S := S))
    (hS := sheafShortComplexOfPresheaf_shortExact_of_shortExact hS)

-- Injective sheaves are flasque.
-- Uses zeroOutsideInt generator/sHom/openHom API + Injective.factors.
instance isFlasque_of_injective {X : TopCat.{u}}
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] : IsFlasqueSheaf I := by
  constructor; intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  obtain ⟨g, hg⟩ := Injective.factors
    (TopCat.Sheaf.zeroOutsideInt.sHom s) (TopCat.Sheaf.zeroOutsideInt.openHom (leOfHom i))
  refine ⟨g.val.app (op V) (TopCat.Sheaf.zeroOutsideInt.generator V), ?_⟩
  rw [show I.val.map i.op = I.val.map (homOfLE (leOfHom i)).op from
    congr_arg I.val.map (congr_arg Quiver.Hom.op (Subsingleton.elim _ _)),
    ← g.val.naturality_apply (homOfLE (leOfHom i)).op,
    ← TopCat.Sheaf.zeroOutsideInt.openHom_val_app_generator]
  change ((TopCat.Sheaf.zeroOutsideInt.openHom (leOfHom i) ≫ g).val.app (op U))
    (TopCat.Sheaf.zeroOutsideInt.generator U) = s
  rw [hg]; exact TopCat.Sheaf.zeroOutsideInt.sHom_app_generator s
