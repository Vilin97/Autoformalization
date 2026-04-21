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

-- For a SES of sheafified presheaves, the evaluated sequence at V is exact:
-- if g_V(x) = 0, then x is in the image of f_V.
lemma sections_exact_of_shortExact_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃}
    (hfg : (let F₁sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₁, h₁⟩
      let F₂sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₂, h₂⟩
      let F₃sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₃, h₃⟩
      let fsh : F₁sh ⟶ F₂sh := Sheaf.Hom.mk f
      let gsh : F₂sh ⟶ F₃sh := Sheaf.Hom.mk g
      fsh ≫ gsh = 0))
    (hS : (let F₁sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₁, h₁⟩
      let F₂sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₂, h₂⟩
      let F₃sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₃, h₃⟩
      let fsh : F₁sh ⟶ F₂sh := Sheaf.Hom.mk f
      let gsh : F₂sh ⟶ F₃sh := Sheaf.Hom.mk g
      let Ssh : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk fsh gsh hfg
      Ssh.ShortExact))
    (V : Opens X) (x : F₂.obj (op V))
    (hx : ConcreteCategory.hom (g.app (op V)) x = 0) :
    ∃ a : F₁.obj (op V),
      ConcreteCategory.hom (f.app (op V)) a = x := by
  let F₁sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₁, h₁⟩
  let F₂sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₂, h₂⟩
  let F₃sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₃, h₃⟩
  let fsh : F₁sh ⟶ F₂sh := Sheaf.Hom.mk f
  let gsh : F₂sh ⟶ F₃sh := Sheaf.Hom.mk g
  let Ssh : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk fsh gsh hfg
  have hSsh : Ssh.ShortExact := by
    simpa [F₁sh, F₂sh, F₃sh, fsh, gsh, Ssh] using hS
  let sectV := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op V)
  haveI : sectV.PreservesZeroMorphisms :=
    inferInstanceAs ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op V)).PreservesZeroMorphisms)
  haveI : PreservesLimit (parallelPair Ssh.g 0) sectV :=
    show PreservesLimit _ (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op V)) from inferInstance
  have hexact : (Ssh.map sectV).Exact :=
    hSsh.exact.map_of_mono_of_preservesKernel sectV hSsh.mono_f inferInstance
  simpa [F₁sh, F₂sh, F₃sh, fsh, gsh, Ssh] using
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
    (f := S.f.val) (g := S.g.val) S.zero
    (hS := by
      simpa using hS)
    V x hx

/-! ### Zero condition and mono for the evaluated short complex -/

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
      simp only [show (homOfLE (le_trans h₁ h₂)).op = (homOfLE h₂).op ≫ (homOfLE h₁).op from rfl,
        Functor.map_comp, AddCommGrpCat.hom_comp,
        AddMonoidHom.coe_comp, Function.comp_apply, ht₂, ht₁]⟩

/-! ### Partial lift sub-lemmas for the Zorn surjectivity argument -/

/-- A partial lift: `(V, t)` with `V ≤ U` and `g(t) = s|_V`. -/
private def IsPartialLift {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (U : Opens X) (s : S.X₃.val.obj (op U))
    (p : Σ V : Opens X, S.X₂.val.obj (op V)) : Prop :=
  ∃ h : p.1 ≤ U, ConcreteCategory.hom (S.g.val.app (op p.1)) p.2 =
    ConcreteCategory.hom (S.X₃.val.map (homOfLE h).op) s

-- Chain of partial lifts has an upper bound via sheaf gluing.
private lemma partialLift_chain_ub {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    {U : Opens X} {s : S.X₃.val.obj (op U)}
    {c : Set (Σ V : Opens X, S.X₂.val.obj (op V))}
    (hcP : ∀ p ∈ c, IsPartialLift (S := S) U s p)
    (hchain : @IsChain _ (sigmaPreorder S).le c) :
    ∃ ub ∈ {p | IsPartialLift (S := S) U s p},
      ∀ p ∈ c, (sigmaPreorder S).le p ub := by
  by_cases hc : c.Nonempty
  · let cV (p : c) := (p : Σ V : Opens X, S.X₂.val.obj (op V)).1
    let cs (p : c) := (p : Σ V : Opens X, S.X₂.val.obj (op V)).2
    set Vsup := ⨆ p, cV p
    have hVsup_le : Vsup ≤ U := iSup_le fun ⟨_, hp⟩ => (hcP _ hp).choose
    have hcompat : TopCat.Presheaf.IsCompatible S.X₂.val cV cs := by
      intro ⟨p, hp⟩ ⟨q, hq⟩
      rcases hchain.total hp hq with ⟨h, e⟩ | ⟨h, e⟩
      · rw [show (p.1).infLERight q.1 = (p.1).infLELeft q.1 ≫ homOfLE h from rfl,
          op_comp, Functor.map_comp, CategoryTheory.comp_apply, e]
      · rw [show (p.1).infLELeft q.1 = (p.1).infLERight q.1 ≫ homOfLE h from rfl,
          op_comp, Functor.map_comp, CategoryTheory.comp_apply, e]
    obtain ⟨t_gl, ht_gl, _⟩ := TopCat.Sheaf.existsUnique_gluing' S.X₂ cV Vsup
        (fun p => homOfLE (le_iSup cV p)) le_rfl cs hcompat
    refine ⟨⟨Vsup, t_gl⟩, ⟨hVsup_le, ?_⟩, fun ⟨p, hp⟩ hpP =>
      ⟨le_iSup cV ⟨⟨p, hp⟩, hpP⟩, ht_gl ⟨⟨p, hp⟩, hpP⟩⟩⟩
    apply TopCat.Sheaf.eq_of_locally_eq' S.X₃ cV Vsup
      (fun p => homOfLE (le_iSup cV p)) le_rfl
    intro ⟨p, hp⟩
    rw [← S.g.val.naturality_apply _ t_gl, ht_gl ⟨p, hp⟩, (hcP _ hp).choose_spec]
    simp only [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact congr_arg (S.X₃.val.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim _ _))
  · exact ⟨⟨⊥, 0⟩, ⟨bot_le, @Subsingleton.elim _
      (AddCommGrpCat.subsingleton_of_isZero S.X₃.isTerminalOfEmpty.isZero) _ _⟩,
      fun _ hz => absurd ⟨_, hz⟩ hc⟩

-- Maximal partial lift must cover all of U.
-- If V₀ < U, find x ∈ U \ V₀, get a local lift on W ∋ x, adjust for compatibility
-- using exactness + flasqueness, glue to get a strictly larger partial lift.
private lemma partialLift_maximal_eq_U {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (hX₁_epi : ∀ {U V : Opens X} (i : U ⟶ V), Epi (S.X₁.val.map i.op))
    {U : Opens X} {s : S.X₃.val.obj (op U)}
    {V₀ : Opens X} {t₀ : S.X₂.val.obj (op V₀)}
    (hV₀U : V₀ ≤ U)
    (ht₀ : ConcreteCategory.hom (S.g.val.app (op V₀)) t₀ =
      ConcreteCategory.hom (S.X₃.val.map (homOfLE hV₀U).op) s)
    (hls : Sheaf.IsLocallySurjective S.g)
    (hmax : ∀ (p : Σ V : Opens X, S.X₂.val.obj (op V)),
      IsPartialLift (S := S) U s p →
      (sigmaPreorder S).le ⟨V₀, t₀⟩ p →
      (sigmaPreorder S).le p ⟨V₀, t₀⟩) :
    V₀ = U := by
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
    exact congr_arg (S.X₃.val.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim _ _))
  obtain ⟨a, ha⟩ := sections_exact_of_shortExact hS (V₀ ⊓ W) _ hdiff_ker
  obtain ⟨ahat, hahat⟩ := (AddCommGrpCat.epi_iff_surjective _).mp
    (hX₁_epi (homOfLE inf_le_right : V₀ ⊓ W ⟶ W)) a
  set t'' := t' + S.f.val.app (op W) ahat with ht''_def
  have hgt'' : S.g.val.app (op W) t'' = S.X₃.val.map (homOfLE hWU).op s := by
    simp only [ht''_def, map_add, show S.g.val.app (op W) (S.f.val.app (op W) ahat) = 0 from by
      show (S.f.val.app (op W) ≫ S.g.val.app (op W)) ahat = 0
      change (S.f ≫ S.g).val.app (op W) ahat = 0; rw [S.zero]; aesop_cat,
      add_zero, ht']; exact congr_arg (S.X₃.val.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim _ _))
  have hcompat_patch : S.X₂.val.map (homOfLE inf_le_right).op t'' =
      S.X₂.val.map (homOfLE inf_le_left).op t₀ := by
    simp only [ht''_def, map_add]
    rw [show S.X₂.val.map (homOfLE inf_le_right).op (S.f.val.app (op W) ahat) =
      S.f.val.app (op (V₀ ⊓ W)) (S.X₁.val.map (homOfLE inf_le_right).op ahat) from
      (S.f.val.naturality_apply (homOfLE inf_le_right).op ahat).symm, hahat, ha]; abel
  -- Binary glue t₀ and t'' to get t_new on V₀ ⊔ W
  let BU : Bool → Opens X | false => V₀ | true => W
  let Bsf : (b : Bool) → S.X₂.val.obj (op (BU b)) | false => t₀ | true => t''
  have hsup_eq : ⨆ b, BU b = V₀ ⊔ W := le_antisymm
    (iSup_le fun b => by cases b <;> simp [BU])
    (by intro y hy; simp only [Opens.mem_iSup]; rcases hy with h | h;
        exact ⟨false, h⟩; exact ⟨true, h⟩)
  have hcompat_glue : TopCat.Presheaf.IsCompatible S.X₂.val BU Bsf := by
    intro i j; match i, j with
    | false, false | true, true => rfl
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
  obtain ⟨t_new, ht_new, _⟩ := TopCat.Sheaf.existsUnique_gluing' S.X₂ BU (V₀ ⊔ W)
    (fun b => homOfLE (by cases b <;> simp [BU])) (hsup_eq ▸ le_rfl) Bsf hcompat_glue
  have h_new_inP : IsPartialLift (S := S) U s ⟨V₀ ⊔ W, t_new⟩ := by
    refine ⟨sup_le hV₀U hWU, ?_⟩
    apply TopCat.Sheaf.eq_of_locally_eq' S.X₃ BU (V₀ ⊔ W)
      (fun b => homOfLE (by cases b <;> simp [BU])) (hsup_eq ▸ le_rfl)
    intro b; rw [← S.g.val.naturality_apply _ t_new]
    have hb := ht_new b; cases b <;>
      (simp only [BU, Bsf] at hb ⊢; rw [hb]; first | rw [ht₀] | rw [hgt'']
       simp only [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
       exact congr_arg (S.X₃.val.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim _ _)))
  exact hxV₀ ((hmax _ h_new_inP ⟨le_sup_left, by
    have h0 := ht_new false; simp only [BU, Bsf] at h0; exact h0⟩).1 (Or.inr hxW))

/-- If `0 → X₁ → X₂ → X₃ → 0` is short exact and every restriction map of the
underlying presheaf `S.X₁.val` is epi, then `g(U) : X₂(U) → X₃(U)` is epi. -/
theorem epi_app_of_shortExact_of_epi_restrictions_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃}
    (hfg : (let F₁sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₁, h₁⟩
      let F₂sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₂, h₂⟩
      let F₃sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₃, h₃⟩
      let fsh : F₁sh ⟶ F₂sh := Sheaf.Hom.mk f
      let gsh : F₂sh ⟶ F₃sh := Sheaf.Hom.mk g
      fsh ≫ gsh = 0))
    (hS : (let F₁sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₁, h₁⟩
      let F₂sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₂, h₂⟩
      let F₃sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₃, h₃⟩
      let fsh : F₁sh ⟶ F₂sh := Sheaf.Hom.mk f
      let gsh : F₂sh ⟶ F₃sh := Sheaf.Hom.mk g
      let Ssh : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk fsh gsh hfg
      Ssh.ShortExact))
    (hX₁_epi : ∀ {U V : Opens X} (i : U ⟶ V), Epi (F₁.map i.op))
    (U : Opens X) :
    Epi (g.app (op U)) := by
  let F₁sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₁, h₁⟩
  let F₂sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₂, h₂⟩
  let F₃sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₃, h₃⟩
  let fsh : F₁sh ⟶ F₂sh := Sheaf.Hom.mk f
  let gsh : F₂sh ⟶ F₃sh := Sheaf.Hom.mk g
  let Ssh : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk fsh gsh hfg
  have hSsh : Ssh.ShortExact := by
    simpa [F₁sh, F₂sh, F₃sh, fsh, gsh, Ssh] using hS
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  haveI : Epi Ssh.g := hSsh.epi_g
  have hls : Sheaf.IsLocallySurjective Ssh.g :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} Ssh.g).mpr inferInstance
  obtain ⟨⟨V₀, t₀⟩, ⟨hV₀U, ht₀⟩, hmax⟩ :=
    @zorn_le₀ _ (sigmaPreorder Ssh) {p | IsPartialLift (S := Ssh) U s p}
      (fun c hcP hchain =>
        partialLift_chain_ub (S := Ssh) (U := U) (s := s) (fun p hp => hcP hp) hchain)
  have := partialLift_maximal_eq_U (S := Ssh) hSsh hX₁_epi hV₀U ht₀ hls hmax
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
    (f := S.f.val) (g := S.g.val) S.zero
    (hS := by
      simpa using hS)
    hX₁_epi U

-- Zorn argument for surjectivity of sections (Nugent, PR #35790).
theorem epi_app_of_shortExact_flasque {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) [IsFlasqueSheaf S.X₁] (U : Opens X) :
    Epi (S.g.val.app (op U)) :=
  epi_app_of_shortExact_of_epi_restrictions hS (fun {_ _} i => IsFlasqueSheaf.epi_map i) U

/-- **Quotient preserves flasqueness** (Nugent, PR #35790).
    If `F'` and `G` are flasque in `0 -> F' -> G -> H -> 0`, then `H` is flasque.
    Follows from `epi_app_of_shortExact_flasque`: the restriction map for `H` factors
    through the epi `G(U) -> H(U)` composed with the restriction of `G`. -/
theorem isFlasque_X₃_of_shortExact {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) [IsFlasqueSheaf S.X₁] [IsFlasqueSheaf S.X₂] :
    IsFlasqueSheaf S.X₃ := by
  constructor; intro U V j
  have hg_U : Epi (S.g.val.app (op U)) := epi_app_of_shortExact_flasque hS U
  have hres₂ : Epi (S.X₂.val.map j.op) := IsFlasqueSheaf.epi_map j
  rw [AddCommGrpCat.epi_iff_surjective] at hg_U hres₂ ⊢
  intro z; obtain ⟨w, hw⟩ := hg_U z
  obtain ⟨x, hx⟩ := hres₂ w
  exact ⟨ConcreteCategory.hom (S.g.val.app (op V)) x, by
    have := congrArg (· x) (S.g.val.naturality j.op)
    simp only [AddCommGrpCat.hom_comp] at this
    exact this.symm.trans (by simp [hx, hw])⟩

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
