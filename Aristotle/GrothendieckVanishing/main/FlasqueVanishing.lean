import Aristotle.GrothendieckVanishing.main.CohomologyAPI
import Aristotle.GrothendieckVanishing.main.ZeroOutside

/-!
# FlasqueVanishing — Flasque sheaf theory and cohomological vanishing

This file collects the flasque-sheaf API used by the Grothendieck vanishing proof.

Main declarations:
* `IsFlasqueSheaf`
* `epi_app_of_shortExact_flasque`
* `isFlasque_X₃_of_shortExact`
* `isFlasque_of_injective`
* `sheafH_subsingleton_H1_of_flasque`
* `sheafH_subsingleton_of_flasque_presheaf`
* `FlasqueVanishing`

Generic `Sheaf.H` and `Ext` APIs live in `CohomologyAPI.lean`.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-! ## Flasque sheaf sub-lemmas

The four sub-lemmas below are adapted from Brian Nugent's Mathlib PR #35790.
Together they imply `FlasqueVanishing`. Each is a self-contained
statement that can be attacked independently.
-/

/-- A sheaf of abelian groups is **flasque** if all restriction maps are epi.
    This is equivalent to surjectivity of restriction on sections. -/
class IsFlasqueSheaf {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop where
  epi_map : ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op)

/-- Turn a short complex of sheaf-valued presheaves into a short complex of sheaves. -/
def sheafShortComplexOfPresheaf {X : TopCat.{u}}
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

/-- The left map in `sheafShortComplexOfPresheaf` is the original presheaf morphism. -/
@[simp] lemma sheafShortComplexOfPresheaf_f_val {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    {h₁ : F₁.IsSheaf} {h₂ : F₂.IsSheaf} {h₃ : F₃.IsSheaf}
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} {hfg : f ≫ g = 0} :
    (sheafShortComplexOfPresheaf h₁ h₂ h₃ (f := f) (g := g) hfg).f.val = f := rfl

/-- The right map in `sheafShortComplexOfPresheaf` is the original presheaf morphism. -/
@[simp] lemma sheafShortComplexOfPresheaf_g_val {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    {h₁ : F₁.IsSheaf} {h₂ : F₂.IsSheaf} {h₃ : F₃.IsSheaf}
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} {hfg : f ≫ g = 0} :
    (sheafShortComplexOfPresheaf h₁ h₂ h₃ (f := f) (g := g) hfg).g.val = g := rfl

/-- A short exact sequence of sheaves remains short exact after viewing it through
`sheafShortComplexOfPresheaf`. -/
lemma sheafShortComplexOfPresheaf_shortExact_of_shortExact {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) :
    (sheafShortComplexOfPresheaf S.X₁.cond S.X₂.cond S.X₃.cond
      (f := S.f.val) (g := S.g.val)
      (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)).ShortExact := by
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
  let sectVForgetIso :
      sectV ⋙ forget AddCommGrpCat.{u} ≅
        sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op V) ⋙ forget AddCommGrpCat.{u} :=
    Functor.isoWhiskerRight
      (sheafSectionsNatIsoEvaluation
        (J := Opens.grothendieckTopology X) (A := AddCommGrpCat.{u}) (X := V))
      (forget AddCommGrpCat.{u})
  haveI : PreservesLimitsOfShape WalkingParallelPair (sectV ⋙ forget AddCommGrpCat.{u}) :=
    preservesLimitsOfShape_of_natIso sectVForgetIso.symm
  haveI : PreservesLimitsOfShape WalkingParallelPair sectV :=
    preservesLimitsOfShape_of_reflects_of_preserves sectV (forget AddCommGrpCat.{u})
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
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
    (hS := sheafShortComplexOfPresheaf_shortExact_of_shortExact hS)
    V x hx

/-! ### Structured-arrow Zorn setup for partial lifts -/

/-- Partial lifts of a section `s` along a morphism of sheaves. An object is an
open `V`, a section over `V`, and the proof that it maps to `s |_ V`. -/
private abbrev Under {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (g : F ⟶ G) {U : Opens X} (s : G.val.obj (op U)) :=
  StructuredArrow ⟨op U, s⟩
    (Functor.whiskerRight g.val (CategoryTheory.forget AddCommGrpCat.{u})).mapElements

private lemma structuredArrowsElementsSheafChainsBounded {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (g : F ⟶ G) {U : Opens X} (s : G.val.obj (op U))
    (c : Set (Under g s))
    (hchain : IsChain (fun x y => Nonempty (y ⟶ x)) c) :
    ∃ ub, ∀ a ∈ c, Nonempty (ub ⟶ a) := by
  let cV : c → Opens X := fun x => x.1.right.1.unop
  let cs : (x : c) → F.val.obj (op (cV x)) := fun x => x.1.right.2
  have hcompat : TopCat.Presheaf.IsCompatible F.val cV cs := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rfl
    · have htotal := hchain i.property j.property (fun h => hij (Subtype.ext h))
      rcases htotal with hji | hij'
      · rw [show (cV i).infLERight (cV j) =
            (cV i).infLELeft (cV j) ≫ hji.some.right.val.unop from Subsingleton.elim _ _,
          op_comp, Functor.map_comp, CategoryTheory.comp_apply]
        have hsec : ConcreteCategory.hom (F.val.map hji.some.right.val) j.1.right.2 =
            i.1.right.2 := CategoryOfElements.map_snd hji.some.right
        exact congrArg (ConcreteCategory.hom (F.val.map ((cV i).infLELeft (cV j)).op))
          hsec.symm
      · rw [show (cV i).infLELeft (cV j) =
            (cV i).infLERight (cV j) ≫ hij'.some.right.val.unop from Subsingleton.elim _ _,
          op_comp, Functor.map_comp, CategoryTheory.comp_apply]
        have hsec : ConcreteCategory.hom (F.val.map hij'.some.right.val) i.1.right.2 =
            j.1.right.2 := CategoryOfElements.map_snd hij'.some.right
        exact congrArg (ConcreteCategory.hom (F.val.map ((cV i).infLERight (cV j)).op)) hsec
  obtain ⟨t_gl, ht_gl, _⟩ := F.existsUnique_gluing cV cs hcompat
  have hVsup_le : iSup cV ≤ U := iSup_le fun j => leOfHom j.1.hom.val.unop
  have hcompat_gs : TopCat.Presheaf.IsCompatible G.val cV
      (fun j => ConcreteCategory.hom
        (G.val.map (homOfLE (le_trans (le_iSup cV j) hVsup_le)).op) s) := by
    intro i j
    dsimp
    rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
      ← G.val.map_comp, ← G.val.map_comp]
    exact congr_arg (G.val.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim _ _))
  obtain ⟨_, _, hgs_uniq⟩ := G.existsUnique_gluing cV _ hcompat_gs
  have hgt : ConcreteCategory.hom (g.val.app (op (iSup cV))) t_gl =
      ConcreteCategory.hom (G.val.map (homOfLE hVsup_le).op) s := by
    have hg_gl : TopCat.Presheaf.IsGluing G.val cV
        (fun j => ConcreteCategory.hom
          (G.val.map (homOfLE (le_trans (le_iSup cV j) hVsup_le)).op) s)
        (ConcreteCategory.hom (g.val.app (op (iSup cV))) t_gl) := by
      intro j
      rw [← g.val.naturality_apply _ t_gl, ht_gl j]
      have hmap := CategoryOfElements.map_snd j.1.hom
      simpa using hmap.symm
    have hs_gl : TopCat.Presheaf.IsGluing G.val cV
        (fun j => ConcreteCategory.hom
          (G.val.map (homOfLE (le_trans (le_iSup cV j) hVsup_le)).op) s)
        (ConcreteCategory.hom (G.val.map (homOfLE hVsup_le).op) s) := by
      intro j
      dsimp
      rw [← CategoryTheory.comp_apply, ← G.val.map_comp]
      exact congr_arg (G.val.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim _ _))
    exact (hgs_uniq _ hg_gl).trans (hgs_uniq _ hs_gl).symm
  let ub : Under g s :=
    StructuredArrow.mk (S := ⟨op U, s⟩)
      (T := (Functor.whiskerRight g.val (CategoryTheory.forget AddCommGrpCat.{u})).mapElements)
      (Y := ⟨op (iSup cV), t_gl⟩)
      (CategoryOfElements.homMk _ _ (homOfLE hVsup_le).op (by
        simpa using hgt.symm))
  refine ⟨ub, ?_⟩
  intro a ha
  exact Nonempty.intro (StructuredArrow.homMk
    (CategoryOfElements.homMk _ _ (homOfLE (le_iSup cV ⟨a, ha⟩)).op (by
      simpa [ub, cV, cs] using ht_gl ⟨a, ha⟩))
    (by cat_disch))

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
  obtain ⟨t, hmax⟩ := exists_maximal_of_chains_bounded
    (structuredArrowsElementsSheafChainsBounded Ssh.g s)
    (fun ⟨f⟩ ⟨g⟩ => ⟨g ≫ f⟩)
  let V₀ : Opens X := t.right.1.unop
  let t₀ : F₂.obj (op V₀) := t.right.2
  have hV₀U : V₀ ≤ U := leOfHom t.hom.val.unop
  have ht₀ : ConcreteCategory.hom (g.app (op V₀)) t₀ =
      ConcreteCategory.hom (F₃.map (homOfLE hV₀U).op) s := by
    have hmap := CategoryOfElements.map_snd t.hom
    simpa [Ssh, V₀, t₀] using hmap.symm
  have hUleV₀ : U ≤ V₀ := by
    by_contra hnot
    have hlt : V₀ < U := lt_of_le_not_ge hV₀U hnot
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
        rw [hfg_app]
        simp,
        add_zero, ht']
      exact congr_arg (F₃.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim _ _))
    have hcompat_patch : F₂.map (homOfLE inf_le_right).op t'' =
        F₂.map (homOfLE inf_le_left).op t₀ := by
      simp only [ht''_def, map_add]
      rw [show F₂.map (homOfLE inf_le_right).op (f.app (op W) ahat) =
        f.app (op (V₀ ⊓ W)) (F₁.map (homOfLE inf_le_right).op ahat) from
        (f.naturality_apply (homOfLE inf_le_right).op ahat).symm, hahat, ha]
      abel
    let BU : Bool → Opens X | false => V₀ | true => W
    let Bsf : (b : Bool) → F₂.obj (op (BU b)) | false => t₀ | true => t''
    have hcompat_glue : TopCat.Presheaf.IsCompatible F₂ BU Bsf := by
      intro i j
      match i, j with
      | false, false | true, true => rfl
      | false, true => exact hcompat_patch.symm
      | true, false =>
        show F₂.map (W.infLELeft V₀).op t'' = F₂.map (W.infLERight V₀).op t₀
        rw [show W.infLELeft V₀ = eqToHom (inf_comm W V₀) ≫ homOfLE inf_le_right
              from Subsingleton.elim _ _,
            show W.infLERight V₀ = eqToHom (inf_comm W V₀) ≫ homOfLE inf_le_left
              from Subsingleton.elim _ _,
          op_comp, Functor.map_comp, CategoryTheory.comp_apply,
          op_comp, Functor.map_comp, CategoryTheory.comp_apply,
          hcompat_patch]
    obtain ⟨t_new, ht_new, _⟩ := h₂.isSheafUniqueGluing BU Bsf hcompat_glue
    have hBU : ∀ b, BU b ≤ U := by
      intro b
      cases b
      · simpa [BU] using hV₀U
      · simpa [BU] using hWU
    have hBUU : iSup BU ≤ U := iSup_le hBU
    have hgt_new : ConcreteCategory.hom (g.app (op (iSup BU))) t_new =
        ConcreteCategory.hom (F₃.map (homOfLE hBUU).op) s := by
      let Bs : (b : Bool) → F₃.obj (op (BU b)) :=
        fun b => ConcreteCategory.hom (F₃.map (homOfLE (hBU b)).op) s
      have hcompat_Bs : TopCat.Presheaf.IsCompatible F₃ BU Bs := by
        intro i j
        dsimp [Bs]
        rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
          ← F₃.map_comp, ← F₃.map_comp]
        exact congr_arg (F₃.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim _ _))
      obtain ⟨_, _, hBs_uniq⟩ := h₃.isSheafUniqueGluing BU Bs hcompat_Bs
      have hg_gl : TopCat.Presheaf.IsGluing F₃ BU Bs
          (ConcreteCategory.hom (g.app (op (iSup BU))) t_new) := by
        intro b
        rw [← g.naturality_apply _ t_new, ht_new b]
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
      exact (hBs_uniq _ hg_gl).trans (hBs_uniq _ hs_gl).symm
    have hxBU : x ∈ iSup BU := by
      simp only [Opens.mem_iSup, BU]
      exact ⟨true, hxW⟩
    let t_new_under : Under Ssh.g s :=
      StructuredArrow.mk (S := ⟨op U, s⟩)
        (T := (Functor.whiskerRight Ssh.g.val
          (CategoryTheory.forget AddCommGrpCat.{u})).mapElements)
        (Y := ⟨op (iSup BU), t_new⟩)
        (CategoryOfElements.homMk _ _ (homOfLE hBUU).op (by
          simpa [Ssh] using hgt_new.symm))
    have h_extend : Nonempty (t_new_under ⟶ t) := by
      exact Nonempty.intro (StructuredArrow.homMk
        (CategoryOfElements.homMk _ _ (homOfLE (le_iSup BU false)).op (by
          simpa [t_new_under, V₀, t₀, BU, Bsf] using ht_new false))
        (by cat_disch))
    have h_back : Nonempty (t ⟶ t_new_under) := hmax t_new_under h_extend
    exact hxV₀ (leOfHom h_back.some.right.val.unop hxBU)
  exact ⟨ConcreteCategory.hom (F₂.map (homOfLE hUleV₀).op) t₀, by
    rw [g.naturality_apply (homOfLE hUleV₀).op t₀, ht₀]
    rw [← CategoryTheory.comp_apply, ← F₃.map_comp]
    rw [show (homOfLE hV₀U).op ≫ (homOfLE hUleV₀).op = 𝟙 (op U) from
      Subsingleton.elim _ _]
    simp⟩

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
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
    (hS := sheafShortComplexOfPresheaf_shortExact_of_shortExact hS)
    hX₁_epi U

/-- If `0 → F₁ → F₂ → F₃ → 0` is short exact on associated sheaves and
`⟨F₁, h₁⟩` is flasque, then `g(U) : F₂(U) → F₃(U)` is epi. -/
theorem epi_app_of_shortExact_flasque_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃}
    (hfg : f ≫ g = 0)
    (hS : (sheafShortComplexOfPresheaf h₁ h₂ h₃ (f := f) (g := g) hfg).ShortExact)
    [IsFlasqueSheaf (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)]
    (U : Opens X) :
    Epi (g.app (op U)) := by
  exact epi_app_of_shortExact_of_epi_restrictions_presheaf
    (F₁ := F₁) (F₂ := F₂) (F₃ := F₃) h₁ h₂ h₃ hfg hS
    (fun {_ _} i => by
      simpa using
        (IsFlasqueSheaf.epi_map
          (F := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) i)) U

-- Zorn argument for surjectivity of sections (Nugent, PR #35790).
theorem epi_app_of_shortExact_flasque {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) [IsFlasqueSheaf S.X₁] (U : Opens X) :
    Epi (S.g.val.app (op U)) := by
  letI : IsFlasqueSheaf (⟨S.X₁.val, S.X₁.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := by
    simpa using (inferInstance : IsFlasqueSheaf S.X₁)
  simpa using epi_app_of_shortExact_flasque_presheaf
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
    (hS := sheafShortComplexOfPresheaf_shortExact_of_shortExact hS) U

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
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
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

/-! ## Cohomological vanishing for flasque sheaves -/

/-- Presheaf-boundary wrapper for `sheafH_subsingleton_H1_of_flasque`: if a presheaf is a
    sheaf and the induced bundled sheaf is flasque, then its `H¹` is subsingleton. -/
theorem sheafH_subsingleton_H1_of_flasque_presheaf {X : TopCat.{u}}
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    [IsFlasqueSheaf ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))] :
    Subsingleton (Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1) := by
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  obtain ⟨ip⟩ := EnoughInjectives.presentation Fsh
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ip.shortComplex
  letI : Injective ((⟨S.X₂.val, S.X₂.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
    simpa [S] using (inferInstance : Injective S.X₂)
  have hSE :
      (ShortComplex.mk
        (X₁ := (⟨S.X₁.val, S.X₁.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (X₂ := (⟨S.X₂.val, S.X₂.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (X₃ := (⟨S.X₃.val, S.X₃.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (Sheaf.Hom.mk S.f.val)
        (Sheaf.Hom.mk S.g.val)
        (by
          apply Sheaf.Hom.ext
          exact congrArg Sheaf.Hom.val S.zero)).ShortExact := by
    simpa [S] using ip.shortExact_shortComplex
  have hg : Epi (S.g.val.app (op ⊤)) := by
    letI : IsFlasqueSheaf ((⟨S.X₁.val, S.X₁.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
      simpa [Fsh, S] using (inferInstance : IsFlasqueSheaf Fsh)
    simpa [S] using epi_app_of_shortExact_flasque_presheaf
      S.X₁.cond S.X₂.cond S.X₃.cond
      (f := S.f.val) (g := S.g.val)
      (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
      hSE ⊤
  simpa [Fsh, S] using sheafH_subsingleton_H1_of_injective_of_epi_app_top_presheaf
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
    hSE hg

/-- Flasque sheaves have vanishing `H¹`. This isolates the base case of flasque
    cohomological vanishing. -/
theorem sheafH_subsingleton_H1_of_flasque {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [IsFlasqueSheaf F] :
    Subsingleton (Sheaf.H F 1) := by
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F.val, F.cond⟩
  letI : IsFlasqueSheaf Fsh := by
    simpa [Fsh] using (inferInstance : IsFlasqueSheaf F)
  simpa [Fsh] using
    (sheafH_subsingleton_H1_of_flasque_presheaf (X := X) (F := F.val) F.cond)

/-- Presheaf-boundary `H¹` vanishing criterion with flasque middle term:
    if `0 → F₁ → F₂ → F₃ → 0` is short exact after bundling the presheaves as sheaves,
    `⟨F₂, h₂⟩` is flasque, and `g.app(⊤)` is epi, then `H¹(F₁)=0`. -/
theorem sheafH_subsingleton_H1_of_flasque_of_epi_app_top_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0)
    (hSE : (ShortComplex.mk
      (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f)
      (Sheaf.Hom.mk g)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg)).ShortExact)
    [IsFlasqueSheaf ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))]
    (hg : Epi (g.app (op ⊤))) :
    Subsingleton (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1) := by
  simpa using sheafH_subsingleton_H1_via_epi_app_top_presheaf
    (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
    h₁ h₂ h₃ hfg hSE
    (sheafH_subsingleton_H1_of_flasque_presheaf (F := F₂) h₂)
    hg

/-- Sheaf-level `H¹` vanishing criterion with flasque middle term:
    if `X₂` is flasque and `g.app(⊤)` is epi in a short exact sequence
    `0 → X₁ → X₂ → X₃ → 0`, then `H¹(X₁)=0`. -/
theorem sheafH_subsingleton_H1_of_flasque_of_epi_app_top {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hSE : S.ShortExact)
    [IsFlasqueSheaf S.X₂]
    (hg : Epi (S.g.val.app (op ⊤))) :
    Subsingleton (Sheaf.H S.X₁ 1) := by
  letI : IsFlasqueSheaf ((⟨S.X₂.val, S.X₂.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
    simpa using (inferInstance : IsFlasqueSheaf S.X₂)
  simpa using sheafH_subsingleton_H1_of_flasque_of_epi_app_top_presheaf
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
    (by simpa using hSE)
    (by simpa using hg)

/-- Presheaf-boundary `H¹` vanishing criterion for a pushed-forward short exact sequence:
    if the pushed-forward middle term is flasque and the source sequence has `H¹(F₁)=0`,
    then the pushed-forward kernel has vanishing `H¹`, provided the caller supplies the
    identification of `i⁻¹(⊤)` with `⊤`. -/
theorem sheafH_subsingleton_H1_of_flasque_of_epi_app_top_map_presheaf {X Y : TopCat.{u}}
    (i : X ⟶ Y)
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0)
    (hSE : (ShortComplex.mk
      (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f)
      (Sheaf.Hom.mk g)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg)).ShortExact)
    (hSE_map : (ShortComplex.mk
      (X₁ := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
        ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)))
      (X₂ := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
        ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)))
      (X₃ := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
        ((⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)))
      (Sheaf.Hom.mk ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map f))
      (Sheaf.Hom.mk ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map g))
      (by
        apply Sheaf.Hom.ext
        simpa using congrArg ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map) hfg)
      ).ShortExact)
    [IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
      ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)))]
    (h_top : (Opens.map i).obj ⊤ = ⊤)
    (h₁H : Subsingleton (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1)) :
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
      ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))) 1) := by
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (Sheaf.Hom.mk f)
    (Sheaf.Hom.mk g)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg)
  let T := S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)
  letI : IsFlasqueSheaf ((⟨T.X₂.val, T.X₂.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} Y)) := by
    simpa [S, T] using
      (inferInstance : IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
        ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))))
  simpa [S, T] using sheafH_subsingleton_H1_of_flasque_of_epi_app_top_presheaf
    (F₁ := T.X₁.val) (F₂ := T.X₂.val) (F₃ := T.X₃.val)
    T.X₁.cond T.X₂.cond T.X₃.cond
    (f := T.f.val) (g := T.g.val)
    (show T.f.val ≫ T.g.val = 0 from congrArg Sheaf.Hom.val T.zero)
    (by simpa [S, T] using hSE_map)
    (by
      change Epi (g.app (op ((Opens.map i).obj ⊤)))
      rw [h_top]
      exact epi_app_top_of_subsingleton_sheafH1_presheaf
        (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
        h₁ h₂ h₃ hfg hSE h₁H)

/-- Sheaf-level `H¹` vanishing criterion for a pushed-forward short exact sequence:
    if the mapped middle term is flasque and the source sequence has `H¹(X₁)=0`,
    then `H¹` vanishes on the mapped kernel, provided the caller supplies the
    identification of `f⁻¹(⊤)` with `⊤`. -/
theorem sheafH_subsingleton_H1_of_flasque_of_epi_app_top_map {X Y : TopCat.{u}}
    (f : X ⟶ Y)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hSE : S.ShortExact)
    (hSE_map : (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).ShortExact)
    [IsFlasqueSheaf ((S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).X₂)]
    (h_top : (Opens.map f).obj ⊤ = ⊤)
    (h₁ : Subsingleton (Sheaf.H S.X₁ 1)) :
    Subsingleton (Sheaf.H ((S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).X₁) 1) := by
  letI : IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj
      ((⟨S.X₂.val, S.X₂.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))) := by
    simpa using (inferInstance :
      IsFlasqueSheaf ((S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).X₂))
  simpa using sheafH_subsingleton_H1_of_flasque_of_epi_app_top_map_presheaf
    (i := f)
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
    (by simpa using hSE)
    (by simpa using hSE_map)
    h_top
    (by simpa using h₁)

/-- Presheaf-boundary form of `FlasqueVanishing`. -/
theorem sheafH_subsingleton_of_flasque_presheaf
    (X : TopCat.{u}) {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    [IsFlasqueSheaf (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)]
    (n : ℕ) :
    Subsingleton (Sheaf.H (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) (n + 1)) := by
  induction n generalizing F with
  | zero =>
      exact sheafH_subsingleton_H1_of_flasque_presheaf (F := F) hF
  | succ n ih =>
      let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
      obtain ⟨ip⟩ := EnoughInjectives.presentation Fsh
      let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ip.shortComplex
      letI : Injective ((⟨S.X₂.val, S.X₂.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
        simpa [S] using (inferInstance : Injective S.X₂)
      letI : IsFlasqueSheaf ((⟨S.X₃.val, S.X₃.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
        simpa [S] using
          (isFlasque_X₃_of_shortExact_presheaf
            S.X₁.cond S.X₂.cond S.X₃.cond
            (f := S.f.val) (g := S.g.val)
            (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
            (by simpa [S] using ip.shortExact_shortComplex))
      have h₃H : Subsingleton (Sheaf.H
          ((⟨S.X₃.val, S.X₃.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1)) := by
        simpa using (ih (F := S.X₃.val) S.X₃.cond)
      simpa [Fsh, S] using
        (sheafH_dimension_shift_presheaf
          (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
          S.X₁.cond S.X₂.cond S.X₃.cond
          (f := S.f.val) (g := S.g.val)
          (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
          (by simpa [S] using ip.shortExact_shortComplex)
          (n + 1) h₃H)

/-- **Flasque sheaves have vanishing higher cohomology** (Nugent, PR #35790). -/
instance FlasqueVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [IsFlasqueSheaf F]
    (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F.val, F.cond⟩
  letI : IsFlasqueSheaf Fsh := by
    simpa [Fsh] using (inferInstance : IsFlasqueSheaf F)
  simpa [Fsh] using
    (sheafH_subsingleton_of_flasque_presheaf (X := X) (F := F.val) F.cond n)
