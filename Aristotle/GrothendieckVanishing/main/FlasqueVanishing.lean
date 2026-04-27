import Aristotle.GrothendieckVanishing.main.CohomologyAPI
import Aristotle.GrothendieckVanishing.main.ZeroOutside

/-!
# FlasqueVanishing — Flasque sheaf theory and cohomological vanishing

This file collects the flasque-sheaf API used by the Grothendieck vanishing proof.

Main declarations:
* `IsFlasqueSheaf`
* `epi_app_of_shortExact_flasque_presheaf`
* `isFlasque_X₃_of_shortExact_presheaf`
* `isFlasque_of_injective`
* `sheafH_subsingleton_H1_of_flasque_presheaf`
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

private lemma presheaf_map_eq {X : TopCat.{u}}
    (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {U V : Opens X} (f g : U ⟶ V) (s : F.obj (op V)) :
    F.map f.op s = F.map g.op s :=
  congr_arg (F.map · s) (congr_arg Quiver.Hom.op (Subsingleton.elim f g))

private lemma map_glued_eq_of_local_eq {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (g : F ⟶ G)
    {ι : Type*} {U : Opens X} {B : ι → Opens X}
    {s : G.val.obj (op U)} {sF : ∀ i, F.val.obj (op (B i))}
    {t : F.val.obj (op (iSup B))}
    (hBU : ∀ i, B i ≤ U)
    (ht : TopCat.Presheaf.IsGluing F.val B sF t)
    (hlocal : ∀ i, ConcreteCategory.hom (g.val.app (op (B i))) (sF i) =
      ConcreteCategory.hom (G.val.map (homOfLE (hBU i)).op) s) :
    ConcreteCategory.hom (g.val.app (op (iSup B))) t =
      ConcreteCategory.hom (G.val.map (homOfLE (iSup_le hBU)).op) s := by
  apply G.eq_of_locally_eq
  intro i
  rw [← g.val.naturality_apply _ t, ht i, hlocal i]
  rw [← CategoryTheory.comp_apply, ← G.val.map_comp]
  exact presheaf_map_eq G.val _ _ s

private lemma exists_patch_of_shortExact {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (hX₁_epi : ∀ {U V : Opens X} (i : U ⟶ V), Epi (S.X₁.val.map i.op))
    {U V W : Opens X} {s : S.X₃.val.obj (op U)}
    (hVU : V ≤ U) (hWU : W ≤ U)
    {tV : S.X₂.val.obj (op V)} {tW : S.X₂.val.obj (op W)}
    (htV : ConcreteCategory.hom (S.g.val.app (op V)) tV =
      ConcreteCategory.hom (S.X₃.val.map (homOfLE hVU).op) s)
    (htW : ConcreteCategory.hom (S.g.val.app (op W)) tW =
      ConcreteCategory.hom (S.X₃.val.map (homOfLE hWU).op) s) :
    ∃ tW' : S.X₂.val.obj (op W),
      ConcreteCategory.hom (S.g.val.app (op W)) tW' =
        ConcreteCategory.hom (S.X₃.val.map (homOfLE hWU).op) s ∧
      S.X₂.val.map (homOfLE inf_le_right).op tW' =
        S.X₂.val.map (homOfLE inf_le_left).op tV := by
  have hdiff_ker : S.g.val.app (op (V ⊓ W))
      (S.X₂.val.map (homOfLE inf_le_left).op tV -
       S.X₂.val.map (homOfLE inf_le_right).op tW) = 0 := by
    simp only [map_sub]
    rw [S.g.val.naturality_apply _ tV, htV, S.g.val.naturality_apply _ tW, htW,
      sub_eq_zero]
    simp only [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact presheaf_map_eq S.X₃.val _ _ s
  obtain ⟨a, ha⟩ := sections_exact_of_shortExact_presheaf
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
    (hS := sheafShortComplexOfPresheaf_shortExact_of_shortExact hS)
    (V ⊓ W) _ hdiff_ker
  obtain ⟨ahat, hahat⟩ := (AddCommGrpCat.epi_iff_surjective _).mp
    (hX₁_epi (homOfLE inf_le_right : V ⊓ W ⟶ W)) a
  have hfg_app : S.f.val.app (op W) ≫ S.g.val.app (op W) = 0 := by
    have hfg : S.f.val ≫ S.g.val = 0 := congrArg Sheaf.Hom.val S.zero
    simpa using congrArg (fun α => α.app (op W)) hfg
  let tW' := tW + S.f.val.app (op W) ahat
  refine ⟨tW', ?_, ?_⟩
  · simp only [tW', map_add, show S.g.val.app (op W) (S.f.val.app (op W) ahat) = 0 from by
      show (S.f.val.app (op W) ≫ S.g.val.app (op W)) ahat = 0
      rw [hfg_app]
      simp,
      add_zero, htW]
  · simp only [tW', map_add]
    rw [show S.X₂.val.map (homOfLE inf_le_right).op (S.f.val.app (op W) ahat) =
      S.f.val.app (op (V ⊓ W)) (S.X₁.val.map (homOfLE inf_le_right).op ahat) from
      (S.f.val.naturality_apply (homOfLE inf_le_right).op ahat).symm, hahat, ha]
    abel

private lemma bool_isCompatible_of_false_true_eq {X : TopCat.{u}}
    (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    {B : Bool → Opens X} {sB : (b : Bool) → F.obj (op (B b))}
    (h : F.map ((B false).infLERight (B true)).op (sB true) =
      F.map ((B false).infLELeft (B true)).op (sB false)) :
    TopCat.Presheaf.IsCompatible F B sB := by
  intro i j
  match i, j with
  | false, false | true, true => rfl
  | false, true => exact h.symm
  | true, false =>
    show F.map ((B true).infLELeft (B false)).op (sB true) =
      F.map ((B true).infLERight (B false)).op (sB false)
    rw [show (B true).infLELeft (B false) =
          eqToHom (inf_comm (B true) (B false)) ≫ (B false).infLERight (B true)
          from Subsingleton.elim _ _,
        show (B true).infLERight (B false) =
          eqToHom (inf_comm (B true) (B false)) ≫ (B false).infLELeft (B true)
          from Subsingleton.elim _ _,
      op_comp, Functor.map_comp, CategoryTheory.comp_apply,
      op_comp, Functor.map_comp, CategoryTheory.comp_apply,
      h]

private abbrev underMk {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (g : F ⟶ G) {U V : Opens X} (s : G.val.obj (op U))
    (t : F.val.obj (op V)) (hVU : V ≤ U)
    (ht : ConcreteCategory.hom (g.val.app (op V)) t =
      ConcreteCategory.hom (G.val.map (homOfLE hVU).op) s) :
    StructuredArrow ⟨op U, s⟩
      (Functor.whiskerRight g.val (CategoryTheory.forget AddCommGrpCat.{u})).mapElements :=
  StructuredArrow.mk (S := ⟨op U, s⟩)
    (T := (Functor.whiskerRight g.val (CategoryTheory.forget AddCommGrpCat.{u})).mapElements)
    (Y := ⟨op V, t⟩)
    (CategoryOfElements.homMk _ _ (homOfLE hVU).op (by simpa using ht.symm))

/-! ### Structured-arrow Zorn setup for partial lifts -/

/-- Partial lifts of a section `s` along a morphism of sheaves. An object is an
open `V`, a section over `V`, and the proof that it maps to `s |_ V`. -/
private abbrev Under {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (g : F ⟶ G) {U : Opens X} (s : G.val.obj (op U)) :=
  StructuredArrow ⟨op U, s⟩
    (Functor.whiskerRight g.val (CategoryTheory.forget AddCommGrpCat.{u})).mapElements

private lemma under_exists_extension_containing {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (hX₁_epi : ∀ {U V : Opens X} (i : U ⟶ V), Epi (S.X₁.val.map i.op))
    {U : Opens X} (s : S.X₃.val.obj (op U))
    (hls : TopCat.Presheaf.IsLocallySurjective S.g.val)
    (t : Under S.g s)
    {x : X} (hxU : x ∈ U) (_hxV₀ : x ∉ t.right.1.unop) :
    ∃ y : Under S.g s, Nonempty (y ⟶ t) ∧ x ∈ y.right.1.unop := by
  let V₀ : Opens X := t.right.1.unop
  let t₀ : S.X₂.val.obj (op V₀) := t.right.2
  have hV₀U : V₀ ≤ U := leOfHom t.hom.val.unop
  have ht₀ : ConcreteCategory.hom (S.g.val.app (op V₀)) t₀ =
      ConcreteCategory.hom (S.X₃.val.map (homOfLE hV₀U).op) s := by
    have hmap := CategoryOfElements.map_snd t.hom
    simpa [V₀, t₀] using hmap.symm
  obtain ⟨W, iWU, ⟨t', ht'⟩, hxW⟩ := (hls.imageSieve_mem s) x hxU
  have hWU : W ≤ U := leOfHom iWU
  obtain ⟨t'', hgt'', hcompat_patch⟩ :=
    exists_patch_of_shortExact hS hX₁_epi hV₀U hWU ht₀ ht'
  let BU : Bool → Opens X | false => V₀ | true => W
  let Bsf : (b : Bool) → S.X₂.val.obj (op (BU b)) | false => t₀ | true => t''
  have hcompat_glue : TopCat.Presheaf.IsCompatible S.X₂.val BU Bsf :=
    bool_isCompatible_of_false_true_eq S.X₂.val hcompat_patch
  obtain ⟨t_new, ht_new, _⟩ := S.X₂.existsUnique_gluing BU Bsf hcompat_glue
  have hBU : ∀ b, BU b ≤ U
    | false => by simpa [BU] using hV₀U
    | true => by simpa [BU] using hWU
  have hBUU : iSup BU ≤ U := iSup_le hBU
  have hgt_new : ConcreteCategory.hom (S.g.val.app (op (iSup BU))) t_new =
      ConcreteCategory.hom (S.X₃.val.map (homOfLE hBUU).op) s := by
    apply map_glued_eq_of_local_eq S.g hBU ht_new
    intro b
    cases b <;> simp only [BU, Bsf]
    · exact ht₀
    · exact hgt''
  have hxBU : x ∈ iSup BU := Opens.mem_iSup.mpr ⟨true, by simpa [BU] using hxW⟩
  let t_new_under : Under S.g s := underMk S.g s t_new hBUU hgt_new
  refine ⟨t_new_under, ?_, ?_⟩
  · exact Nonempty.intro (StructuredArrow.homMk
      (CategoryOfElements.homMk _ _ (homOfLE (le_iSup BU false)).op (by
        simpa [t_new_under, V₀, t₀, BU, Bsf] using ht_new false))
      (by cat_disch))
  · simpa [t_new_under] using hxBU

private lemma chain_isCompatible_of_chain {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {g : F ⟶ G} {U : Opens X} {s : G.val.obj (op U)}
    {c : Set (Under g s)}
    (hchain : IsChain (fun x y => Nonempty (y ⟶ x)) c) :
    TopCat.Presheaf.IsCompatible F.val
      (fun x : c => x.1.right.1.unop)
      (fun x : c => x.1.right.2) := by
  let cV : c → Opens X := fun x => x.1.right.1.unop
  let cs : (x : c) → F.val.obj (op (cV x)) := fun x => x.1.right.2
  change TopCat.Presheaf.IsCompatible F.val cV cs
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

private lemma under_chain_upper_bound {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (g : F ⟶ G) {U : Opens X} (s : G.val.obj (op U))
    (c : Set (Under g s))
    (hchain : IsChain (fun x y => Nonempty (y ⟶ x)) c) :
    ∃ ub, ∀ a ∈ c, Nonempty (ub ⟶ a) := by
  let cV : c → Opens X := fun x => x.1.right.1.unop
  let cs : (x : c) → F.val.obj (op (cV x)) := fun x => x.1.right.2
  have hcompat : TopCat.Presheaf.IsCompatible F.val cV cs := by
    simpa [cV, cs] using chain_isCompatible_of_chain (g := g) (s := s) (c := c) hchain
  obtain ⟨t_gl, ht_gl, _⟩ := F.existsUnique_gluing cV cs hcompat
  have hVsup_le : iSup cV ≤ U := iSup_le fun j => leOfHom j.1.hom.val.unop
  have hgt : ConcreteCategory.hom (g.val.app (op (iSup cV))) t_gl =
      ConcreteCategory.hom (G.val.map (homOfLE hVsup_le).op) s := by
    apply map_glued_eq_of_local_eq g (fun j => le_trans (le_iSup cV j) hVsup_le) ht_gl
    intro j
    have hmap := CategoryOfElements.map_snd j.1.hom
    simpa using hmap.symm
  let ub : Under g s := underMk g s t_gl hVsup_le hgt
  refine ⟨ub, fun a ha => ?_⟩
  exact Nonempty.intro (StructuredArrow.homMk
    (CategoryOfElements.homMk _ _ (homOfLE (le_iSup cV ⟨a, ha⟩)).op (by
      simpa [ub, cV, cs] using ht_gl ⟨a, ha⟩))
    (by cat_disch))

private lemma under_maximal_eq_top {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (hX₁_epi : ∀ {U V : Opens X} (i : U ⟶ V), Epi (S.X₁.val.map i.op))
    {U : Opens X} (s : S.X₃.val.obj (op U))
    (hls : TopCat.Presheaf.IsLocallySurjective S.g.val)
    (t : Under S.g s)
    (hmax : ∀ y : Under S.g s, Nonempty (y ⟶ t) → Nonempty (t ⟶ y)) :
    U ≤ t.right.1.unop := by
  let V₀ : Opens X := t.right.1.unop
  have hV₀U : V₀ ≤ U := leOfHom t.hom.val.unop
  by_contra hnot
  have hlt : V₀ < U := lt_of_le_not_ge hV₀U hnot
  obtain ⟨x, hxU, hxV₀⟩ := Set.not_subset.mp hlt.2
  obtain ⟨y, hyt, hxy⟩ :=
    under_exists_extension_containing hS hX₁_epi s hls t hxU (by simpa [V₀] using hxV₀)
  have h_back : Nonempty (t ⟶ y) := hmax y hyt
  exact hxV₀ (leOfHom h_back.some.right.val.unop hxy)

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
    (under_chain_upper_bound Ssh.g s)
    (fun ⟨f⟩ ⟨g⟩ => ⟨g ≫ f⟩)
  let V₀ : Opens X := t.right.1.unop
  let t₀ : F₂.obj (op V₀) := t.right.2
  have hV₀U : V₀ ≤ U := leOfHom t.hom.val.unop
  have ht₀ : ConcreteCategory.hom (g.app (op V₀)) t₀ =
      ConcreteCategory.hom (F₃.map (homOfLE hV₀U).op) s := by
    have hmap := CategoryOfElements.map_snd t.hom
    simpa [Ssh, V₀, t₀] using hmap.symm
  have hUleV₀ : U ≤ V₀ := by
    simpa [Ssh, V₀] using
      under_maximal_eq_top (S := Ssh) hSsh
        (by
          intro U V i
          simpa [Ssh] using hX₁_epi i)
        s (by simpa [Ssh] using hls) t hmax
  exact ⟨ConcreteCategory.hom (F₂.map (homOfLE hUleV₀).op) t₀, by
    rw [g.naturality_apply (homOfLE hUleV₀).op t₀, ht₀]
    rw [← CategoryTheory.comp_apply, ← F₃.map_comp]
    rw [show (homOfLE hV₀U).op ≫ (homOfLE hUleV₀).op = 𝟙 (op U) from
      Subsingleton.elim _ _]
    simp⟩

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

/-- Presheaf-boundary `H¹` vanishing criterion for flasque sheaves: if a presheaf is a
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
