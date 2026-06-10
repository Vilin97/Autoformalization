import Aristotle.GrothendieckVanishing.main.CohomologyAPI
import Aristotle.GrothendieckVanishing.main.ZeroOutside

/-!
# Flasque sheaf theory and cohomological vanishing

A sheaf of abelian groups is **flasque** when every restriction map is epi. Such sheaves
have vanishing higher cohomology, which is one of the key inputs to Grothendieck vanishing.

## Main definitions

* `IsFlasqueSheaf` — the flasque predicate.

## Main results

* `epi_app_of_shortExact_flasque`, `isFlasque_X₃_of_shortExact` — flasqueness propagates
  through short exact sequences.
* `isFlasque_of_injective` — every injective sheaf is flasque.
* `sheafH_subsingleton_H1_of_flasque`, `sheafH_subsingleton_of_flasque` — flasque sheaves
  have vanishing `Hⁿ` for `n ≥ 1`.

The four sub-lemmas inside the `epi_app_of_shortExact_of_epi_restrictions` block are
adapted from Brian Nugent's Mathlib PR #35790.

Generic `Sheaf.H` and `Ext` API lives in `CohomologyAPI.lean`.
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
abbrev IsFlasqueSheaf {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op)

/-- For a short exact sequence of sheaves, the sequence of sections at any open `V` is
exact: if `g_V x = 0`, then `x` lies in the image of `f_V`. -/
lemma sections_exact_of_shortExact {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (V : Opens X) (x : S.X₂.val.obj (op V))
    (hx : ConcreteCategory.hom (S.g.val.app (op V)) x = 0) :
    ∃ a : S.X₁.val.obj (op V),
      ConcreteCategory.hom (S.f.val.app (op V)) a = x := by
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
  have hexact : (S.map sectV).Exact :=
    hS.exact.map_of_mono_of_preservesKernel sectV hS.mono_f inferInstance
  simpa using
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
  obtain ⟨a, ha⟩ := sections_exact_of_shortExact hS (V ⊓ W) _ hdiff_ker
  obtain ⟨ahat, hahat⟩ := (AddCommGrpCat.epi_iff_surjective _).mp
    (hX₁_epi (homOfLE inf_le_right : V ⊓ W ⟶ W)) a
  have hfg_app : S.f.val.app (op W) ≫ S.g.val.app (op W) = 0 := by
    have hfg : S.f.val ≫ S.g.val = 0 := congrArg Sheaf.Hom.val S.zero
    simpa using congrArg (fun α ↦ α.app (op W)) hfg
  let tW' := tW + S.f.val.app (op W) ahat
  have hgf_zero : S.g.val.app (op W) (S.f.val.app (op W) ahat) = 0 := by
    show (S.f.val.app (op W) ≫ S.g.val.app (op W)) ahat = 0
    rw [hfg_app]; simp
  have hf_naturality :
      S.X₂.val.map (homOfLE inf_le_right).op (S.f.val.app (op W) ahat) =
        S.f.val.app (op (V ⊓ W)) (S.X₁.val.map (homOfLE inf_le_right).op ahat) :=
    (S.f.val.naturality_apply (homOfLE inf_le_right).op ahat).symm
  refine ⟨tW', ?_, ?_⟩
  · simp only [tW', map_add, hgf_zero, add_zero, htW]
  · simp only [tW', map_add]
    rw [hf_naturality, hahat, ha]
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

private lemma chain_isCompatible_of_chain {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {g : F ⟶ G} {U : Opens X} {s : G.val.obj (op U)}
    {c : Set (StructuredArrow ⟨op U, s⟩
      (Functor.whiskerRight g.val (CategoryTheory.forget AddCommGrpCat.{u})).mapElements)}
    (hchain : IsChain (fun x y ↦ Nonempty (y ⟶ x)) c) :
    TopCat.Presheaf.IsCompatible F.val
      (fun x : c ↦ x.1.right.1.unop)
      (fun x : c ↦ x.1.right.2) := by
  let cV : c → Opens X := fun x ↦ x.1.right.1.unop
  let cs : (x : c) → F.val.obj (op (cV x)) := fun x ↦ x.1.right.2
  change TopCat.Presheaf.IsCompatible F.val cV cs
  intro i j
  by_cases hij : i = j
  · subst hij
    rfl
  · have htotal := hchain i.property j.property (fun h ↦ hij (Subtype.ext h))
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

private lemma exists_glued_lift_upper_bound {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (g : F ⟶ G) {U : Opens X} (s : G.val.obj (op U))
    {ι : Type*}
    (T : ι → StructuredArrow ⟨op U, s⟩
      (Functor.whiskerRight g.val (CategoryTheory.forget AddCommGrpCat.{u})).mapElements)
    (hcompat : TopCat.Presheaf.IsCompatible F.val
      (fun i ↦ (T i).right.1.unop) (fun i ↦ (T i).right.2)) :
    ∃ y : StructuredArrow ⟨op U, s⟩
        (Functor.whiskerRight g.val
          (CategoryTheory.forget AddCommGrpCat.{u})).mapElements,
      y.right.1.unop = iSup (fun i ↦ (T i).right.1.unop) ∧
      ∀ i, Nonempty (y ⟶ T i) := by
  let cV : ι → Opens X := fun i ↦ (T i).right.1.unop
  let cs : (i : ι) → F.val.obj (op (cV i)) := fun i ↦ (T i).right.2
  have hcompat' : TopCat.Presheaf.IsCompatible F.val cV cs := by
    simpa [cV, cs] using hcompat
  obtain ⟨t_gl, ht_gl, _⟩ := F.existsUnique_gluing cV cs hcompat'
  have hVsup_le : iSup cV ≤ U := iSup_le fun i ↦ leOfHom (T i).hom.val.unop
  have hgt : ConcreteCategory.hom (g.val.app (op (iSup cV))) t_gl =
      ConcreteCategory.hom (G.val.map (homOfLE hVsup_le).op) s := by
    apply map_glued_eq_of_local_eq g (fun j ↦ le_trans (le_iSup cV j) hVsup_le) ht_gl
    intro j
    have hmap := CategoryOfElements.map_snd (T j).hom
    simpa [cV, cs] using hmap.symm
  let y := underMk g s t_gl hVsup_le hgt
  refine ⟨y, rfl, fun i ↦ ?_⟩
  exact Nonempty.intro (StructuredArrow.homMk
    (CategoryOfElements.homMk _ _ (homOfLE (le_iSup cV i)).op (by
      simpa [y, cV, cs] using ht_gl i))
    (by cat_disch))

/-! ### Structured-arrow Zorn setup for partial lifts -/

/-- Partial lifts of a section `s` along a morphism of sheaves. An object is an
open `V`, a section over `V`, and the proof that it maps to `s |_ V`. -/
private abbrev Under {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (g : F ⟶ G) {U : Opens X} (s : G.val.obj (op U)) :=
  StructuredArrow ⟨op U, s⟩
    (Functor.whiskerRight g.val (CategoryTheory.forget AddCommGrpCat.{u})).mapElements
private lemma under_extend_by_one_open {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (hX₁_epi : ∀ {U V : Opens X} (i : U ⟶ V), Epi (S.X₁.val.map i.op))
    {U : Opens X} (s : S.X₃.val.obj (op U))
    (t : Under S.g s)
    (W : Opens X) (hWU : W ≤ U)
    (t' : S.X₂.val.obj (op W))
    (ht' : ConcreteCategory.hom (S.g.val.app (op W)) t' =
      ConcreteCategory.hom (S.X₃.val.map (homOfLE hWU).op) s)
    {x : X} (hxW : x ∈ W) :
    ∃ y : Under S.g s, Nonempty (y ⟶ t) ∧ x ∈ y.right.1.unop := by
  let V₀ : Opens X := t.right.1.unop
  let t₀ : S.X₂.val.obj (op V₀) := t.right.2
  have hV₀U : V₀ ≤ U := leOfHom t.hom.val.unop
  have ht₀ : ConcreteCategory.hom (S.g.val.app (op V₀)) t₀ =
      ConcreteCategory.hom (S.X₃.val.map (homOfLE hV₀U).op) s := by
    have hmap := CategoryOfElements.map_snd t.hom
    simpa [V₀, t₀] using hmap.symm
  obtain ⟨t'', hgt'', hcompat_patch⟩ :=
    exists_patch_of_shortExact hS hX₁_epi hV₀U hWU ht₀ ht'
  let T : Bool → Under S.g s
    | false => t
    | true => underMk S.g s t'' hWU hgt''
  have hcompat_glue : TopCat.Presheaf.IsCompatible S.X₂.val
      (fun b ↦ (T b).right.1.unop) (fun b ↦ (T b).right.2) := by
    apply bool_isCompatible_of_false_true_eq S.X₂.val
    simpa [T, V₀, t₀] using hcompat_patch
  obtain ⟨y, hy_open, hy⟩ := exists_glued_lift_upper_bound S.g s T hcompat_glue
  refine ⟨y, hy false, ?_⟩
  rw [hy_open]
  exact Opens.mem_iSup.mpr ⟨true, by simpa [T] using hxW⟩

/-- If `0 → X₁ → X₂ → X₃ → 0` is short exact and every restriction map of the
underlying presheaf `S.X₁.val` is epi, then `g(U) : X₂(U) → X₃(U)` is epi. -/
theorem epi_app_of_shortExact_of_epi_restrictions {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (hX₁_epi : ∀ {U V : Opens X} (i : U ⟶ V), Epi (S.X₁.val.map i.op))
    (U : Opens X) :
    Epi (S.g.val.app (op U)) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  haveI : Epi S.g := by
    simpa using hS.epi_g
  have hls : TopCat.Presheaf.IsLocallySurjective S.g.val := by
    simpa using (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} S.g).mpr inferInstance
  obtain ⟨t, hmax⟩ := exists_maximal_of_chains_bounded
    (fun (c : Set (Under S.g s)) hchain ↦ by
      have hcompat : TopCat.Presheaf.IsCompatible S.X₂.val
          (fun x : c ↦ x.1.right.1.unop) (fun x : c ↦ x.1.right.2) :=
        chain_isCompatible_of_chain (g := S.g) (s := s) (c := c) hchain
      obtain ⟨ub, _, hub⟩ := exists_glued_lift_upper_bound S.g s (fun x : c ↦ x.1) hcompat
      exact ⟨ub, fun a ha ↦ hub ⟨a, ha⟩⟩)
    (fun {a b c : Under S.g s} (hab : Nonempty (b ⟶ a)) (hbc : Nonempty (c ⟶ b)) ↦
      ⟨hbc.some ≫ hab.some⟩)
  let V₀ : Opens X := t.right.1.unop
  let t₀ : S.X₂.val.obj (op V₀) := t.right.2
  have hV₀U : V₀ ≤ U := leOfHom t.hom.val.unop
  have ht₀ : ConcreteCategory.hom (S.g.val.app (op V₀)) t₀ =
      ConcreteCategory.hom (S.X₃.val.map (homOfLE hV₀U).op) s := by
    have hmap := CategoryOfElements.map_snd t.hom
    simpa [V₀, t₀] using hmap.symm
  have hUleV₀ : U ≤ V₀ := by
    by_contra hnot
    have hlt : V₀ < U := lt_of_le_not_ge hV₀U hnot
    obtain ⟨x, hxU, hxV₀⟩ := Set.not_subset.mp hlt.2
    obtain ⟨W, iWU, ⟨t', ht'⟩, hxW⟩ := (hls.imageSieve_mem s) x hxU
    obtain ⟨y, hyt, hxy⟩ :=
      under_extend_by_one_open (S := S) hS hX₁_epi
        s t W (leOfHom iWU) t' ht' hxW
    have h_back : Nonempty (t ⟶ y) := hmax y hyt
    exact hxV₀ (leOfHom h_back.some.right.val.unop hxy)
  exact ⟨ConcreteCategory.hom (S.X₂.val.map (homOfLE hUleV₀).op) t₀, by
    rw [S.g.val.naturality_apply (homOfLE hUleV₀).op t₀, ht₀]
    rw [← CategoryTheory.comp_apply, ← S.X₃.val.map_comp]
    rw [show (homOfLE hV₀U).op ≫ (homOfLE hUleV₀).op = 𝟙 (op U) from
      Subsingleton.elim _ _]
    simp⟩

/-- If `0 → X₁ → X₂ → X₃ → 0` is short exact and `X₁` is flasque, then
`g(U) : X₂(U) → X₃(U)` is epi. -/
theorem epi_app_of_shortExact_flasque {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (hX₁ : IsFlasqueSheaf S.X₁)
    (U : Opens X) :
    Epi (S.g.val.app (op U)) := by
  exact epi_app_of_shortExact_of_epi_restrictions hS
    (fun {_ _} i ↦ hX₁ i) U

/-- Quotients of flasque sheaves are flasque along a short exact sequence. -/
theorem isFlasque_X₃_of_shortExact {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (hX₁ : IsFlasqueSheaf S.X₁)
    (hX₂ : IsFlasqueSheaf S.X₂) :
    IsFlasqueSheaf S.X₃ := by
  intro U V j
  have hg_U : Epi (S.g.val.app (op U)) :=
    epi_app_of_shortExact_of_epi_restrictions hS
      (fun {_ _} i ↦ hX₁ i) U
  have hres₂ : Epi (S.X₂.val.map j.op) := hX₂ j
  rw [AddCommGrpCat.epi_iff_surjective] at hg_U hres₂ ⊢
  intro z
  obtain ⟨w, hw⟩ := hg_U z
  obtain ⟨x, hx⟩ := hres₂ w
  exact ⟨ConcreteCategory.hom (S.g.val.app (op V)) x, by
    have := congrArg (· x) (S.g.val.naturality j.op)
    simp only [AddCommGrpCat.hom_comp] at this
    exact this.symm.trans (by simp [hx, hw])⟩

/-- Injective sheaves are flasque. -/
theorem isFlasque_of_injective {X : TopCat.{u}}
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] : IsFlasqueSheaf I := by
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  obtain ⟨g, hg⟩ := Injective.factors
    (TopCat.Sheaf.zeroOutsideInt.sHom s) (TopCat.Sheaf.zeroOutsideInt.openHom (leOfHom i))
  refine ⟨g.val.app (op V) (TopCat.Sheaf.zeroOutsideInt.generator V), ?_⟩
  have hi_eq : I.val.map i.op = I.val.map (homOfLE (leOfHom i)).op :=
    congr_arg I.val.map (congr_arg Quiver.Hom.op (Subsingleton.elim _ _))
  rw [hi_eq, ← g.val.naturality_apply (homOfLE (leOfHom i)).op,
    ← TopCat.Sheaf.zeroOutsideInt.openHom_val_app_generator]
  change ((TopCat.Sheaf.zeroOutsideInt.openHom (leOfHom i) ≫ g).val.app (op U))
    (TopCat.Sheaf.zeroOutsideInt.generator U) = s
  rw [hg]
  exact TopCat.Sheaf.zeroOutsideInt.sHom_app_generator s

/-! ## Cohomological vanishing for flasque sheaves -/

/-- `H¹` vanishes for flasque sheaves. -/
theorem sheafH_subsingleton_H1_of_flasque {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : IsFlasqueSheaf F) :
    Subsingleton (Sheaf.H F 1) := by
  obtain ⟨ip⟩ := EnoughInjectives.presentation F
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ip.shortComplex
  letI : Injective S.X₂ := by
    simpa [S] using (inferInstance : Injective S.X₂)
  have hg : Epi (S.g.val.app (op ⊤)) := by
    simpa [S] using epi_app_of_shortExact_flasque
      (by simpa [S] using ip.shortExact_shortComplex)
      (fun i ↦ by simpa [S] using hF i) ⊤
  simpa [S] using
    sheafH_subsingleton_H1_of_injective_of_epi_app_top
      (by simpa [S] using ip.shortExact_shortComplex) hg

/-- Flasque sheaves have vanishing higher cohomology. -/
theorem sheafH_subsingleton_of_flasque
    (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : IsFlasqueSheaf F)
    (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  induction n generalizing F with
  | zero =>
      exact sheafH_subsingleton_H1_of_flasque F hF
  | succ n ih =>
      obtain ⟨ip⟩ := EnoughInjectives.presentation F
      let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ip.shortComplex
      letI : Injective S.X₂ := by
        simpa [S] using (inferInstance : Injective S.X₂)
      have hX₁ : IsFlasqueSheaf S.X₁ := fun i ↦ by simpa [S] using hF i
      have hX₂ : IsFlasqueSheaf S.X₂ := isFlasque_of_injective S.X₂
      have hX₃ : IsFlasqueSheaf S.X₃ := fun i ↦ by
        simpa [S] using
          (isFlasque_X₃_of_shortExact
            (by simpa [S] using ip.shortExact_shortComplex) hX₁ hX₂) i
      have h₃H : Subsingleton (Sheaf.H S.X₃ (n + 1)) := by
        simpa using (ih S.X₃ hX₃)
      simpa [S] using
        (sheafH_dimension_shift_of_injective
          (S := S)
          (by simpa [S] using ip.shortExact_shortComplex)
          (n + 1) h₃H)
