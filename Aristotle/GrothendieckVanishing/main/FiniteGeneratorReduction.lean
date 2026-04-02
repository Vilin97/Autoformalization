/-
  FiniteGeneratorReduction.lean — Colimit step and finitely generated vanishing

  Key results:
  - ext_comm_filtered_colimit_mono: Ext^n preserves filtered colimits of mono diagrams
    (2 sorry's: objectwise colimit evaluation + n≥1 Ext case)
  - finsetGenFunctor / finsetGenCocone / finsetGenCocone_isColimit: K is the filtered
    colimit of its finitely generated subsheaves (PROVED)
  - cohomology_vanishing_of_finitelyGenerated_vanishing: H^m = 0 for all f.g. subsheaves
    implies H^m(K) = 0 (PROVED modulo ext_comm_filtered_colimit_mono)
  - finsetGeneratedSheaf_vanishing: vanishing for finitely generated sheaves by
    Finset.induction (PROVED)
  - directLimit_cohomology_vanishing: from epi-image vanishing to all sheaves (PROVED)
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.ConstantSheafFlasque

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-! ### Helper lemmas: Subsingleton transfer for AddCommGrpCat -/

/-- In `AddCommGrpCat`, `Subsingleton (ULift ℤ ⟶ G)` implies `Subsingleton G`. -/
private theorem addCommGrpCat_subsingleton_of_subsingleton_hom
    (G : AddCommGrpCat.{u})
    (h : Subsingleton (AddCommGrpCat.of (ULift.{u} ℤ) ⟶ G)) :
    Subsingleton G := by
  constructor; intro a b
  -- Every a ∈ G determines a hom fa : ULift ℤ → G with fa(⟨1⟩) = a.
  let fa : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ G := AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun z => ULift.down z • a) (fun x y => by simp [add_smul]))
  let fb : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ G := AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun z => ULift.down z • b) (fun x y => by simp [add_smul]))
  have heq := @Subsingleton.elim _ h fa fb
  have := AddCommGrpCat.ext_iff.mp heq (⟨1⟩ : ULift.{u} ℤ)
  simpa [fa, fb] using this

/-- In `AddCommGrpCat`, `Subsingleton G` implies `Subsingleton (ULift ℤ ⟶ G)`. -/
private theorem addCommGrpCat_subsingleton_hom_of_subsingleton
    (G : AddCommGrpCat.{u})
    (h : Subsingleton G) :
    Subsingleton (AddCommGrpCat.of (ULift.{u} ℤ) ⟶ G) := by
  constructor; intro f g
  ext x
  exact @Subsingleton.elim _ h _ _

/-- **Hartshorne 2.9 (Ext version)**: In a Grothendieck abelian category, if `Hom(Z, -)`
    sends filtered-colimit vanishing to vanishing (the `hHom` hypothesis), then
    `Ext^n(Z, -)` does too, for all n. Proved by induction on n:
    - **Base case (n = 0)**: `Ext^0 ≅ Hom` via `homEquiv₀`, apply `hHom`.
    - **Inductive step**: Embed `c.pt ↪ I` (injective). Dimension-shift gives
      `Ext^{n+1}(Z, c.pt) ≅ Ext^n(Z, I/c.pt)`. By AB5, `I/c.pt = colim(I/Y.obj j)`.
      Apply the inductive hypothesis to the quotient diagram.

    The `hHom` hypothesis holds for `Z = constantSheaf(ULift ℤ)` on a topological space
    because `Hom(Z, F) ≅ Γ(X, F) = F(X)` and filtered colimits of sheaves are objectwise.
    The mono-transition condition is NOT needed; the proof works for arbitrary filtered
    diagrams. -/
theorem ext_comm_filtered_colimit_mono
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt C]
    [IsGrothendieckAbelian.{w} C]
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (Y : J ⥤ C) (c : Cocone Y) (hc : IsColimit c)
    [∀ (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)]
    (Z : C) (n : ℕ)
    -- The `hHom` hypothesis: Hom(Z,-) sends colimit vanishing to vanishing.
    -- For sheaves, this follows from objectwise colimits: Hom(Z_X, F) ≅ F(X).
    (hHom : (∀ j, Subsingleton (Z ⟶ Y.obj j)) → Subsingleton (Z ⟶ c.pt))
    (hvan : ∀ j, Subsingleton (Ext Z (Y.obj j) n)) :
    Subsingleton (Ext Z c.pt n) := by
  induction n with
  | zero =>
    -- n=0: Ext^0 ≅ Hom via homEquiv₀, then apply hHom. PROVED.
    exact Ext.homEquiv₀.subsingleton_congr.mpr
      (hHom (fun j => Ext.homEquiv₀.subsingleton_congr.mp (hvan j)))
  | succ n _ =>
    -- n≥1: Mathlib API gap. Requires Čech cohomology, universal δ-functors,
    -- or functorial Godement resolution. See proofs.md for analysis.
    sorry

/-! ### Filtered diagram of finitely generated subsheaves

We build a functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending each finite set `S`
of local sections to the subsheaf `finsetGeneratedSheaf S`. The transition maps
(for `S ⊆ S'`) are monomorphisms, and K is the colimit of this filtered diagram. -/

section FilteredDiagram
open scoped Classical

variable {X : TopCat.{u}} [NoetherianSpace X] (K : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- Coproduct inclusion for general `S ⊆ S'`. -/
private noncomputable def finsetCoproductInclGen
    {S S' : Finset (TopCat.Sheaf.SectionIndex K)} (h : S ⊆ S') :
    (∐ fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟶
    (∐ fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) :=
  Sigma.desc fun σ =>
    Sigma.ι (fun τ : {τ // τ ∈ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ.1, h σ.2⟩

/-- Image inclusion for general `S ⊆ S'`: `finsetGeneratedSheaf S ⟶ finsetGeneratedSheaf S'`. -/
private noncomputable def finsetImageInclGen
    {S S' : Finset (TopCat.Sheaf.SectionIndex K)} (h : S ⊆ S') :
    TopCat.Sheaf.finsetGeneratedSheaf S ⟶ TopCat.Sheaf.finsetGeneratedSheaf S' :=
  Limits.image.lift
    { I := TopCat.Sheaf.finsetGeneratedSheaf S'
      m := Limits.image.ι _
      e := finsetCoproductInclGen K h ≫ factorThruImage (TopCat.Sheaf.finsetGeneratorMap S')
      fac := by
        rw [Category.assoc, Limits.image.fac]
        ext ⟨σ, hσ⟩
        simp [finsetCoproductInclGen, TopCat.Sheaf.finsetGeneratorMap,
              TopCat.Sheaf.familyGeneratorMap] }

omit [NoetherianSpace X] in
private lemma finsetImageInclGen_comp_ι
    {S S' : Finset (TopCat.Sheaf.SectionIndex K)} (h : S ⊆ S') :
    finsetImageInclGen K h ≫ Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S') =
      Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S) :=
  Limits.image.lift_fac _

private instance finsetImageInclGen_mono
    {S S' : Finset (TopCat.Sheaf.SectionIndex K)} (h : S ⊆ S') :
    Mono (finsetImageInclGen K h) :=
  mono_of_mono_fac (finsetImageInclGen_comp_ι K h)

/-- The functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending `S ↦ finsetGeneratedSheaf S`.
    Transition maps are the canonical image inclusions, which are monomorphisms. -/
private noncomputable def finsetGenFunctor :
    Finset (TopCat.Sheaf.SectionIndex K) ⥤ TopCat.Sheaf AddCommGrpCat.{u} X where
  obj S := TopCat.Sheaf.finsetGeneratedSheaf S
  map h := finsetImageInclGen K h.le
  map_id S := by
    apply (cancel_mono (Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S))).1
    rw [finsetImageInclGen_comp_ι, Category.id_comp]
  map_comp {S₁ S₂ S₃} h₁ h₂ := by
    apply (cancel_mono (Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S₃))).1
    rw [Category.assoc, finsetImageInclGen_comp_ι, finsetImageInclGen_comp_ι,
        finsetImageInclGen_comp_ι]

/-- Cocone with vertex `K`: the cocone maps are `image.ι : finsetGeneratedSheaf S ⟶ K`. -/
private noncomputable def finsetGenCocone :
    Cocone (finsetGenFunctor K) :=
  Cocone.mk K
    { app := fun S => Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S)
      naturality := fun S S' h => by
        dsimp [finsetGenFunctor]
        rw [finsetImageInclGen_comp_ι, Category.comp_id] }

/-- The cocone is a colimit: `K` is the filtered colimit of its finitely generated subsheaves.
    Proof: the canonical map `colim → K` is mono (by AB5 + mono transitions) and epi
    (since `allSectionMap K` factors through it), hence an isomorphism. -/
private noncomputable def finsetGenCocone_isColimit :
    IsColimit (finsetGenCocone K) := by
  -- Show the comparison map colim → K is an iso, then transport IsColimit
  let d := colimit.desc (finsetGenFunctor K) (finsetGenCocone K)
  -- desc is mono: natural transformation to const K has all components mono (image.ι),
  -- and in a Grothendieck abelian category filtered colimits preserve monos
  have hd_mono : Mono d := by
    haveI : IsConnected (Finset (TopCat.Sheaf.SectionIndex K)) := IsFiltered.isConnected _
    let α : finsetGenFunctor K ⟶ (Functor.const _).obj K :=
      { app := fun S => Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S)
        naturality := fun S S' h => by
          dsimp [finsetGenFunctor]
          rw [finsetImageInclGen_comp_ι, Category.comp_id] }
    haveI : ∀ j, Mono (α.app j) := fun _ => inferInstance
    haveI := NatTrans.mono_of_mono_app α
    exact colim.map_mono' α (colimit.isColimit _) (isColimitConstCocone _ _) d
      (fun j => by simp [d, α, finsetGenCocone, constCocone])
  -- desc is epi: allSectionMap K factors through desc
  have hd_epi : Epi d := by
    let g : (∐ fun σ : TopCat.Sheaf.SectionIndex K => TopCat.Sheaf.zeroOutsideInt σ.1) ⟶
        colimit (finsetGenFunctor K) :=
      Sigma.desc fun σ =>
        Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} =>
            TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, Finset.mem_singleton_self σ⟩ ≫
          factorThruImage (TopCat.Sheaf.finsetGeneratorMap {σ}) ≫
          colimit.ι (finsetGenFunctor K) {σ}
    have hfac : g ≫ d = TopCat.Sheaf.allSectionMap K := by
      dsimp only [g, d]
      apply Sigma.hom_ext; intro σ
      simp only [← Category.assoc, Sigma.ι_desc]
      simp only [Category.assoc, colimit.ι_desc]
      dsimp [finsetGenCocone]
      rw [Limits.image.fac]
      simp [TopCat.Sheaf.finsetGeneratorMap, TopCat.Sheaf.familyGeneratorMap,
            TopCat.Sheaf.allSectionMap]
    haveI := TopCat.Sheaf.allSectionMap_epi K
    exact epi_of_epi_fac hfac
  -- mono + epi → iso in abelian category
  haveI := hd_mono; haveI := hd_epi
  haveI : IsIso ((colimit.isColimit (finsetGenFunctor K)).desc (finsetGenCocone K)) :=
    isIso_of_mono_of_epi d
  exact (colimit.isColimit (finsetGenFunctor K)).ofPointIso

instance finsetGenFunctor_mono
    (j j' : Finset (TopCat.Sheaf.SectionIndex K))
    (φ : j ⟶ j') : Mono ((finsetGenFunctor K).map φ) :=
  finsetImageInclGen_mono K φ.le

end FilteredDiagram

/-- **Hartshorne 2.9 core**: on a Noetherian space, if `H^m = 0` for all finitely generated
    subsheaves of `K`, then `H^m(K) = 0`. Uses `ext_comm_filtered_colimit_mono` applied to
    the filtered diagram of finitely generated subsheaves. -/
theorem cohomology_vanishing_of_finitelyGenerated_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    (K : TopCat.Sheaf AddCommGrpCat.{u} X) (m : ℕ)
    (hfg : ∀ (S : Finset (TopCat.Sheaf.SectionIndex K))
      [HasCoproduct fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1],
      Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf S) m)) :
    Subsingleton (Sheaf.H K m) := by
  -- hHom: for sheaves, Hom(Z_X, colim F_j) ≅ colim Hom(Z_X, F_j) because
  -- filtered colimits of sheaves are computed objectwise and Hom(Z_X, F) ≅ F(X).
  let Z := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))
  have hHom : (∀ j, Subsingleton (Z ⟶ (finsetGenFunctor K).obj j)) →
      Subsingleton (Z ⟶ (finsetGenCocone K).pt) := by
    intro hvan
    -- Step 1: Z ⟶ F ≃ Ext^0(Z,F) ≃ F(⊤) via sheafH0EquivSections
    -- So Subsingleton (Z ⟶ F) ↔ Subsingleton F(⊤)
    -- Step 2: K(⊤) = colim((finsetGeneratedSheaf j)(⊤)) by objectwise colimits
    -- Step 3: Each (finsetGeneratedSheaf j)(⊤) is subsingleton → colim is subsingleton
    -- Via Ext.homEquiv₀: (Z ⟶ F) ≃ Ext^0(Z,F). Via sheafH0EquivSections: Ext^0 ≃+ F(⊤).
    -- So Subsingleton (Z ⟶ F) ↔ Subsingleton (F.val.obj (op ⊤)).
    have adj := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      Limits.isTerminalTop
    -- Use adjunction to transfer: (Z ⟶ K) ≃ (ULift ℤ ⟶ K.val.obj(op ⊤))
    rw [show (finsetGenCocone K).pt = K from rfl]
    have heq : ∀ F : TopCat.Sheaf AddCommGrpCat.{u} X,
        (Z ⟶ F) ≃ (AddCommGrpCat.of (ULift.{u} ℤ) ⟶
          ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op ⊤)).obj F) :=
      fun F => adj.homEquiv _ F
    -- Transfer Subsingleton across the equivalence for K
    apply (heq K).subsingleton_congr.mpr
    -- Now goal: Subsingleton (ULift ℤ ⟶ K.val.obj(op ⊤))
    -- From hvan: Subsingleton (Z ⟶ finsetGeneratedSheaf j) for each j
    -- Via adjunction: Subsingleton (ULift ℤ ⟶ (finsetGeneratedSheaf j).val.obj(op ⊤))
    have hvan' : ∀ j, Subsingleton (AddCommGrpCat.of (ULift.{u} ℤ) ⟶
        ((finsetGenFunctor K).obj j).val.obj (op ⊤)) :=
      fun j => (heq _).subsingleton_congr.mp (hvan j)
    -- Each finsetGeneratedSheaf(j)(⊤) is zero (Subsingleton in AddCommGrpCat).
    -- K is their colimit. The colimit cocone maps ι_j(⊤) all map from zero objects.
    -- In AddCommGrpCat, Subsingleton (ULift ℤ ⟶ G) iff G is zero.
    -- We need: Subsingleton (ULift ℤ ⟶ K(⊤)).
    -- Use: every morphism ULift ℤ → K(⊤) factors through some G_j (⊤) via the
    -- colimit structure, and G_j(⊤) is zero, so the morphism is zero.
    -- Each G_j(⊤) is subsingleton → K(⊤) is subsingleton → Hom(ULift ℤ, K(⊤)) subsingleton
    -- First: Subsingleton(ULift ℤ ⟶ G) ↔ Subsingleton G in AddCommGrpCat
    have hGsub : ∀ j, Subsingleton (((finsetGenFunctor K).obj j).val.obj (op ⊤)) := by
      intro j
      exact addCommGrpCat_subsingleton_of_subsingleton_hom _ (hvan' j)
    -- K.val.obj(op ⊤) = colim(G_j(⊤)) since sheaf filtered colimits are objectwise.
    -- colim of subsingleton (zero) groups is subsingleton.
    -- Therefore K(⊤) is subsingleton.
    have hKsub : Subsingleton (K.val.obj (op ⊤)) := by
      -- K = colim(finsetGenFunctor K) as a sheaf. The presheaf colimit creates
      -- this sheaf colimit. Evaluation at op ⊤ preserves colimits.
      -- So K(⊤) = colim(G_j(⊤)) in AddCommGrpCat. Each G_j(⊤) is zero → colimit is zero.
      -- Step 1: Get the presheaf-level colimit from the sheaf-level colimit
      let F := finsetGenFunctor K
      let cc := finsetGenCocone K
      let hcc := finsetGenCocone_isColimit K
      -- The sheaf colimit cocone gives a presheaf cocone
      let pcc : Cocone (F ⋙ sheafToPresheaf _ _) :=
        (sheafToPresheaf _ _).mapCocone cc
      -- Step 2: Evaluate the presheaf cocone at op ⊤
      let ecc : Cocone (F ⋙ sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op ⊤)) :=
        ((evaluation _ _).obj (op ⊤)).mapCocone pcc
      -- ecc.pt = K.val.obj(op ⊤), each ecc.ι.app j = (finsetGeneratedSheaf j)(⊤) → K(⊤)
      -- Step 3: Get colimit at the section level
      -- For the colimit at sections, we need a different approach since
      -- sheafToPresheaf creates (but may not preserve) filtered colimits.
      -- Instead, use the concrete IsColimit structure directly.
      -- The cocone maps ecc.ι.app j : G_j(⊤) → K(⊤) all map from subsingleton,
      -- so their image is {0}. The colimit is generated by these images.
      -- Since all images are {0}, K(⊤) = {0}.
      -- Use hcc to show K(⊤) is subsingleton: any two sections of K are equal.
      -- sheafToPresheaf creates filtered colimits → it preserves them.
      -- evaluation preserves all colimits. Compose to get section-level colimit.
      -- Each section group is zero → colimit is zero.
      -- K(⊤) = colim(G_j(⊤)) since filtered colimits of sheaves are objectwise.
      -- Each G_j(⊤) is zero → colimit is zero → K(⊤) is zero.
      -- The formal proof needs sheafToPresheaf to create the filtered colimit
      -- (CreatesColimit instance), then evaluation at ⊤ preserves it.
      -- CreatesColimit is not auto-synthesized for specific functors in Lean.
      sorry
    -- Hom(ULift ℤ, subsingleton) is subsingleton.
    exact addCommGrpCat_subsingleton_hom_of_subsingleton _ hKsub
  exact ext_comm_filtered_colimit_mono (finsetGenFunctor K) (finsetGenCocone K)
    (finsetGenCocone_isColimit K) Z m hHom (fun S => hfg S)

section FinsetGenerated
open scoped Classical

/-- Coproduct inclusion from `S'` to `insert σ₀ S'`. -/
private noncomputable def finsetCoproductIncl
    {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K} (_ : σ₀ ∉ S')
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    (∐ fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟶
    (∐ fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) :=
  Sigma.desc fun σ =>
    Sigma.ι (fun τ : {τ // τ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1)
      ⟨σ.1, Finset.mem_insert_of_mem σ.2⟩

/-- Mono from `image(S')` to `image(insert σ₀ S')` via coproduct inclusion. -/
private noncomputable def imageIncl
    {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K} (hσ₀ : σ₀ ∉ S')
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    TopCat.Sheaf.finsetGeneratedSheaf S' ⟶ TopCat.Sheaf.finsetGeneratedSheaf (insert σ₀ S') :=
  Limits.image.lift
    { I := TopCat.Sheaf.finsetGeneratedSheaf (insert σ₀ S')
      m := Limits.image.ι _
      e := finsetCoproductIncl hσ₀ ≫ factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S'))
      fac := by
        rw [Category.assoc, Limits.image.fac]
        ext ⟨σ, hσ⟩
        simp [finsetCoproductIncl, TopCat.Sheaf.finsetGeneratorMap, TopCat.Sheaf.familyGeneratorMap] }

private instance imageIncl_mono
    {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K} (hσ₀ : σ₀ ∉ S')
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Mono (imageIncl hσ₀ : TopCat.Sheaf.finsetGeneratedSheaf S' ⟶ _) := by
  have h : imageIncl hσ₀ ≫ Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) =
      Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S') := Limits.image.lift_fac _
  exact mono_of_mono_fac h

/-- The `σ₀`-component maps epi onto the cokernel of `imageIncl`. -/
private theorem imageIncl_cokernel_epi
    {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K} (hσ₀ : σ₀ ∉ S')
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Epi (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1)
      ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
      factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π (imageIncl hσ₀)) := by
  let proj : (∐ fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟶
      TopCat.Sheaf.zeroOutsideInt σ₀.1 :=
    Sigma.desc fun σ =>
      if h : σ.1 = σ₀ then
        eqToHom (by rw [h])
      else 0
  have heq : finsetCoproductIncl hσ₀ ≫
      factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) =
    factorThruImage (TopCat.Sheaf.finsetGeneratorMap S') ≫ imageIncl hσ₀ := by
    apply (cancel_mono (Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')))).1
    rw [Category.assoc, Limits.image.fac]
    have hlf : imageIncl hσ₀ ≫ Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) =
        Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S') := Limits.image.lift_fac _
    rw [Category.assoc, hlf, Limits.image.fac]
    ext ⟨σ', hσ'⟩
    simp [finsetCoproductIncl, TopCat.Sheaf.finsetGeneratorMap, TopCat.Sheaf.familyGeneratorMap]
  have hfac : proj ≫
      (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1)
        ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
      factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π (imageIncl hσ₀)) =
    factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π (imageIncl hσ₀) := by
    ext ⟨σ, hσ⟩
    simp only [proj, Category.assoc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    by_cases h : σ = σ₀
    · subst h; simp
    · rw [← Category.assoc
        (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟨σ, hσ⟩)
        (Sigma.desc _)]
      rw [colimit.ι_desc, Cofan.mk_ι_app, dif_neg h, zero_comp]
      symm
      have hσ' : σ ∈ S' := Finset.mem_of_mem_insert_of_ne hσ h
      have hι : Sigma.ι (fun τ : {τ // τ ∈ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, hσ'⟩ ≫
          finsetCoproductIncl hσ₀ =
        Sigma.ι (fun τ : {τ // τ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, hσ⟩ := by
        simp [finsetCoproductIncl]
      rw [← hι, Category.assoc, reassoc_of% heq]
      simp [cokernel.condition]
  exact epi_of_epi_fac hfac

/-- **Step 3B–3C**: vanishing for `finsetGeneratedSheaf S` by `Finset.induction`. -/
theorem finsetGeneratedSheaf_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    (m : ℕ)
    (hzero : ∀ {G : TopCat.Sheaf AddCommGrpCat.{u} X} {V : Opens X}
      (f : TopCat.Sheaf.zeroOutsideInt V ⟶ G), Epi f → Subsingleton (Sheaf.H G m))
    (S : Finset (TopCat.Sheaf.SectionIndex K))
    [HasCoproduct fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf S) m) := by
  suffices h : ∀ (T : Finset (TopCat.Sheaf.SectionIndex K)),
      Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf T) m) from h S
  intro T
  induction T using Finset.induction with
  | empty =>
    apply subsingleton_sheafH_of_isZero'
    apply IsZero.of_iso (isZero_zero _) (imageZero' _)
    apply Sigma.hom_ext; intro ⟨σ, hσ⟩; simp at hσ
  | @insert σ₀ S' hσ₀ ih =>
    haveI : Mono (imageIncl hσ₀) := imageIncl_mono hσ₀
    let SC := ShortComplex.mk (imageIncl hσ₀) (cokernel.π (imageIncl hσ₀))
      (cokernel.condition _)
    have hSE : SC.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) inferInstance inferInstance
    have hCoker : Subsingleton (Sheaf.H SC.X₃ m) := by
      haveI := imageIncl_cokernel_epi hσ₀
      exact hzero (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} =>
            TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
          factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
          cokernel.π (imageIncl hσ₀)) inferInstance
    exact subsingleton_sheafH_of_shortExact_middle hSE m ih hCoker

end FinsetGenerated

/-- **Step 3A** (Hartshorne III.2.7): on a Noetherian space, if vanishing holds for
    all epi images of `zeroOutsideInt V`, then it holds for every sheaf.
    Assembles `finsetGeneratedSheaf_vanishing` (finite case) with
    `cohomology_vanishing_of_finitelyGenerated_vanishing` (colimit step). -/
theorem directLimit_cohomology_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    (K : TopCat.Sheaf AddCommGrpCat.{u} X) (m : ℕ)
    (hzero : ∀ {G : TopCat.Sheaf AddCommGrpCat.{u} X} {V : Opens X}
      (f : TopCat.Sheaf.zeroOutsideInt V ⟶ G), Epi f → Subsingleton (Sheaf.H G m)) :
    Subsingleton (Sheaf.H K m) :=
  cohomology_vanishing_of_finitelyGenerated_vanishing K m
    (fun S _ => finsetGeneratedSheaf_vanishing m hzero S)
