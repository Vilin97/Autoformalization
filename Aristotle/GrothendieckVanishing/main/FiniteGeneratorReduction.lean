/-
  FiniteGeneratorReduction.lean — Colimit step and finitely generated vanishing

  Key results (presheaf colimit theory split to PresheafFilteredColimit.lean):
  - sheafH_filtered_colimit_aux / sheafH_preserves_filtered_colimits: vanishing propagation
    for filtered colimits (FULLY PROVED).
  - sheafH_filtered_colimit_surj: surjectivity of colim H^n(F_j) → H^n(colim F_j) (FULLY PROVED).
    Uses extClass_naturality (in SetupCore.lean) for the connecting map commutation.
  - finsetGenFunctor / finsetGenCocone / finsetGenCocone_isColimit: K is the filtered
    colimit of its finitely generated subsheaves (PROVED)
  - cohomology_vanishing_of_finitelyGenerated_vanishing: H^m = 0 for all f.g. subsheaves
    implies H^m(K) = 0 (PROVED via sheafH_preserves_filtered_colimits)
  - finsetGeneratedSheaf_vanishing: vanishing for finitely generated sheaves by
    Finset.induction (PROVED)
  - directLimit_cohomology_vanishing: from epi-image vanishing to all sheaves (PROVED)
-/
import Aristotle.GrothendieckVanishing.main.PresheafFilteredColimit
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.ZeroOutsideFinset

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-! ### Filtered colimits of flasque sheaves

On a Noetherian topological space, filtered colimits of flasque sheaves are flasque.
This is because `sheafToPresheaf` creates filtered colimits (presheaf colimits of sheaves
are already sheaves on Noetherian spaces), so restrictions of the colimit are colimits of
per-piece restrictions. Filtered colimits in `AddCommGrpCat` preserve surjections, and
flasque means all restrictions are surjective.

This replaces Gabriel's theorem (filtered colimits of injectives are injective) for our
purposes: we only need `H^n(colim I_j) = 0` for injective `I_j`, and `flasqueVanishing`
gives this since injective sheaves are flasque (`isFlasque_of_injective`). -/

/-- Filtered colimits of flasque sheaves on Noetherian spaces are flasque. -/
lemma isFlasque_filtered_colimit
    {X : TopCat.{u}} [NoetherianSpace X]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (hFlasque : ∀ j, IsFlasqueSheaf (F.obj j))
    {c : Cocone F} (hc : IsColimit c) :
    IsFlasqueSheaf c.pt := by
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro b; haveI := createsFilteredColimit F
  have hc_psh := isColimitOfPreserves (sheafToPresheaf _ _) hc
  have hc_U := isColimitOfPreserves
    ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) hc_psh
  obtain ⟨j₀, b₀, hb₀⟩ := Concrete.isColimit_exists_rep _ hc_U b
  obtain ⟨a₀, ha₀⟩ := (AddCommGrpCat.epi_iff_surjective _).mp (hFlasque j₀ i) b₀
  refine ⟨ConcreteCategory.hom ((c.ι.app j₀).val.app (op V)) a₀, ?_⟩
  rw [show ConcreteCategory.hom (c.pt.val.map i.op)
      (ConcreteCategory.hom ((c.ι.app j₀).val.app (op V)) a₀) =
    ConcreteCategory.hom ((c.ι.app j₀).val.app (op U))
      (ConcreteCategory.hom ((F.obj j₀).val.map i.op) a₀) from
    congrFun (congrArg DFunLike.coe
      (congrArg ConcreteCategory.hom ((c.ι.app j₀).val.naturality i.op).symm)) a₀,
    ha₀]; exact hb₀

/-! ### Filtered diagram of finitely generated subsheaves

We build a functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending each finite set `S`
of local sections to the subsheaf `finsetGeneratedSheaf S`. The transition maps
(for `S ⊆ S'`) are monomorphisms, and K is the colimit of this filtered diagram. -/

section FilteredDiagram
open scoped Classical

variable {X : TopCat.{u}} [NoetherianSpace X] (K : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- Coproduct inclusion for `S ⊆ S'`: maps the coproduct indexed by `S` into that indexed by `S'`. -/
noncomputable def finsetCoproductInclGen
    {S S' : Finset (TopCat.Sheaf.SectionIndex K)} (h : S ⊆ S') :
    (∐ fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟶
    (∐ fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) :=
  Sigma.desc fun σ =>
    Sigma.ι (fun τ : {τ // τ ∈ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ.1, h σ.2⟩

/-- Image inclusion for general `S ⊆ S'`: `finsetGeneratedSheaf S ⟶ finsetGeneratedSheaf S'`. -/
noncomputable def finsetImageInclGen
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
/-- The image inclusion composed with `image.ι` equals the original `image.ι`. -/
lemma finsetImageInclGen_comp_ι
    {S S' : Finset (TopCat.Sheaf.SectionIndex K)} (h : S ⊆ S') :
    finsetImageInclGen K h ≫ Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S') =
      Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S) :=
  Limits.image.lift_fac _

/-- The image inclusion for `S ⊆ S'` is a monomorphism. -/
instance finsetImageInclGen_mono
    {S S' : Finset (TopCat.Sheaf.SectionIndex K)} (h : S ⊆ S') :
    Mono (finsetImageInclGen K h) :=
  mono_of_mono_fac (finsetImageInclGen_comp_ι K h)

/-- The functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending `S ↦ finsetGeneratedSheaf S`.
    Transition maps are the canonical image inclusions, which are monomorphisms. -/
noncomputable def finsetGenFunctor :
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
noncomputable def finsetGenCocone :
    Cocone (finsetGenFunctor K) :=
  Cocone.mk K
    { app := fun S => Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S)
      naturality := fun S S' h => by
        simp [finsetGenFunctor, finsetImageInclGen_comp_ι] }

/-- The cocone is a colimit: `K` is the filtered colimit of its finitely generated subsheaves.
    Proof: the canonical map `colim → K` is mono (by AB5 + mono transitions) and epi
    (since `allSectionMap K` factors through it), hence an isomorphism. -/
noncomputable def finsetGenCocone_isColimit :
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
          simp [finsetGenFunctor, finsetImageInclGen_comp_ι] }
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
      dsimp only [g, d]; apply Sigma.hom_ext; intro σ
      simp [← Category.assoc, Sigma.ι_desc, Category.assoc, colimit.ι_desc,
        finsetGenCocone, Limits.image.fac, TopCat.Sheaf.finsetGeneratorMap,
        TopCat.Sheaf.familyGeneratorMap]
    haveI := TopCat.Sheaf.allSectionMap_epi K
    exact epi_of_epi_fac hfac
  -- mono + epi → iso in abelian category
  haveI := hd_mono; haveI := hd_epi
  haveI : IsIso ((colimit.isColimit (finsetGenFunctor K)).desc (finsetGenCocone K)) :=
    isIso_of_mono_of_epi d
  exact (colimit.isColimit (finsetGenFunctor K)).ofPointIso

end FilteredDiagram

/-! ### Sheaf cohomology commutes with filtered colimits

The main result `sheafH_preserves_filtered_colimits` proves that on a Noetherian
space, if `H^n(F_j) = 0` for all pieces of a filtered diagram, then `H^n(colim F_j) = 0`.

The proof uses per-object functorial injective embeddings via Mathlib's
`IsGrothendieckAbelian.instHasFunctorialFactorizationMonomorphismsRlp`. For each `j`,
the zero morphism `0 : Y'.obj j → 0` is factored as a monomorphism followed by a
morphism with the RLP w.r.t. monomorphisms, giving `Y'.obj j ↪ I_j` with `I_j` injective.
This is functorial in `j`, yielding a functor `Inj : J' ⥤ Sheaf` and a mono natural
transformation `η : Y' ⟶ Inj`. The filtered colimit `colim(Inj)` is flasque
(by `isFlasque_filtered_colimit`, since injective ⟹ flasque), and the induced map
`c'.pt → colim(Inj)` is mono by AB5.

This approach avoids requiring mono transitions in the diagram (the previous approach
embedded into a single injective and needed mono coprojections, which is false at
recursive IH levels). -/

/-- Auxiliary: sheaf cohomology vanishing commutes with filtered colimits on Noetherian
    spaces. Proof by induction on `n` with dimension shifting via per-object functorial
    injective embeddings. FULLY PROVED (flasque vanishing replaces Gabriel's theorem). -/
theorem sheafH_filtered_colimit_aux
    {X : TopCat.{u}} [NoetherianSpace X] (n : ℕ) :
    ∀ {J' : Type u} [SmallCategory J'] [IsFiltered J']
      (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
      (c' : Cocone Y') (_ : IsColimit c')
      (_ : ∀ j, Subsingleton (Sheaf.H (Y'.obj j) n)),
    Subsingleton (Sheaf.H c'.pt n) := by
  induction n with
  | zero =>
    -- Base case: H^0 = Ext^0 ≅ Hom ≅ global sections.
    -- On Noetherian spaces, sheafToPresheaf creates filtered colimits (via
    -- isSheaf_presheaf_filtered_colimit), so global sections commute with
    -- filtered colimits. If each piece has trivial global sections, so does the colimit.
    intro J' inst1 inst2 Y' c' hc' hvan
    letI := inst1; letI := inst2
    -- H^0 ≅ global sections, colimit of trivial sections is trivial
    haveI := createsFilteredColimit Y'
    have hc_psh := isColimitOfPreserves (sheafToPresheaf _ _) hc'
    have hc_top := isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh
    have h_sec : ∀ j, Subsingleton ((Y'.obj j).val.obj (op ⊤)) := fun j => by
      haveI := hvan j; exact subsingleton_of_addEquiv (sheafH0EquivSections (Y'.obj j))
    have : Subsingleton (c'.pt.val.obj (op ⊤)) := by
      constructor; intro a b
      obtain ⟨j₁, x, hx⟩ := Concrete.isColimit_exists_rep _ hc_top a
      obtain ⟨j₂, y, hy⟩ := Concrete.isColimit_exists_rep _ hc_top b
      rw [← hx, ← hy, @Subsingleton.elim _ (h_sec j₁) x 0,
          @Subsingleton.elim _ (h_sec j₂) y 0, map_zero, map_zero]
    exact subsingleton_of_addEquiv (sheafH0EquivSections c'.pt).symm
  | succ n ih =>
    -- Inductive step: dimension shifting via per-object functorial injective embedding.
    -- Key idea: instead of embedding colim(Y') into a single injective (which needs mono
    -- coprojections), embed each Y'.obj j into its own injective I_j via functorial
    -- factorization. This gives mono η.app j : Y'.obj j → I_j for free, avoiding the
    -- need for mono transitions in the diagram.
    intro J' inst1 inst2 Y' c' hc' hvan
    letI := inst1; letI := inst2
    -- Zero instance for sheaves (needed for `(0 : X ⟶ 0)` syntax in Arrow.mk)
    letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) :=
      Limits.HasZeroObject.zero' _
    -- Arrow functor: j ↦ Arrow.mk (0 : Y'.obj j ⟶ 0)
    let toArrow : J' ⥤ Arrow (TopCat.Sheaf AddCommGrpCat.{u} X) :=
      { obj := fun j => Arrow.mk (0 : Y'.obj j ⟶ 0)
        map := fun f => Arrow.homMk (Y'.map f) (𝟙 0) (by simp)
        map_id := fun j => by ext <;> simp
        map_comp := fun f g => by ext <;> simp }
    -- Functorial factorization data
    let ffData := MorphismProperty.functorialFactorizationData
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
    -- Injective functor: Inj.obj j = ffData.Z(Arrow.mk(0 : Y'.obj j → 0))
    let Inj : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X := toArrow ⋙ ffData.Z
    -- Per-object mono embedding η : Y' ⟶ Inj (naturality from ffData.i)
    let η : Y' ⟶ Inj :=
      { app := fun j => ffData.i.app (toArrow.obj j)
        naturality := fun _ _ f => ffData.i.naturality (toArrow.map f) }
    -- Each η.app j is mono (from the functorial factorization)
    have hη_mono : ∀ j, Mono (η.app j) := fun j => ffData.hi (toArrow.obj j)
    -- Each Inj.obj j is injective (factorization of zero morphism)
    -- Proof: monoMapFactorizationDataRlp(0 : X → 0).Z is injective by Mathlib instance
    haveI hInj : ∀ j, Injective (Inj.obj j) := fun j => by
      change Injective (ffData.Z.obj (Arrow.mk (0 : Y'.obj j ⟶ 0)))
      exact IsGrothendieckAbelian.instInjectiveZMonomorphismsRlpMonoMapFactorizationDataRlpOfNatHom
    -- Build cocone c'.pt → colim(Inj) via η and c'
    -- The cocone maps are: η.app j ≫ colimit.ι Inj j
    let injCocone : Cocone Inj := colimit.cocone Inj
    let ι'Cocone : Cocone Y' := Cocone.mk injCocone.pt
      { app := fun j => η.app j ≫ injCocone.ι.app j
        naturality := fun j j' f => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
            ← injCocone.w f, ← Category.assoc, η.naturality f] }
    -- ι' : c'.pt → colim(Inj) is the desc of ι'Cocone
    let ι' : c'.pt ⟶ injCocone.pt := hc'.desc ι'Cocone
    -- ι' is mono: η is mono nat trans, and filtered colimits preserve monos (AB5)
    haveI : Mono ι' := by
      haveI : ∀ j, Mono (η.app j) := hη_mono
      haveI := NatTrans.mono_of_mono_app η
      exact colim.map_mono' η hc' (colimit.isColimit Inj) ι' (fun j =>
        hc'.fac ι'Cocone j)
    let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
      ShortComplex.mk ι' (cokernel.π ι') (cokernel.condition ι')
    have hSE : S.ShortExact := shortExact_of_mono ι'
    -- H^{n+1}(colim Inj) = 0 since colim Inj is flasque
    have hI := flasqueVanishing X injCocone.pt
      (isFlasque_filtered_colimit Inj (fun j => isFlasque_of_injective _)
        (colimit.isColimit Inj)) n
    -- Build per-object quotient functor Q.obj j = cokernel(η.app j)
    -- η.app j is ALWAYS mono by ffData.hi, so no hmono needed!
    let Q : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
      { obj := fun j => cokernel (η.app j)
        map := fun {j j'} f => cokernel.map _ _ (Y'.map f) (Inj.map f) (η.naturality f).symm
        map_id := fun j => by ext; simp [cokernel.map]
        map_comp := fun {j j' j''} f g => by ext; simp [cokernel.map, Functor.map_comp] }
    -- Factoring lemma: c'.ι.app j ≫ ι' = η.app j ≫ injCocone.ι.app j
    have hfac_ι : ∀ j, c'.ι.app j ≫ ι' = η.app j ≫ injCocone.ι.app j := hc'.fac ι'Cocone
    -- Cocone on Q with vertex S.X₃ = cokernel(ι')
    -- Map: cokernel(η.app j) → cokernel(ι') via the commutative square
    --   Y'.obj j --c'.ι.app j-→ c'.pt
    --      |                       |
    --   η.app j                   ι'
    --      |                       |
    --   Inj.obj j --ι_j--------→ colim Inj
    let qCocone : Cocone Q := Cocone.mk S.X₃
      { app := fun j => cokernel.map (η.app j) ι' (c'.ι.app j) (injCocone.ι.app j)
            (hfac_ι j).symm
        naturality := fun j j' f => by
          ext; show cokernel.π _ ≫ Q.map f ≫ _ = cokernel.π _ ≫ _ ≫ _
          rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc]
          simp [cokernel.π_desc, Functor.const_obj_map] }
    -- IsColimit: qCocone is a colimit.
    -- Strategy: lift a cocone s on Q to a cocone on Inj, use colimit of Inj to descend.
    have hqColim : IsColimit qCocone := by
      haveI : Nonempty J' := IsFiltered.nonempty
      -- cokernel.π(η.app j) ≫ qCocone.ι.app j = injCocone.ι.app j ≫ cokernel.π(ι')
      have hπC : ∀ j, cokernel.π (η.app j) ≫ qCocone.ι.app j =
          injCocone.ι.app j ≫ cokernel.π ι' := fun j => cokernel.π_desc _ _ _
      -- For a cocone s on Q, the maps Inj.obj j →[cokernel.π ≫ s.ι] s.pt form a cocone on Inj
      -- cokernel.π(η.app j) ≫ Q.map a = Inj.map a ≫ cokernel.π(η.app j')
      have hπQ : ∀ {j₁ j₂ : J'} (a : j₁ ⟶ j₂),
          cokernel.π (η.app j₁) ≫ Q.map a =
          Inj.map a ≫ cokernel.π (η.app j₂) := fun a => cokernel.π_desc _ _ _
      let liftCocone : ∀ (s : Cocone Q), Cocone Inj := fun s =>
        Cocone.mk s.pt
          { app := fun j => cokernel.π (η.app j) ≫ s.ι.app j
            naturality := fun j j' a => by
              dsimp; rw [Category.comp_id, ← Category.assoc, ← hπQ a, Category.assoc, s.w] }
      -- Use injCocone as colimit of Inj to get d : injCocone.pt → s.pt
      let injColim := colimit.isColimit Inj
      -- desc: cokernel(ι') → s.pt
      -- Factor through: injCocone.pt →[d] s.pt where d = injColim.desc(liftCocone s)
      -- Then cokernel.desc ι' d (condition)
      exact
      { desc := fun s => cokernel.desc ι' (injColim.desc (liftCocone s)) (by
          apply hc'.hom_ext; intro j
          rw [comp_zero]; conv_lhs => rw [← Category.assoc, hfac_ι j, Category.assoc]
          rw [injColim.fac, ← Category.assoc, cokernel.condition, zero_comp])
        fac := fun s j => by
          apply (cancel_epi (cokernel.π (η.app j))).mp
          rw [← Category.assoc, hπC, Category.assoc, cokernel.π_desc, injColim.fac]
        uniq := fun s m hm => by
          apply (cancel_epi (cokernel.π ι')).mp
          rw [cokernel.π_desc]
          apply injColim.hom_ext; intro j
          rw [injColim.fac]
          show injCocone.ι.app j ≫ cokernel.π ι' ≫ m = _
          rw [← Category.assoc, ← hπC j, Category.assoc, hm] }
    -- Split on n: n=0 needs direct H^1 argument, n≥1 uses dimension shift
    match n with
    | 0 =>
      -- Direct proof of H^1(c'.pt) = 0 using the LES + Ext^0 surjectivity.
      have hΓg_epi : Epi (S.g.val.app (op ⊤)) := by
        rw [AddCommGrpCat.epi_iff_surjective]; intro q
        -- Γ(Q) = colim Γ(Q_j) via filtered colimit preservation
        haveI := createsFilteredColimit Q
        have hc_top_Q := isColimitOfPreserves
          ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))
          (isColimitOfPreserves (sheafToPresheaf _ _) hqColim)
        obtain ⟨j₀, q₀, hq₀⟩ := Concrete.isColimit_exists_rep _ hc_top_Q q
        -- Per-piece: Γ(Inj.obj j₀) ↠ Γ(Q_{j₀}) from SES + mono + H^1(Y_{j₀}) = 0
        haveI : Mono (η.app j₀) := hη_mono j₀
        have hπ_epi := epi_g_app_top_of_H1_vanishing (shortExact_of_mono (η.app j₀)) (hvan j₀)
        rw [AddCommGrpCat.epi_iff_surjective] at hπ_epi
        obtain ⟨p, hp⟩ := hπ_epi q₀
        -- Composition: Inj.obj j₀ →[π_{j₀}] Q_{j₀} →[cocone] Q
        -- = Inj.obj j₀ →[ι_{j₀}] colim Inj →[S.g] Q
        refine ⟨(injCocone.ι.app j₀).val.app (op ⊤) p, ?_⟩
        show (S.g.val.app (op ⊤)) ((injCocone.ι.app j₀).val.app (op ⊤) p) = q
        have hcomp_sec : (injCocone.ι.app j₀ ≫ S.g).val.app (op ⊤) =
            (cokernel.π (η.app j₀) ≫ qCocone.ι.app j₀).val.app (op ⊤) :=
          congrArg (fun f => f.val.app (op ⊤)) (show cokernel.π (η.app j₀) ≫ qCocone.ι.app j₀ =
            injCocone.ι.app j₀ ≫ S.g from cokernel.π_desc _ _ _).symm
        rw [← hq₀, ← hp]; exact congrArg (· p) (congrArg ConcreteCategory.hom hcomp_sec)
      exact subsingleton_H1_via_surj _ hSE hI (ext0_surj_of_epi_top (S := S) hΓg_epi)
    | n' + 1 =>
      -- For n ≥ 1: dimension shift via h_van_Q + IH
      have h_van_Q : ∀ j, Subsingleton (Sheaf.H (Q.obj j) (n' + 1)) := fun j => by
        haveI : Mono (η.app j) := hη_mono j
        exact ext_dimension_shift_X₃ _ (shortExact_of_mono (η.app j)) (n' + 1)
          (Ext.subsingleton_of_injective _ _ n') (hvan j)
      exact ext_dimension_shift _ hSE (n' + 1) (ih Q qCocone hqColim h_van_Q) hI

/-- **Sheaf cohomology commutes with filtered colimits** on Noetherian spaces.
    If `H^n(F_j) = 0` for all pieces of a filtered diagram, then `H^n(colim F_j) = 0`.

    FULLY PROVED. -/
theorem sheafH_preserves_filtered_colimits
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c')
    (n : ℕ)
    (hvan : ∀ j, Subsingleton (Sheaf.H (Y'.obj j) n)) :
    Subsingleton (Sheaf.H c'.pt n) :=
  sheafH_filtered_colimit_aux n Y' c' hc' hvan

/-- **Sheaf cohomology commutes with filtered colimits (surjectivity)** on Noetherian spaces.
    Every element of `H^n(colim F_j)` comes from some `H^n(F_j)` via the canonical map.
    Together with injectivity (not proved here), this gives `colim H^n(F_j) ≅ H^n(colim F_j)`. -/
theorem sheafH_filtered_colimit_surj
    {X : TopCat.{u}} [NoetherianSpace X]
    (n : ℕ) :
    ∀ {J' : Type u} [SmallCategory J'] [IsFiltered J']
      (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
      (c' : Cocone Y') (hc' : IsColimit c') --
      (x : Sheaf.H c'.pt n),
    ∃ (j : J') (y : Sheaf.H (Y'.obj j) n),
      y.comp (Ext.mk₀ (c'.ι.app j)) (add_zero n) = x := by
  induction n with
  | zero =>
    intro J' inst1 inst2 Y' c' hc' x
    letI := inst1; letI := inst2
    haveI := createsFilteredColimit Y'
    have hc_psh := isColimitOfPreserves (sheafToPresheaf _ _) hc'
    have hc_top := isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh
    let x_sec := sheafH0EquivSections c'.pt x
    obtain ⟨j, s_j, hs_j⟩ := Concrete.isColimit_exists_rep _ hc_top x_sec
    let y := (sheafH0EquivSections (Y'.obj j)).symm s_j
    refine ⟨j, y, ?_⟩
    apply (sheafH0EquivSections c'.pt).injective
    rw [sheafH0EquivSections_natural, AddEquiv.apply_symm_apply]
    exact hs_j
  | succ n ih =>
    intro J' inst1 inst2 Y' c' hc' x
    letI := inst1; letI := inst2
    letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) := Limits.HasZeroObject.zero' _
    let toArrow : J' ⥤ Arrow (TopCat.Sheaf AddCommGrpCat.{u} X) :=
      { obj := fun j => Arrow.mk (0 : Y'.obj j ⟶ 0)
        map := fun f => Arrow.homMk (Y'.map f) (𝟙 0) (by simp)
        map_id := fun j => by ext <;> simp
        map_comp := fun f g => by ext <;> simp }
    let ffData := MorphismProperty.functorialFactorizationData
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
    let Inj : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X := toArrow ⋙ ffData.Z
    let η : Y' ⟶ Inj :=
      { app := fun j => ffData.i.app (toArrow.obj j)
        naturality := fun _ _ f => ffData.i.naturality (toArrow.map f) }
    have hη_mono : ∀ j, Mono (η.app j) := fun j => ffData.hi (toArrow.obj j)
    haveI hInj : ∀ j, Injective (Inj.obj j) := fun j =>
      IsGrothendieckAbelian.instInjectiveZMonomorphismsRlpMonoMapFactorizationDataRlpOfNatHom
    let injCocone : Cocone Inj := colimit.cocone Inj
    let ι'Cocone : Cocone Y' := Cocone.mk injCocone.pt
      { app := fun j => η.app j ≫ injCocone.ι.app j
        naturality := fun j j' f => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
            ← injCocone.w f, ← Category.assoc, η.naturality f] }
    let ι' : c'.pt ⟶ injCocone.pt := hc'.desc ι'Cocone
    haveI : Mono ι' := by
      haveI : ∀ j, Mono (η.app j) := hη_mono
      haveI := NatTrans.mono_of_mono_app η
      exact colim.map_mono' η hc' (colimit.isColimit Inj) ι' (fun j => hc'.fac ι'Cocone j)
    let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
      ShortComplex.mk ι' (cokernel.π ι') (cokernel.condition ι')
    have hSE : S.ShortExact := shortExact_of_mono ι'
    have hI := flasqueVanishing X injCocone.pt
      (isFlasque_filtered_colimit Inj (fun j => isFlasque_of_injective _)
        (colimit.isColimit Inj)) n
    let Q : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
      { obj := fun j => cokernel (η.app j)
        map := fun {j j'} f => cokernel.map _ _ (Y'.map f) (Inj.map f) (η.naturality f).symm
        map_id := fun j => by ext; simp [cokernel.map]
        map_comp := fun {j j' j''} f g => by ext; simp [cokernel.map, Functor.map_comp] }
    have hfac_ι : ∀ j, c'.ι.app j ≫ ι' = η.app j ≫ injCocone.ι.app j := hc'.fac ι'Cocone
    let qCocone : Cocone Q := Cocone.mk S.X₃
      { app := fun j => cokernel.map (η.app j) ι' (c'.ι.app j) (injCocone.ι.app j)
            (hfac_ι j).symm
        naturality := fun j j' f => by
          ext; show cokernel.π _ ≫ Q.map f ≫ _ = cokernel.π _ ≫ _ ≫ _
          rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc]
          simp [cokernel.π_desc, Functor.const_obj_map] }
    have hqColim : IsColimit qCocone := by
      haveI : Nonempty J' := IsFiltered.nonempty
      have hπC : ∀ j, cokernel.π (η.app j) ≫ qCocone.ι.app j =
          injCocone.ι.app j ≫ cokernel.π ι' := fun j => cokernel.π_desc _ _ _
      have hπQ : ∀ {j₁ j₂ : J'} (a : j₁ ⟶ j₂),
          cokernel.π (η.app j₁) ≫ Q.map a =
          Inj.map a ≫ cokernel.π (η.app j₂) := fun a => cokernel.π_desc _ _ _
      let liftCocone : ∀ (s : Cocone Q), Cocone Inj := fun s =>
        Cocone.mk s.pt
          { app := fun j => cokernel.π (η.app j) ≫ s.ι.app j
            naturality := fun j j' a => by
              dsimp; rw [Category.comp_id, ← Category.assoc, ← hπQ a, Category.assoc, s.w] }
      let injColim := colimit.isColimit Inj
      exact
      { desc := fun s => cokernel.desc ι' (injColim.desc (liftCocone s)) (by
          apply hc'.hom_ext; intro j
          rw [comp_zero]; conv_lhs => rw [← Category.assoc, hfac_ι j, Category.assoc]
          rw [injColim.fac, ← Category.assoc, cokernel.condition, zero_comp])
        fac := fun s j => by
          apply (cancel_epi (cokernel.π (η.app j))).mp
          rw [← Category.assoc, hπC, Category.assoc, cokernel.π_desc, injColim.fac]
        uniq := fun s m hm => by
          apply (cancel_epi (cokernel.π ι')).mp
          rw [cokernel.π_desc]
          apply injColim.hom_ext; intro j
          rw [injColim.fac]
          show injCocone.ι.app j ≫ cokernel.π ι' ≫ m = _
          rw [← Category.assoc, ← hπC j, Category.assoc, hm] }
    have hSE_j : ∀ j, (ShortComplex.mk (η.app j) (cokernel.π (η.app j))
        (cokernel.condition (η.app j))).ShortExact := fun j => by
      haveI : Mono (η.app j) := hη_mono j; exact shortExact_of_mono (η.app j)
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hSE x
      (@Subsingleton.elim _ hI _ _) rfl
    obtain ⟨j₀, y_j, hy_j⟩ := ih (Y' := Q) qCocone hqColim y
    haveI : Mono (η.app j₀) := hη_mono j₀
    let x_j : Sheaf.H (Y'.obj j₀) (n + 1) := y_j.comp (hSE_j j₀).extClass rfl
    refine ⟨j₀, x_j, ?_⟩
    show x_j.comp (Ext.mk₀ (c'.ι.app j₀)) (add_zero (n + 1)) = x
    rw [show x_j = y_j.comp (hSE_j j₀).extClass rfl from rfl]
    rw [Ext.comp_assoc_of_third_deg_zero]
    have h_nat : (Ext.mk₀ (qCocone.ι.app j₀)).comp hSE.extClass (zero_add 1) =
        (hSE_j j₀).extClass.comp (Ext.mk₀ (c'.ι.app j₀)) (add_zero 1) :=
      extClass_naturality (hSE_j j₀) hSE (ShortComplex.homMk (c'.ι.app j₀) (injCocone.ι.app j₀)
        (qCocone.ι.app j₀) (hfac_ι j₀) (cokernel.π_desc _ _ _).symm)
    rw [← h_nat, ← Ext.comp_assoc_of_second_deg_zero, hy_j, hy]

/-- **Hartshorne III, Ex. 2.9 core**: on a Noetherian space, if `H^m = 0` for all finitely generated
    subsheaves of `K`, then `H^m(K) = 0`. Applies `sheafH_preserves_filtered_colimits`
    to the filtered diagram of finitely generated subsheaves. -/
theorem cohomology_vanishing_of_finitelyGenerated_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    (K : TopCat.Sheaf AddCommGrpCat.{u} X) (m : ℕ)
    (hfg : ∀ (S : Finset (TopCat.Sheaf.SectionIndex K))
      [HasCoproduct fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1],
      Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf S) m)) :
    Subsingleton (Sheaf.H K m) :=
  sheafH_preserves_filtered_colimits (finsetGenFunctor K) (finsetGenCocone K)
    (finsetGenCocone_isColimit K) m (fun S => hfg S)

section FinsetGenerated
open scoped Classical

variable {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K}
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]

/-- Coproduct inclusion for the insertion `S' ⊆ insert σ₀ S'`. -/
noncomputable abbrev finsetCoproductIncl (_ : σ₀ ∉ S') :=
  finsetCoproductInclGen K (Finset.subset_insert σ₀ S')

/-- Image inclusion for the insertion `S' ⊆ insert σ₀ S'`. -/
noncomputable abbrev imageIncl (_ : σ₀ ∉ S') :=
  finsetImageInclGen K (Finset.subset_insert σ₀ S')

/-- The image inclusion for `insert σ₀ S'` is a monomorphism. -/
instance imageIncl_mono (hσ₀ : σ₀ ∉ S') :
    Mono (imageIncl hσ₀ : TopCat.Sheaf.finsetGeneratedSheaf S' ⟶ _) :=
  finsetImageInclGen_mono K (Finset.subset_insert σ₀ S')

/-- The `σ₀`-component maps epi onto the cokernel of `imageIncl`. -/
theorem imageIncl_cokernel_epi (hσ₀ : σ₀ ∉ S') :
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
    simp [finsetCoproductIncl, finsetCoproductInclGen, TopCat.Sheaf.finsetGeneratorMap,
      TopCat.Sheaf.familyGeneratorMap]
  have hfac : proj ≫
      (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1)
        ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
      factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π (imageIncl hσ₀)) =
    factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π (imageIncl hσ₀) := by
    ext ⟨σ, hσ⟩
    simp only [proj]
    by_cases h : σ = σ₀
    · subst h; simp
    · rw [← Category.assoc
        (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟨σ, hσ⟩)
        (Sigma.desc _)]
      rw [colimit.ι_desc, Cofan.mk_ι_app, dif_neg h, zero_comp]
      symm
      have hι : Sigma.ι (fun τ : {τ // τ ∈ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1)
          ⟨σ, Finset.mem_of_mem_insert_of_ne hσ h⟩ ≫
          finsetCoproductIncl hσ₀ =
        Sigma.ι (fun τ : {τ // τ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, hσ⟩ := by
        simp [finsetCoproductIncl, finsetCoproductInclGen]
      rw [← hι, Category.assoc, reassoc_of% heq]; simp [cokernel.condition]
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
  intro T; induction T using Finset.induction with
  | empty =>
    apply subsingleton_sheafH_of_isZero'
    apply IsZero.of_iso (isZero_zero _) (imageZero' _)
    apply Sigma.hom_ext; intro ⟨σ, hσ⟩; simp at hσ
  | @insert σ₀ S' hσ₀ ih =>
    haveI : Mono (imageIncl hσ₀) := imageIncl_mono hσ₀
    let SC := ShortComplex.mk (imageIncl hσ₀) (cokernel.π (imageIncl hσ₀))
      (cokernel.condition _)
    have hSE : SC.ShortExact := shortExact_of_mono (imageIncl hσ₀)
    have hCoker : Subsingleton (Sheaf.H SC.X₃ m) :=
      haveI := imageIncl_cokernel_epi hσ₀
      hzero (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} =>
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
