/-
  SetupCore.lean -- Closed immersion infrastructure for Grothendieck vanishing

  Provides:
  1. `PushforwardHVanishing` (pushforward preserves cohomological vanishing)
  2. `epi_unit_of_closedImmersion` (adjunction unit is epi)
  3. `ClosedImmersionSES` (short exact sequence from closed immersion)

  Depends on FlasqueVanishing.lean for `FlasqueVanishing`, `IsFlasqueSheaf`,
  `isFlasque_of_injective`.
-/
import Aristotle.GrothendieckVanishing.main.FlasqueVanishing

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-! ## Building blocks for the closed-open decomposition

ReducibleVanishing and IrreduciblePosVanishing require two building blocks:

1. PushforwardHVanishing: pushforward along closed immersion preserves vanishing
   (adjunction + mono preservation + exactness of i_*)
2. ClosedImmersionSES: the adjunction unit F -> i_*(i^*F) gives a short exact sequence
-/

-- stalkPushforward naturality w.r.t. presheaf morphisms
private theorem stalkPush_nat_closedIncl
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F G : X.Presheaf AddCommGrpCat.{u}} (α : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (ConcreteCategory.hom f x)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map α) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f G x =
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f F x ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α := by
  apply TopCat.Presheaf.stalk_hom_ext; intro U hU
  simp only [TopCat.Presheaf.stalkFunctor_map_germ_assoc,
    TopCat.Presheaf.stalkPushforward_germ,
    TopCat.Presheaf.stalkPushforward_germ_assoc,
    TopCat.Presheaf.stalkFunctor_map_germ]; rfl

-- Stalk of pushforward is zero outside the closed set
private theorem pushforward_stalk_zero_closedIncl
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) (x : X) (hx : x ∉ s)
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) :
    ∀ a : ((TopCat.Presheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs)).obj G.val).stalk x, a = 0 := by
  let F := (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).obj G.val
  intro a
  obtain ⟨U, hxU, sU, rfl⟩ := F.germ_exist x a
  let W : Opens X := U ⊓ ⟨sᶜ, hs.isOpen_compl⟩
  have hxW : x ∈ W := ⟨hxU, hx⟩
  have hW_bot : (Opens.map (TopCat.closedIncl hs)).obj W = ⊥ := by
    ext ⟨y, hy⟩; simp only [Opens.map, TopCat.closedIncl, SetLike.mem_coe,
      Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun h => absurd hy h.2
  have hFW_zero : IsZero (F.obj (op W)) := by
    change IsZero (G.val.obj (op ((Opens.map (TopCat.closedIncl hs)).obj W)))
    rw [hW_bot]; exact (isTerminal_sheaf_bot G).isZero
  let sW := ConcreteCategory.hom (F.map (homOfLE (show W ≤ U from inf_le_left)).op) sU
  have hsW_eq : sW = 0 := by
    calc sW = ConcreteCategory.hom (𝟙 (F.obj (op W))) sW :=
              (ConcreteCategory.id_apply sW).symm
      _ = ConcreteCategory.hom (0 : F.obj (op W) ⟶ F.obj (op W)) sW := by
              rw [hFW_zero.eq_of_src (𝟙 _) 0]
      _ = 0 := AddMonoidHom.zero_apply _
  rw [← TopCat.Presheaf.germ_res_apply F
    (homOfLE (show W ≤ U from inf_le_left)) x hxW sU]
  change ConcreteCategory.hom (F.germ W x hxW) sW = 0
  rw [hsW_eq]; exact AddMonoidHom.map_zero _

-- Surjectivity transfer: f ≫ g = h ≫ k with g, h iso and k surj → f surj
private theorem surj_transfer_closedIncl {A B C D : AddCommGrpCat.{u}}
    {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ D} {k : D ⟶ C}
    [IsIso g] [IsIso h]
    (hnat : f ≫ g = h ≫ k)
    (hk : Function.Surjective (ConcreteCategory.hom k)) :
    Function.Surjective (ConcreteCategory.hom f) := by
  intro b
  obtain ⟨d, hd⟩ := hk (ConcreteCategory.hom g b)
  refine ⟨ConcreteCategory.hom (inv h) d, ?_⟩
  rw [show ConcreteCategory.hom f (ConcreteCategory.hom (inv h) d) =
      ConcreteCategory.hom (inv h ≫ f) d from
        (ConcreteCategory.comp_apply _ _ _).symm,
    show inv h ≫ f = k ≫ inv g by
      have : f = h ≫ k ≫ inv g := by
        rw [← Category.assoc, ← hnat, Category.assoc,
          IsIso.hom_inv_id, Category.comp_id]
      rw [this]; simp,
    ConcreteCategory.comp_apply, hd, ← ConcreteCategory.comp_apply,
    IsIso.hom_inv_id, ConcreteCategory.id_apply]

-- Cache Balanced to avoid expensive synthesis chain
-- (Abelian → IsNormalEpiCategory → StrongEpiCategory → Balanced)
noncomputable instance sheafStrongEpiCategory (X : TopCat.{u}) :
    StrongEpiCategory (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  strongEpiCategory_of_regularEpiCategory

noncomputable instance sheafBalanced (X : TopCat.{u}) :
    Balanced (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  balanced_of_strongEpiCategory

-- Stalkwise surjectivity of pushed-forward g
private theorem closedIncl_pushforward_epi_g
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)}
    (ip : InjectivePresentation G)
    (hSE : ip.shortComplex.ShortExact) :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map ip.shortComplex.g) := by
  letI : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := sheafBalanced X
  rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}]
  change TopCat.Presheaf.IsLocallySurjective
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map ip.shortComplex.g).val
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x
  by_cases hx : (x : X) ∈ s
  · let z : TopCat.of s := ⟨x, hx⟩
    haveI : IsIso (TopCat.Presheaf.stalkPushforward
        AddCommGrpCat.{u} (TopCat.closedIncl hs)
        ip.shortComplex.X₂.val z) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat.{u}
        hs.isClosedEmbedding_subtypeVal.isInducing _ z
    haveI : IsIso (TopCat.Presheaf.stalkPushforward
        AddCommGrpCat.{u} (TopCat.closedIncl hs)
        ip.shortComplex.X₃.val z) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat.{u}
        hs.isClosedEmbedding_subtypeVal.isInducing _ z
    have hg_surj : Function.Surjective
        (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
            ip.shortComplex.g.val)) :=
      ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
          (T := ip.shortComplex.g.val)).mp
        ((Sheaf.isLocallySurjective_iff_epi'
            AddCommGrpCat.{u} _).mpr hSE.epi_g)) z
    exact surj_transfer_closedIncl
      (hnat := stalkPush_nat_closedIncl
        (TopCat.closedIncl hs) ip.shortComplex.g.val z)
      hg_surj
  · intro b
    rw [pushforward_stalk_zero_closedIncl hs x hx ip.shortComplex.X₃ b]
    exact ⟨0, AddMonoidHom.map_zero _⟩

-- Pushforward along closed immersion preserves ShortExact.
theorem closedIncl_pushforward_shortExact
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)}
    (ip : InjectivePresentation G) :
    (ip.shortComplex.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs))).ShortExact := by
  have hSE := ip.shortExact_shortComplex
  haveI : Mono (ip.shortComplex.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs))).f := by
    change Mono ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map _)
    exact Functor.map_mono _ _
  have hExact : (ip.shortComplex.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs))).Exact :=
    hSE.exact.map_of_mono_of_preservesKernel _ hSE.mono_f inferInstance
  haveI : Epi (ip.shortComplex.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs))).g := by
    change Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map _)
    exact closedIncl_pushforward_epi_g hs ip hSE
  exact ShortComplex.ShortExact.mk' hExact ‹_› ‹_›

-- Pushforward preserves flasqueness for any continuous map.
theorem pushforward_preserves_flasque {Y : TopCat.{u}} (f : TopCat.of Y ⟶ X)
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Y)) (hG : IsFlasqueSheaf G) :
    IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj G) :=
  fun i => by change Epi (G.val.map ((Opens.map f).op.map i.op)); exact hG _

-- If both ends of a short exact sequence have vanishing H^n, so does the middle.
theorem subsingleton_sheafH_of_shortExact_middle {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₁ : Subsingleton (Sheaf.H S.X₁ n))
    (h₃ : Subsingleton (Sheaf.H S.X₃ n)) :
    Subsingleton (Sheaf.H S.X₂ n) := by
  let Z := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))
  constructor
  intro a b
  have ha : a.comp (Ext.mk₀ S.g) (add_zero n) = 0 := @Subsingleton.elim _ ((add_zero n) ▸ h₃) _ _
  have hb : b.comp (Ext.mk₀ S.g) (add_zero n) = 0 := @Subsingleton.elim _ ((add_zero n) ▸ h₃) _ _
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₂ Z hS a ha
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₂ Z hS b hb
  rw [← hc, ← hd, @Subsingleton.elim _ h₁ c d]

/-! ### PushforwardHVanishing sub-lemmas -/

-- Base case: Γ comparison. Γ_X(i_*G') = G'(⊤_Z) = Γ_Z(G')
private lemma PushforwardHVanishing_zero
    {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) [NoetherianSpace X]
    (G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))
    (hG' : Subsingleton (Sheaf.H G' 0)) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G') 0) := by
  intro i
  let F' := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G'
  have hsec : Subsingleton (G'.val.obj (op ⊤)) := by
    letI := hG'; exact subsingleton_of_addEquiv (sheafH0EquivSections G')
  have htop : ((Opens.map i).obj ⊤ : Opens (TopCat.of Z)) = ⊤ := by ext; simp [Opens.map]
  have hobj : F'.val.obj (op ⊤) = G'.val.obj (op ⊤) := by
    change G'.val.obj (op ((Opens.map i).obj ⊤)) = G'.val.obj (op ⊤)
    simpa [TopCat.Sheaf.pushforward, TopCat.Presheaf.pushforward, htop]
  constructor; intro a b
  apply (sheafH0EquivSections F').injective
  exact @Subsingleton.elim (F'.val.obj (op ⊤)) (hobj ▸ hsec) _ _

-- Helper: Ext₀ composition identity used in epi_g_app_top_of_H1_vanishing
private lemma ext0_comp_eq_of_covariant
    {Z : TopCat.{u}} [NoetherianSpace Z]
    {A B C : TopCat.Sheaf AddCommGrpCat.{u} Z}
    (g : B ⟶ C)
    (z : Ext A B 0)
    (φ : A ⟶ C)
    (hz : z.comp (Ext.mk₀ g) (add_zero 0) = Ext.addEquiv₀.symm φ) :
    Ext.addEquiv₀ z ≫ g = φ := by
  apply Ext.addEquiv₀.symm.injective
  change Ext.addEquiv₀.symm (Ext.addEquiv₀ z ≫ g) = Ext.addEquiv₀.symm φ
  rw [show Ext.addEquiv₀.symm (Ext.addEquiv₀ z ≫ g) =
      Ext.mk₀ (Ext.addEquiv₀ z ≫ g) from rfl, ← Ext.mk₀_comp_mk₀]
  show (Ext.addEquiv₀.symm (Ext.addEquiv₀ z)).comp
      (Ext.mk₀ g) _ = Ext.addEquiv₀.symm φ
  rw [AddEquiv.symm_apply_apply]; exact hz

-- Sub-lemma: Epi of g at ⊤ from H^1(G')=0 via LES + adj + separator
private lemma epi_g_app_top_of_H1_vanishing
    {Z : TopCat.{u}} [NoetherianSpace Z]
    {G' : TopCat.Sheaf AddCommGrpCat.{u} Z}
    (ip : InjectivePresentation G')
    (hG' : Subsingleton (Sheaf.H G' 1)) :
    Epi (ip.shortComplex.g.val.app (op ⊤)) := by
  have hSE_Z := ip.shortExact_shortComplex
  rw [AddCommGrpCat.epi_iff_surjective]; intro r
  let R_top := ip.shortComplex.X₃.val.obj (op ⊤)
  let φ_hom : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ R_top :=
    AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun (n : ULift.{u} ℤ) => (n.down : ℤ) • (r : R_top))
        (fun a b => by simp [add_zsmul]))
  let adj_Z := constantSheafAdj (Opens.grothendieckTopology Z)
    AddCommGrpCat.{u} Limits.isTerminalTop
  let φ := (adj_Z.homEquiv _ ip.shortComplex.X₃).symm φ_hom
  have hy : (Ext.addEquiv₀.symm φ).comp hSE_Z.extClass rfl = 0 :=
    @Subsingleton.elim _ hG' _ _
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hSE_Z _ rfl hy
  let ψ := Ext.addEquiv₀ z
  have hψ : ψ ≫ ip.shortComplex.g = φ :=
    ext0_comp_eq_of_covariant ip.shortComplex.g z φ hz
  let ψ_hom := (adj_Z.homEquiv _ ip.shortComplex.X₂) ψ
  have hfact := Adjunction.homEquiv_naturality_right adj_Z ψ ip.shortComplex.g
  rw [hψ, Equiv.apply_symm_apply] at hfact
  change φ_hom = ψ_hom ≫ ip.shortComplex.g.val.app (op ⊤) at hfact
  refine ⟨ψ_hom (ULift.up 1), ?_⟩
  change (ConcreteCategory.hom (ψ_hom ≫ ip.shortComplex.g.val.app (op ⊤))) (ULift.up 1) = r
  rw [← hfact]; simp [φ_hom, one_zsmul]

-- Sub-lemma: surjectivity of Ext⁰ map from epi at ⊤ via adjunction + projectivity
private lemma ext0_surj_of_epi_top
    {X : TopCat.{u}} [NoetherianSpace X]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hg_epi_top : Epi (S.g.val.app (op ⊤))) :
    ∀ y : Sheaf.H S.X₃ 0,
      ∃ z : Sheaf.H S.X₂ 0,
        z.comp (Ext.mk₀ S.g) (add_zero 0) = y := by
  intro y
  suffices ∃ ψ : _ ⟶ S.X₂, ψ ≫ S.g = Ext.addEquiv₀ y by
    obtain ⟨ψ, hψ⟩ := this
    exact ⟨Ext.mk₀ ψ, by rw [Ext.mk₀_comp_mk₀, hψ, Ext.mk₀_addEquiv₀_apply]⟩
  have hΓg : Epi ((Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map S.g) :=
    epi_of_natIso_epi (Sheaf.ΓNatIsoSheafSections _ _ Limits.isTerminalTop).symm S.g hg_epi_top
  let adj := constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let M := AddCommGrpCat.of (ULift.{u} ℤ)
  haveI : Projective M := ulift_int_projective
  exact ⟨(adj.homEquiv M _).symm (Projective.factorThru
    ((adj.homEquiv M _) (Ext.addEquiv₀ y))
    ((Sheaf.Γ _ _).map S.g)), by
    apply (adj.homEquiv M _).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
      Projective.factorThru_comp]⟩

-- n = 1: from H^1(G')=0 on Z, show H^1(i_*G')=0 on X
private lemma PushforwardHVanishing_one
    {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) [NoetherianSpace X]
    (G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))
    (hG' : Subsingleton (Sheaf.H G' 1)) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G') 1) := by
  intro i
  obtain ⟨ip⟩ := EnoughInjectives.presentation G'
  have hSE_Z := ip.shortExact_shortComplex
  have hSE_X : (ip.shortComplex.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)).ShortExact :=
    closedIncl_pushforward_shortExact hZ ip
  have hFlasque : IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat i).obj
      ip.shortComplex.X₂) :=
    fun {U V} j => by
      change Epi (ip.shortComplex.X₂.val.map ((Opens.map i).op.map j.op))
      exact isFlasque_of_injective ip.shortComplex.X₂ _
  have hJ : Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat i).obj
      ip.shortComplex.X₂) 1) :=
    FlasqueVanishing _ _ hFlasque 0
  have htop : ((Opens.map i).obj ⊤ : Opens (TopCat.of Z)) = ⊤ := by ext; simp [Opens.map]
  have hg_epi : Epi (ip.shortComplex.g.val.app (op ⊤)) :=
    epi_g_app_top_of_H1_vanishing ip hG'
  have hg_epi_X : Epi ((ip.shortComplex.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)).g.val.app (op ⊤)) := by
    show Epi (ip.shortComplex.g.val.app (op ((Opens.map i).obj ⊤)))
    rw [htop]; exact hg_epi
  have hsurj_X := ext0_surj_of_epi_top hg_epi_X
  constructor; intro a b
  have ha : a.comp (Ext.mk₀ (ip.shortComplex.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)).f) rfl = 0 :=
    @Subsingleton.elim _ hJ _ 0
  have hb : b.comp (Ext.mk₀ (ip.shortComplex.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)).f) rfl = 0 :=
    @Subsingleton.elim _ hJ _ 0
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hSE_X a ha rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hSE_X b hb rfl
  have zero_c : c.comp hSE_X.extClass rfl = 0 := by
    obtain ⟨c', hc'⟩ := hsurj_X c
    rw [← hc', Ext.comp_assoc_of_second_deg_zero c' (Ext.mk₀
      (ip.shortComplex.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)).g)
      hSE_X.extClass rfl, hSE_X.comp_extClass,
      Ext.comp_zero c' _ 1 1 rfl]
  have zero_d : d.comp hSE_X.extClass rfl = 0 := by
    obtain ⟨d', hd'⟩ := hsurj_X d
    rw [← hd', Ext.comp_assoc_of_second_deg_zero d' (Ext.mk₀
      (ip.shortComplex.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)).g)
      hSE_X.extClass rfl, hSE_X.comp_extClass,
      Ext.comp_zero d' _ 1 1 rfl]
  rw [← hc, ← hd, zero_c, zero_d]

-- n = m+2 ≥ 2: use pushed-forward injective presentation + FlasqueVanishing + LES
private lemma PushforwardHVanishing_succ
    {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) [NoetherianSpace X]
    (m : ℕ)
    (ih_push : ∀ (G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)),
      Subsingleton (Sheaf.H G' (m + 1)) →
      let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G') (m + 1)))
    (G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))
    (hG' : Subsingleton (Sheaf.H G' (m + 2))) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G') (m + 2)) := by
  intro i
  obtain ⟨ip⟩ := EnoughInjectives.presentation G'
  have hSE_X : (ip.shortComplex.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)).ShortExact :=
    closedIncl_pushforward_shortExact hZ ip
  have hFlasque : IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat i).obj
      ip.shortComplex.X₂) :=
    fun {U V} j => by
      change Epi (ip.shortComplex.X₂.val.map ((Opens.map i).op.map j.op))
      exact isFlasque_of_injective ip.shortComplex.X₂ _
  haveI hJ : Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat i).obj
      ip.shortComplex.X₂) (m + 2)) :=
    FlasqueVanishing _ _ hFlasque (m + 1)
  constructor; intro a b
  have ha : a.comp (Ext.mk₀ (ip.shortComplex.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)).f) rfl = 0 :=
    @Subsingleton.elim _ hJ _ 0
  have hb : b.comp (Ext.mk₀ (ip.shortComplex.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)).f) rfl = 0 :=
    @Subsingleton.elim _ hJ _ 0
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hSE_X a ha rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hSE_X b hb rfl
  rw [← hc, ← hd]; congr 1
  have hR : Subsingleton (Sheaf.H ip.shortComplex.X₃ (m + 1)) := by
    constructor; intro c d
    have hSE_Z := ip.shortExact_shortComplex
    have heq : c.comp hSE_Z.extClass rfl = d.comp hSE_Z.extClass rfl :=
      @Subsingleton.elim _ hG' _ _
    have hker : (c - d).comp hSE_Z.extClass rfl = 0 := by
      change (Ext.postcomp hSE_Z.extClass _ rfl) (c - d) = 0
      rw [map_sub, sub_eq_zero]; exact heq
    obtain ⟨e, he⟩ := Ext.covariant_sequence_exact₃ _ hSE_Z (c - d) rfl hker
    rw [Ext.eq_zero_of_injective e, Ext.zero_comp] at he
    exact sub_eq_zero.mp he.symm
  exact @Subsingleton.elim _ (ih_push ip.shortComplex.X₃ hR) c d

-- Pushforward along closed immersion preserves cohomological vanishing.
theorem PushforwardHVanishing
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    [NoetherianSpace X]
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)) (n : ℕ)
    (h : Subsingleton (Sheaf.H G n)) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) n) := by
  intro i
  suffices ∀ (m : ℕ) (G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)),
      Subsingleton (Sheaf.H G' m) →
      Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G') m) from
    this n G h
  intro m
  induction m with
  | zero => exact PushforwardHVanishing_zero hZ
  | succ k ih_push =>
    intro G' hG'
    cases k with
    | zero => exact PushforwardHVanishing_one hZ G' hG'
    | succ m => exact PushforwardHVanishing_succ hZ m ih_push G' hG'

-- The adjunction unit F → i_*(i^*F) is epi for closed immersions.
-- Proof: stalkwise surjective (identity on Z, maps to 0 outside Z).
-- Requires: stalkPushforward_iso_of_isInducing + stalk of i_*G = 0 outside Z.
-- epi via surjective on stalks
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
  · -- x ∈ Z: stalk map is surjective
    let y : TopCat.of Z := ⟨x, hxZ⟩
    change Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} ((TopCat.closedIncl hZ) y)).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (TopCat.closedIncl hZ)).unit.app F).val)
    haveI :
        IsIso
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} ((TopCat.closedIncl hZ) y)).map
            ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
              (TopCat.closedIncl hZ)).unit.app F).val) :=
      TopCat.closedIncl_unit_stalk_isIso hZ F y
    intro b
    refine
      ⟨inv
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} ((TopCat.closedIncl hZ) y)).map
            ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
              (TopCat.closedIncl hZ)).unit.app F).val) b, ?_⟩
    simp
  · -- x ∉ Z: target stalk is 0 (pushforward has zero stalk outside closed Z)
    -- Show stalk is IsZero by showing all colimit injections (germs) are 0.
    -- Each germ_V factors through V' = V ∩ (X\Z) where the source is 0.
    let D := (OpenNhds.inclusion x).op ⋙
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj F)).val
    have hstalk_zero : IsZero (colimit D) := by
      rw [IsZero.iff_id_eq_zero]
      apply colimit.hom_ext; intro ⟨⟨V, hxV⟩⟩
      simp only [comp_zero, Category.comp_id]
      let Zc : Opens X := ⟨Zᶜ, hZ.isOpen_compl⟩
      let V'_nhd : OpenNhds x := ⟨V ⊓ Zc, ⟨hxV, hxZ⟩⟩
      rw [show colimit.ι D (op ⟨V, hxV⟩) =
        D.map (homOfLE (show V'_nhd.1 ≤ V from inf_le_left) : V'_nhd ⟶ ⟨V, hxV⟩).op ≫
          colimit.ι D (op V'_nhd) from (colimit.w D _).symm]
      suffices IsZero (D.obj (op V'_nhd)) by
        rw [this.eq_zero_of_src (colimit.ι D (op V'_nhd)), comp_zero]
      change IsZero (((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj F).val.obj
        (op ((Opens.map i).obj V'_nhd.1)))
      have : (Opens.map i).obj V'_nhd.1 = ⊥ := by
        apply le_antisymm
        · intro ⟨y, hy⟩ hmem
          simp only [Opens.map, Opens.mem_mk] at hmem
          exact absurd hy (hmem.2 ·)
        · exact bot_le
      rw [this]
      exact (isTerminal_sheaf_bot _).isZero
    -- The stalk is IsZero → surjective
    intro b; refine ⟨0, ?_⟩; simp only [map_zero]
    have hsub := AddCommGrpCat.subsingleton_of_isZero hstalk_zero
    exact (@Subsingleton.elim _ hsub b 0).symm

-- Short exact sequence from closed immersion.
-- Uses epi_unit_of_closedImmersion to form 0 → ker(η) → F → i_*(i^*F) → 0.
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

/-- Dimension shift via SES: if `0 → X₁ → X₂ → X₃ → 0` is short exact,
`H^n(X₃) = 0`, and `H^{n+1}(X₂) = 0`, then `H^{n+1}(X₁) = 0`. -/
theorem sheafH_dimension_shift_ses {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₃ : Subsingleton (Sheaf.H S.X₃ n))
    (h₂ : Subsingleton (Sheaf.H S.X₂ (n + 1))) :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) := by
  constructor; intro a b
  have ha : a.comp (Ext.mk₀ S.f) rfl = 0 := @Subsingleton.elim _ h₂ _ _
  have hb : b.comp (Ext.mk₀ S.f) rfl = 0 := @Subsingleton.elim _ h₂ _ _
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hS a ha rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hS b hb rfl
  rw [← hc, ← hd, @Subsingleton.elim _ h₃ c d]
