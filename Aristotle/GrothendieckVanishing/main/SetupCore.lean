/-
  SetupCore.lean -- Closed immersion infrastructure for Grothendieck vanishing

  Provides:
  1. `pushforwardHVanishing` (pushforward preserves cohomological vanishing)
  2. `epi_unit_of_closedImmersion` (adjunction unit is epi)
  3. `closedImmersionSES` (short exact sequence from closed immersion)

  Depends on FlasqueCohomology.lean for `flasqueVanishing`, `sheafH0EquivSections`,
  and FlasqueVanishing.lean for `IsFlasqueSheaf`, `isFlasque_of_injective`.
-/
import Aristotle.GrothendieckVanishing.main.FlasqueCohomology
import Mathlib.Topology.NoetherianSpace

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-- The induction hypothesis for Grothendieck vanishing: vanishing holds for all
    sheaves on all spaces of strictly smaller Krull dimension than X. -/
abbrev VanishingIH {X : TopCat.{u}} (dimX := topologicalKrullDim X) : Prop :=
  ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
    (m : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
    topologicalKrullDim Y < dimX →
    m > topologicalKrullDim Y →
    Subsingleton (Sheaf.H G m)

/-! ## Abstract Ext dimension shift helpers -/

section ExtDimShift
variable {C' : Type*} [Category C'] [Abelian C'] [HasExt C']

/-- Dimension shift for Ext via LES: given `0 → X₁ → X₂ → X₃ → 0` short exact,
    `Ext^n(Z, X₃) = 0` and `Ext^{n+1}(Z, X₂) = 0` imply `Ext^{n+1}(Z, X₁) = 0`. -/
theorem ext_dimension_shift (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₃ : Subsingleton (Ext Z S.X₃ n))
    (h₂ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Subsingleton (Ext Z S.X₁ (n + 1)) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hS a (@Subsingleton.elim _ h₂ _ _) rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hS b (@Subsingleton.elim _ h₂ _ _) rfl
  rw [← hc, ← hd, @Subsingleton.elim _ h₃ c d]

/-- Reverse dimension shift: `Ext^n(Z, X₂) = 0` and `Ext^{n+1}(Z, X₁) = 0` imply
    `Ext^n(Z, X₃) = 0`. Uses exactness at X₃ in the covariant LES. -/
theorem ext_dimension_shift_X₃ (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂ : Subsingleton (Ext Z S.X₂ n))
    (h₁ : Subsingleton (Ext Z S.X₁ (n + 1))) :
    Subsingleton (Ext Z S.X₃ n) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₃ _ hS a rfl (@Subsingleton.elim _ h₁ _ _)
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₃ _ hS b rfl (@Subsingleton.elim _ h₁ _ _)
  rw [← hc, ← hd, @Subsingleton.elim _ h₂ c d]

/-- **Dimension shift additive equivalence**: given `0 → X₁ → X₂ → X₃ → 0` short exact
    with `Ext^n(Z, X₂) = 0` and `Ext^{n+1}(Z, X₂) = 0`, the connecting map
    `δ : Ext^n(Z, X₃) ≃+ Ext^{n+1}(Z, X₁)` is an isomorphism. -/
noncomputable def ext_dimension_shift_addEquiv (Z : C') {S : ShortComplex C'} (hS : S.ShortExact)
    (n : ℕ) (h₂n : Subsingleton (Ext Z S.X₂ n)) (h₂n1 : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Ext Z S.X₃ n ≃+ Ext Z S.X₁ (n + 1) :=
  let δ_fun : Ext Z S.X₃ n → Ext Z S.X₁ (n + 1) := fun x₃ => x₃.comp hS.extClass rfl
  have δ_inj : Function.Injective δ_fun := fun {a b} hab => by
    have : (a - b).comp hS.extClass rfl = 0 := by
      rw [show a - b = a + (-b) from sub_eq_add_neg a b, Ext.add_comp, Ext.neg_comp,
        show a.comp hS.extClass rfl = b.comp hS.extClass rfl from hab, add_neg_cancel]
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hS (a - b) rfl this
    rw [@Subsingleton.elim _ h₂n x₂ 0, Ext.zero_comp] at hx₂
    exact sub_eq_zero.mp hx₂.symm
  have δ_surj : Function.Surjective δ_fun := fun x₁ =>
    Ext.covariant_sequence_exact₁ _ hS x₁ (@Subsingleton.elim _ h₂n1 _ _) rfl
  AddEquiv.ofBijective
    (AddMonoidHom.mk' δ_fun (fun a b => Ext.add_comp a b hS.extClass rfl))
    ⟨δ_inj, δ_surj⟩

end ExtDimShift

/-! ## Building blocks for the closed-open decomposition

reducibleVanishing and irreduciblePosVanishing require two building blocks:

1. pushforwardHVanishing: pushforward along closed immersion preserves vanishing
   (adjunction + mono preservation + exactness of i_*)
2. closedImmersionSES: the adjunction unit F -> i_*(i^*F) gives a short exact sequence
-/

/-- Naturality of `stalkPushforward` with respect to presheaf morphisms. -/
theorem stalkPush_nat_closedIncl
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

/-- The stalk of a pushforward sheaf `i_* G` vanishes at points outside the closed set `s`. -/
theorem pushforward_stalk_zero_closedIncl
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) (x : X) (hx : x ∉ s)
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) :
    ∀ a : ((TopCat.Presheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs)).obj G.val).stalk x, a = 0 := by
  let F := (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).obj G.val
  intro a; obtain ⟨U, hxU, sU, rfl⟩ := F.germ_exist x a
  let W : Opens X := U ⊓ ⟨sᶜ, hs.isOpen_compl⟩
  have hxW : x ∈ W := ⟨hxU, hx⟩
  have hW_bot : (Opens.map (TopCat.closedIncl hs)).obj W = ⊥ :=
    le_antisymm (fun ⟨_, hy⟩ h => absurd hy h.2) bot_le
  have hFW_zero : IsZero (F.obj (op W)) := by
    change IsZero (G.val.obj (op ((Opens.map (TopCat.closedIncl hs)).obj W)))
    rw [hW_bot]; exact (isTerminal_sheaf_bot G).isZero
  let sW := ConcreteCategory.hom (F.map (homOfLE (show W ≤ U from inf_le_left)).op) sU
  have hsW_eq : sW = 0 := by
    have h0 : (𝟙 (F.obj (op W)) : _ ⟶ _) = 0 := hFW_zero.eq_of_src _ _
    calc sW = ConcreteCategory.hom (𝟙 (F.obj (op W))) sW := (ConcreteCategory.id_apply sW).symm
      _ = 0 := by rw [h0]; exact AddMonoidHom.zero_apply _
  rw [← TopCat.Presheaf.germ_res_apply F
    (homOfLE (show W ≤ U from inf_le_left)) x hxW sU]
  change ConcreteCategory.hom (F.germ W x hxW) sW = 0
  rw [hsW_eq]; exact AddMonoidHom.map_zero _

/-- Surjectivity transfer: if `f ≫ g = h ≫ k` with `g`, `h` isomorphisms and `k` surjective,
then `f` is surjective. -/
theorem surj_transfer_closedIncl {A B C D : AddCommGrpCat.{u}}
    {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ D} {k : D ⟶ C}
    [IsIso g] [IsIso h]
    (hnat : f ≫ g = h ≫ k)
    (hk : Function.Surjective (ConcreteCategory.hom k)) :
    Function.Surjective (ConcreteCategory.hom f) := by
  intro b; obtain ⟨d, hd⟩ := hk (ConcreteCategory.hom g b)
  refine ⟨ConcreteCategory.hom (inv h) d, ?_⟩
  rw [show ConcreteCategory.hom f (ConcreteCategory.hom (inv h) d) =
      ConcreteCategory.hom (inv h ≫ f) d from
        (ConcreteCategory.comp_apply _ _ _).symm,
    show inv h ≫ f = k ≫ inv g by
      rw [show f = h ≫ k ≫ inv g from by
        rw [← Category.assoc, ← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]; simp,
    ConcreteCategory.comp_apply, hd, ← ConcreteCategory.comp_apply,
    IsIso.hom_inv_id, ConcreteCategory.id_apply]

/-- Sheaves of abelian groups form a strong epi category. Cached to avoid expensive synthesis. -/
noncomputable instance sheafStrongEpiCategory (X : TopCat.{u}) :
    StrongEpiCategory (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  strongEpiCategory_of_regularEpiCategory

/-- Sheaves of abelian groups form a balanced category. Cached to avoid expensive synthesis. -/
noncomputable instance sheafBalanced (X : TopCat.{u}) :
    Balanced (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  balanced_of_strongEpiCategory

/-- Pushforward of the epi `g` in a short exact sequence along a closed inclusion is epi.
Proved by checking stalkwise surjectivity (identity on `s`, maps to `0` outside). -/
theorem closedIncl_pushforward_epi_g
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s))}
    (hSE : S.ShortExact) :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map S.g) := by
  letI : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := sheafBalanced X
  rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}]
  change TopCat.Presheaf.IsLocallySurjective
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map S.g).val
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x; by_cases hx : (x : X) ∈ s
  · let z : TopCat.of s := ⟨x, hx⟩
    haveI : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) S.X₂.val z) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat.{u} hs.isClosedEmbedding_subtypeVal.isInducing _ z
    haveI : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) S.X₃.val z) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat.{u} hs.isClosedEmbedding_subtypeVal.isInducing _ z
    have hg_surj : Function.Surjective
        (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
            S.g.val)) :=
      ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
          (T := S.g.val)).mp
        ((Sheaf.isLocallySurjective_iff_epi'
            AddCommGrpCat.{u} _).mpr hSE.epi_g)) z
    exact surj_transfer_closedIncl
      (hnat := stalkPush_nat_closedIncl
        (TopCat.closedIncl hs) S.g.val z)
      hg_surj
  · intro b
    rw [pushforward_stalk_zero_closedIncl hs x hx S.X₃ b]
    exact ⟨0, AddMonoidHom.map_zero _⟩

/-- Pushforward along a closed immersion preserves short exactness. -/
theorem closedIncl_pushforward_shortExact
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s))}
    (hSE : S.ShortExact) :
    (S.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs))).ShortExact := by
  haveI : Mono S.f := hSE.mono_f
  haveI : Mono ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map S.f) :=
    Functor.map_mono _ _
  have hExact : (S.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs))).Exact :=
    hSE.exact.map_of_mono_of_preservesKernel _ hSE.mono_f inferInstance
  haveI : Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map S.g) :=
    closedIncl_pushforward_epi_g hs hSE
  exact ShortComplex.ShortExact.mk' hExact ‹_› ‹_›


/-- If both ends of a short exact sequence have vanishing `H^n`, so does the middle term. -/
theorem subsingleton_sheafH_of_shortExact_middle {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₁ : Subsingleton (Sheaf.H S.X₁ n))
    (h₃ : Subsingleton (Sheaf.H S.X₃ n)) :
    Subsingleton (Sheaf.H S.X₂ n) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₂ _ hS a
    (@Subsingleton.elim _ ((add_zero n) ▸ h₃) _ _)
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₂ _ hS b
    (@Subsingleton.elim _ ((add_zero n) ▸ h₃) _ _)
  rw [← hc, ← hd, @Subsingleton.elim _ h₁ c d]

/-! ### pushforwardHVanishing sub-lemmas -/

/-- Base case of `pushforwardHVanishing`: the pushforward preserves `H^0` vanishing
by comparing global sections `Γ_X(i_* G') = G'(⊤_Z) = Γ_Z(G')`. -/
lemma pushforwardHVanishing_zero
    {X : TopCat.{u}} {Z : Set X} (_hZ : IsClosed Z) [NoetherianSpace X]
    (G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))
    (hG' : Subsingleton (Sheaf.H G' 0)) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G') 0) := by
  intro i; let F' := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G'
  have hsec : Subsingleton (G'.val.obj (op ⊤)) := by
    letI := hG'; exact subsingleton_of_addEquiv (sheafH0EquivSections G')
  have hobj : F'.val.obj (op ⊤) = G'.val.obj (op ⊤) := by
    change G'.val.obj (op ((Opens.map i).obj ⊤)) = G'.val.obj (op ⊤)
    simp [show ((Opens.map i).obj ⊤ : Opens (TopCat.of Z)) = ⊤ from by ext; simp [Opens.map]]
  constructor; intro a b
  apply (sheafH0EquivSections F').injective
  exact @Subsingleton.elim (F'.val.obj (op ⊤)) (hobj ▸ hsec) _ _

/-- Helper: if `z.comp(mk₀(g)) = mk₀(φ)` in `Ext^0`, then `addEquiv₀(z) ≫ g = φ` as morphisms. -/
lemma ext0_comp_eq_of_covariant
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

/-- If `H^1(S.X₁) = 0` in a short exact sequence, then `g` evaluated at `⊤` is epi.
Proved via the covariant Ext LES, adjunction, and projectivity of `ULift ℤ`. -/
theorem epi_g_app_top_of_H1_vanishing
    {Z : TopCat.{u}} [NoetherianSpace Z]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} Z)}
    (hSE : S.ShortExact)
    (hX₁ : Subsingleton (Sheaf.H S.X₁ 1)) :
    Epi (S.g.val.app (op ⊤)) := by
  rw [AddCommGrpCat.epi_iff_surjective]; intro r
  let R_top := S.X₃.val.obj (op ⊤)
  let φ_hom : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ R_top :=
    AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun (n : ULift.{u} ℤ) => (n.down : ℤ) • (r : R_top))
        (fun a b => by simp [add_zsmul]))
  let adj_Z := constantSheafAdj (Opens.grothendieckTopology Z)
    AddCommGrpCat.{u} Limits.isTerminalTop
  let φ := (adj_Z.homEquiv _ S.X₃).symm φ_hom
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hSE _ rfl
    (@Subsingleton.elim _ hX₁ _ _)
  have hψ : Ext.addEquiv₀ z ≫ S.g = φ :=
    ext0_comp_eq_of_covariant S.g z φ hz
  let ψ_hom := (adj_Z.homEquiv _ S.X₂) (Ext.addEquiv₀ z)
  have hfact := Adjunction.homEquiv_naturality_right adj_Z (Ext.addEquiv₀ z) S.g
  rw [hψ, Equiv.apply_symm_apply] at hfact
  change φ_hom = ψ_hom ≫ S.g.val.app (op ⊤) at hfact
  refine ⟨ψ_hom (ULift.up 1), ?_⟩
  change (ConcreteCategory.hom (ψ_hom ≫ S.g.val.app (op ⊤))) (ULift.up 1) = r
  rw [← hfact]; simp [φ_hom]

/-- Surjectivity of the `Ext^0` map from epimorphism of `g` at global sections,
via adjunction and projectivity of `ULift ℤ`. -/
theorem ext0_surj_of_epi_top
    {X : TopCat.{u}} [NoetherianSpace X]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hg_epi_top : Epi (S.g.val.app (op ⊤))) :
    ∀ y : Sheaf.H S.X₃ 0,
      ∃ z : Sheaf.H S.X₂ 0,
        z.comp (Ext.mk₀ S.g) (add_zero 0) = y := by
  intro y; suffices ∃ ψ : _ ⟶ S.X₂, ψ ≫ S.g = Ext.addEquiv₀ y by
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

/-- **Pushforward preserves cohomological vanishing.** If `H^n(G) = 0` on the closed subspace `Z`,
then `H^n(i_* G) = 0` on `X`. Proved by induction: `n=0` via sections, `n=1` via Ext^0
surjectivity, `n ≥ 2` via LES dimension shift. -/
theorem pushforwardHVanishing
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    [NoetherianSpace X]
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)) (n : ℕ)
    (h : Subsingleton (Sheaf.H G n)) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) n) := by
  intro i; suffices ∀ (m : ℕ) (G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)),
      Subsingleton (Sheaf.H G' m) →
      Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G') m) from
    this n G h
  intro m; induction m with
  | zero => exact pushforwardHVanishing_zero hZ
  | succ k ih_push =>
    intro G' hG'
    obtain ⟨ip⟩ := EnoughInjectives.presentation G'
    have hSE_X : (ip.shortComplex.map
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)).ShortExact :=
      closedIncl_pushforward_shortExact hZ ip.shortExact_shortComplex
    have hFlasque : IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat i).obj
        ip.shortComplex.X₂) :=
      pushforward_preserves_flasque i _ (isFlasque_of_injective ip.shortComplex.X₂)
    cases k with
    | zero =>
      exact subsingleton_H1_via_surj _ hSE_X (flasqueVanishing _ _ hFlasque 0)
        (ext0_surj_of_epi_top (by
          show Epi (ip.shortComplex.g.val.app (op ((Opens.map i).obj ⊤)))
          rw [show ((Opens.map i).obj ⊤ : Opens (TopCat.of Z)) = ⊤ from by ext; simp [Opens.map]]
          exact epi_g_app_top_of_H1_vanishing ip.shortExact_shortComplex hG'))
    | succ m =>
      exact ext_dimension_shift _ hSE_X (m + 1)
        (ih_push ip.shortComplex.X₃ (ext_dimension_shift_X₃ _ ip.shortExact_shortComplex (m + 1)
          (Ext.subsingleton_of_injective _ _ m) hG'))
        (flasqueVanishing _ _ hFlasque (m + 1))

/-- Degree-0 pushforward isomorphism: `H^0(X, i_*F) ≃+ H^0(Z, F)` via sections comparison. -/
noncomputable def pushforwardH0Iso
    {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) [NoetherianSpace X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)) :
    let i := TopCat.closedIncl hZ
    let h : ((Opens.map i).obj ⊤ : Opens (TopCat.of Z)) = ⊤ := by ext; simp [Opens.map]
    Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F) 0 ≃+ Sheaf.H F 0 := by
  intro i h; subst h
  exact (sheafH0EquivSections _).trans (sheafH0EquivSections F).symm

/-- Reverse naturality of `sheafH0EquivSections`: composing `sheafH0.symm` with `mk₀ f`
    equals applying `f.app(⊤)` then `sheafH0.symm`. -/
lemma sheafH0EquivSections_symm_natural {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (a : F.val.obj (op ⊤)) :
    ((sheafH0EquivSections F).symm a).comp (Ext.mk₀ f) (add_zero 0) =
    (sheafH0EquivSections G).symm (ConcreteCategory.hom (f.val.app (op ⊤)) a) := by
  apply (sheafH0EquivSections G).injective
  erw [AddEquiv.apply_symm_apply, sheafH0EquivSections_natural, AddEquiv.apply_symm_apply]

/-- After naturality rewrites, the sections-level maps agree:
    `(push.map f).app(⊤)(a) = f.app(⊤)(sheafH0(F)(sheafH0(F).symm(a)))`. -/
lemma pushforwardH0Iso_natural_step3
    {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) [NoetherianSpace X]
    {F G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)} (f : F ⟶ G)
    (a : ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hZ)).obj F).val.obj (op ⊤)) :
    ConcreteCategory.hom (((TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ)).map f).val.app (op ⊤)) a =
    ConcreteCategory.hom (f.val.app (op ⊤))
      ((sheafH0EquivSections F) ((sheafH0EquivSections F).symm a)) := by
  erw [AddEquiv.apply_symm_apply]; rfl

/-- `pushforwardH0Iso` is natural: commutes with morphisms of sheaves.
    Proved by `subst` on the Opens.map equality + `sheafH0EquivSections_natural` + `rfl`. -/
lemma pushforwardH0Iso_natural
    {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) [NoetherianSpace X]
    {F G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)} (f : F ⟶ G)
    (x : Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hZ)).obj F) 0) :
    pushforwardH0Iso hZ G (x.comp (Ext.mk₀ ((TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ)).map f)) (add_zero 0)) =
    (pushforwardH0Iso hZ F x).comp (Ext.mk₀ f) (add_zero 0) := by
  show pushforwardH0Iso hZ G _ = _
  unfold pushforwardH0Iso
  simp only [id, AddEquiv.trans_apply]
  -- Apply sheafH0(G).injective, use naturality lemmas on both sides.
  apply (sheafH0EquivSections G).injective
  erw [AddEquiv.apply_symm_apply]
  -- Goal: sheafH0(i_*G)(x.comp(mk₀(push.map f))) = sheafH0(G)(RHS.comp(mk₀ f))
  erw [sheafH0EquivSections_natural
    ((TopCat.Sheaf.pushforward AddCommGrpCat (TopCat.closedIncl hZ)).map f) x]
  -- Goal: (push.map f).app(⊤)(sheafH0(i_*F)(x)) = sheafH0(G)(RHS.comp(mk₀ f))
  -- Use pre-computed naturality to avoid heartbeat overflow from erw.
  have h2 := sheafH0EquivSections_natural f
    ((sheafH0EquivSections F).symm
      ((sheafH0EquivSections ((TopCat.Sheaf.pushforward AddCommGrpCat
        (TopCat.closedIncl hZ)).obj F)) x))
  erw [h2]; exact pushforwardH0Iso_natural_step3 hZ f _

/-- Kernel compatibility (forward): if `δ_X(x) = 0` then `δ_Z(pushH0(x)) = 0`.
    Uses `pushforwardH0Iso_natural` + `comp_extClass`. -/
lemma pushforwardH1Iso_ker_fwd
    {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) [NoetherianSpace X]
    {G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)}
    (ip : InjectivePresentation G')
    (hSE_X : (ip.shortComplex.map (TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ))).ShortExact)
    (hSE_Z : ip.shortComplex.ShortExact)
    (x : Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ)).obj ip.shortComplex.X₃) 0)
    (hx : x.comp hSE_X.extClass rfl = 0) :
    (pushforwardH0Iso hZ ip.shortComplex.X₃ x).comp hSE_Z.extClass rfl = 0 := by
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hSE_X x rfl hx
  show (pushforwardH0Iso hZ _ _).comp hSE_Z.extClass rfl = 0
  rw [hz.symm]; erw [pushforwardH0Iso_natural hZ ip.shortComplex.g z]
  rw [Ext.comp_assoc_of_second_deg_zero, hSE_Z.comp_extClass, Ext.comp_zero]

/-- Naturality of `pushforwardH0Iso` composed with `.symm`: applying `pushH0` to
    `(pushH0.symm y).comp(mk₀(push.map f))` yields `y.comp(mk₀ f)`. -/
lemma pushforwardH0Iso_symm_comp
    {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) [NoetherianSpace X]
    {F G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)} (f : F ⟶ G)
    (y : Sheaf.H F 0) :
    pushforwardH0Iso hZ G (((pushforwardH0Iso hZ F).symm y).comp
      (Ext.mk₀ ((TopCat.Sheaf.pushforward AddCommGrpCat
        (TopCat.closedIncl hZ)).map f)) (add_zero 0)) =
    y.comp (Ext.mk₀ f) (add_zero 0) := by
  erw [pushforwardH0Iso_natural hZ f]; rw [AddEquiv.apply_symm_apply]

/-- Kernel compatibility (backward): if `δ_Z(pushH0(x)) = 0` then `δ_X(x) = 0`.
    Uses `pushforwardH0Iso_symm_comp` + `comp_extClass`. -/
lemma pushforwardH1Iso_ker_bwd
    {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) [NoetherianSpace X]
    {G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)}
    (ip : InjectivePresentation G')
    (hSE_X : (ip.shortComplex.map (TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ))).ShortExact)
    (hSE_Z : ip.shortComplex.ShortExact)
    (x : Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ)).obj ip.shortComplex.X₃) 0)
    (hx : (pushforwardH0Iso hZ ip.shortComplex.X₃ x).comp hSE_Z.extClass rfl = 0) :
    x.comp hSE_X.extClass rfl = 0 := by
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ _ hSE_Z _ rfl hx
  have : x = ((pushforwardH0Iso hZ ip.shortComplex.X₂).symm y).comp
      (Ext.mk₀ (ip.shortComplex.map (TopCat.Sheaf.pushforward _
        (TopCat.closedIncl hZ))).g) (add_zero 0) :=
    (pushforwardH0Iso hZ ip.shortComplex.X₃).injective
      (pushforwardH0Iso_symm_comp hZ ip.shortComplex.g y ▸ hy.symm)
  rw [this, Ext.comp_assoc_of_second_deg_zero, hSE_X.comp_extClass, Ext.comp_zero]

/-- Additivity helper for `pushforwardH1Iso`: the lift-then-compose map is additive. -/
lemma pushforwardH1Iso_add
    {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) [NoetherianSpace X]
    {G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)}
    (ip : InjectivePresentation G')
    (hSE_X : (ip.shortComplex.map (TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ))).ShortExact)
    (hSE_Z : ip.shortComplex.ShortExact)
    (hFlasque : IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ)).obj ip.shortComplex.X₂))
    (a b : Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hZ)).obj G') 1) :
    let hX1 := flasqueVanishing _ _ hFlasque 0
    let liftX := fun c => (Ext.covariant_sequence_exact₁ _ hSE_X c
      (@Subsingleton.elim _ hX1 _ _) rfl).choose
    let φ : AddMonoidHom _ _ := (AddMonoidHom.mk'
      (fun x => x.comp hSE_Z.extClass rfl)
      (fun a b => Ext.add_comp a b hSE_Z.extClass rfl)).comp
      (pushforwardH0Iso hZ ip.shortComplex.X₃).toAddMonoidHom
    φ (liftX (a + b)) = φ (liftX a) + φ (liftX b) := by
  intro hX1 liftX φ
  have hlX : ∀ c, (liftX c).comp hSE_X.extClass rfl = c := fun c =>
    (Ext.covariant_sequence_exact₁ _ hSE_X c (@Subsingleton.elim _ hX1 _ _) rfl).choose_spec
  rw [← map_add]
  have : (liftX (a + b) - (liftX a + liftX b)).comp hSE_X.extClass rfl = 0 := by
    rw [show liftX (a + b) - (liftX a + liftX b) = liftX (a + b) + (-(liftX a + liftX b)) from
      sub_eq_add_neg _ _, Ext.add_comp, Ext.neg_comp, Ext.add_comp, hlX, hlX, hlX, add_neg_cancel]
  exact sub_eq_zero.mp (show φ (liftX (a + b)) - φ (liftX a + liftX b) = 0 from by
    rw [← map_sub]; exact pushforwardH1Iso_ker_fwd hZ ip hSE_X hSE_Z _ this)

/-- Injectivity helper for `pushforwardH1Iso`. -/
lemma pushforwardH1Iso_inj
    {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) [NoetherianSpace X]
    {G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)}
    (ip : InjectivePresentation G')
    (hSE_X : (ip.shortComplex.map (TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ))).ShortExact)
    (hSE_Z : ip.shortComplex.ShortExact)
    (hFlasque : IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ)).obj ip.shortComplex.X₂))
    {a b : Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hZ)).obj G') 1}
    (hab : let hX1 := flasqueVanishing _ _ hFlasque 0
      let liftX := fun c => (Ext.covariant_sequence_exact₁ _ hSE_X c
        (@Subsingleton.elim _ hX1 _ _) rfl).choose
      let φ : AddMonoidHom _ _ := (AddMonoidHom.mk'
        (fun x => x.comp hSE_Z.extClass rfl)
        (fun a b => Ext.add_comp a b hSE_Z.extClass rfl)).comp
        (pushforwardH0Iso hZ ip.shortComplex.X₃).toAddMonoidHom
      φ (liftX a) = φ (liftX b)) :
    a = b := by
  let hX1 := flasqueVanishing _ _ hFlasque 0
  let liftX := fun c => (Ext.covariant_sequence_exact₁ _ hSE_X c
    (@Subsingleton.elim _ hX1 _ _) rfl).choose
  have hlX : ∀ c, (liftX c).comp hSE_X.extClass rfl = c := fun c =>
    (Ext.covariant_sequence_exact₁ _ hSE_X c (@Subsingleton.elim _ hX1 _ _) rfl).choose_spec
  let φ : AddMonoidHom _ _ := (AddMonoidHom.mk'
    (fun x => x.comp hSE_Z.extClass rfl)
    (fun a b => Ext.add_comp a b hSE_Z.extClass rfl)).comp
    (pushforwardH0Iso hZ ip.shortComplex.X₃).toAddMonoidHom
  have h1 : (liftX a - liftX b).comp hSE_X.extClass rfl = 0 :=
    pushforwardH1Iso_ker_bwd hZ ip hSE_X hSE_Z _ (by
      show φ (liftX a - liftX b) = 0; rw [map_sub]; exact sub_eq_zero.mpr hab)
  rw [← hlX a, ← hlX b]
  rw [show liftX a - liftX b = liftX a + -(liftX b) from sub_eq_add_neg _ _,
    Ext.add_comp, Ext.neg_comp] at h1
  have := add_eq_zero_iff_eq_neg.mp h1
  rwa [neg_neg] at this

/-- Surjectivity helper for `pushforwardH1Iso`. -/
lemma pushforwardH1Iso_surj
    {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) [NoetherianSpace X]
    {G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)}
    (ip : InjectivePresentation G')
    (hSE_X : (ip.shortComplex.map (TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ))).ShortExact)
    (hSE_Z : ip.shortComplex.ShortExact)
    (hFlasque : IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ)).obj ip.shortComplex.X₂))
    (b : Sheaf.H G' 1) :
    let hX1 := flasqueVanishing _ _ hFlasque 0
    let hZ1 := Ext.subsingleton_of_injective
      ((constantSheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) ip.shortComplex.X₂ 0
    let liftX := fun c => (Ext.covariant_sequence_exact₁ _ hSE_X c
      (@Subsingleton.elim _ hX1 _ _) rfl).choose
    let φ : AddMonoidHom _ _ := (AddMonoidHom.mk'
      (fun x => x.comp hSE_Z.extClass rfl)
      (fun a b => Ext.add_comp a b hSE_Z.extClass rfl)).comp
      (pushforwardH0Iso hZ ip.shortComplex.X₃).toAddMonoidHom
    ∃ a, φ (liftX a) = b := by
  intro hX1 hZ1 liftX φ
  have hlX : ∀ c, (liftX c).comp hSE_X.extClass rfl = c := fun c =>
    (Ext.covariant_sequence_exact₁ _ hSE_X c (@Subsingleton.elim _ hX1 _ _) rfl).choose_spec
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hSE_Z b
    (@Subsingleton.elim _ hZ1 _ _) rfl
  refine ⟨((pushforwardH0Iso hZ ip.shortComplex.X₃).symm y).comp hSE_X.extClass rfl, ?_⟩
  show φ (liftX _) = b
  -- Cast liftX _ to Sheaf.H type to match pushH0.symm y (definitionally equal types)
  let a := ((pushforwardH0Iso hZ ip.shortComplex.X₃).symm y).comp hSE_X.extClass rfl
  let z : Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ)).obj ip.shortComplex.X₃) 0 := liftX a
  have h1 : (z + -((pushforwardH0Iso hZ ip.shortComplex.X₃).symm y)).comp
      hSE_X.extClass rfl = 0 := by
    rw [Ext.add_comp, Ext.neg_comp, hlX, add_neg_cancel]
  have h2 := pushforwardH1Iso_ker_fwd hZ ip hSE_X hSE_Z _ h1
  -- h2 : φ(z + -(pushH0.symm y)) = 0. Since φ is AddMonoidHom:
  have h3 : φ z = φ ((pushforwardH0Iso hZ ip.shortComplex.X₃).symm y) := by
    have : φ z + -(φ ((pushforwardH0Iso hZ ip.shortComplex.X₃).symm y)) = 0 := by
      rw [← map_neg, ← map_add]; exact h2
    have := add_eq_zero_iff_eq_neg.mp this
    rwa [neg_neg] at this
  rw [show φ (liftX a) = φ z from rfl, h3]
  show (pushforwardH0Iso hZ ip.shortComplex.X₃
    ((pushforwardH0Iso hZ ip.shortComplex.X₃).symm y)).comp hSE_Z.extClass rfl = b
  rw [AddEquiv.apply_symm_apply]; exact hy

/-- **Pushforward H^1 isomorphism**: assembles the three pieces. -/
noncomputable def pushforwardH1Iso
    {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) [NoetherianSpace X]
    {G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)}
    (ip : InjectivePresentation G')
    (hSE_X : (ip.shortComplex.map (TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ))).ShortExact)
    (hSE_Z : ip.shortComplex.ShortExact)
    (hFlasque : IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.closedIncl hZ)).obj ip.shortComplex.X₂)) :
    Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hZ)).obj G') 1 ≃+ Sheaf.H G' 1 :=
  let hX1 := flasqueVanishing _ _ hFlasque 0
  let liftX := fun c => (Ext.covariant_sequence_exact₁ _ hSE_X c
    (@Subsingleton.elim _ hX1 _ _) rfl).choose
  let φ : AddMonoidHom _ _ := (AddMonoidHom.mk'
    (fun x => x.comp hSE_Z.extClass rfl)
    (fun a b => Ext.add_comp a b hSE_Z.extClass rfl)).comp
    (pushforwardH0Iso hZ ip.shortComplex.X₃).toAddMonoidHom
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun a => φ (liftX a))
      (pushforwardH1Iso_add hZ ip hSE_X hSE_Z hFlasque))
    ⟨fun {a b} hab => pushforwardH1Iso_inj hZ ip hSE_X hSE_Z hFlasque
      (show _ from hab),
    fun b => pushforwardH1Iso_surj hZ ip hSE_X hSE_Z hFlasque b⟩

/-- **Pushforward isomorphism**: `H^n(X, i_*G) ≃+ H^n(Z, G)` for closed immersions.
    The pushforward along a closed immersion preserves cohomology, not just vanishing.
    Base case: sections comparison `Γ(X, i_*G) = Γ(Z, G)`.
    Inductive step: dimension shifting via the connecting map isomorphism. -/
noncomputable def pushforwardHIso
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    [NoetherianSpace X]
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)) (n : ℕ) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) n ≃+
    Sheaf.H G n := by
  intro i
  suffices ∀ (m : ℕ) (G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)),
      Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G') m ≃+
      Sheaf.H G' m from this n G
  intro m; induction m with
  | zero =>
    intro G'; let F' := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G'
    have hobj : F'.val.obj (op ⊤) = G'.val.obj (op ⊤) := by
      change G'.val.obj (op ((Opens.map i).obj ⊤)) = G'.val.obj (op ⊤)
      simp [show ((Opens.map i).obj ⊤ : Opens (TopCat.of Z)) = ⊤ from by ext; simp [Opens.map]]
    exact (sheafH0EquivSections F').trans (hobj ▸ (sheafH0EquivSections G').symm)
  | succ k ih_push =>
    intro G'
    let ip := Classical.choice (EnoughInjectives.presentation G')
    have hSE_X := closedIncl_pushforward_shortExact hZ ip.shortExact_shortComplex
    have hFlasque : IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat i).obj
        ip.shortComplex.X₂) :=
      pushforward_preserves_flasque i ip.shortComplex.X₂
        (isFlasque_of_injective ip.shortComplex.X₂)
    have hSE_Z := ip.shortExact_shortComplex
    cases k with
    | zero =>
      exact pushforwardH1Iso hZ ip hSE_X hSE_Z hFlasque
    | succ m =>
      -- H^{m+2}: dimension shift connecting map isomorphism
      exact (ext_dimension_shift_addEquiv _ hSE_X (m + 1)
          (flasqueVanishing _ _ hFlasque m) (flasqueVanishing _ _ hFlasque (m + 1))).symm.trans
        ((ih_push ip.shortComplex.X₃).trans
          (ext_dimension_shift_addEquiv _ hSE_Z (m + 1)
            (Ext.subsingleton_of_injective _ _ m) (Ext.subsingleton_of_injective _ _ (m + 1))))

/-- The adjunction unit `F → i_*(i^*F)` is epi for closed immersions. Stalkwise:
on `Z` the stalk map is an iso (by `closedIncl_unit_stalk_isIso`), and outside `Z`
the target stalk is zero. -/
theorem epi_unit_of_closedImmersion
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    [NoetherianSpace X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i
    Epi (adj.unit.app F) := by
  intro i adj
  rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} (adj.unit.app F),
    show Sheaf.IsLocallySurjective (adj.unit.app F) =
      TopCat.Presheaf.IsLocallySurjective (adj.unit.app F).val from rfl,
    TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x; by_cases hxZ : (x : X) ∈ Z
  · -- x ∈ Z: stalk map is surjective (it's an iso)
    haveI := TopCat.closedIncl_unit_stalk_isIso hZ F ⟨x, hxZ⟩
    exact (ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} ((TopCat.closedIncl hZ) ⟨x, hxZ⟩)).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          (TopCat.closedIncl hZ)).unit.app F).val)).2
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
      rw [show (Opens.map i).obj V'_nhd.1 = ⊥ from le_antisymm (fun ⟨_, hy⟩ hmem => by
        simp only [Opens.map, Opens.mem_mk] at hmem; exact absurd hy (hmem.2 ·)) bot_le]
      exact (isTerminal_sheaf_bot _).isZero
    -- The stalk is IsZero → surjective
    exact fun b => ⟨0, by simp [(@Subsingleton.elim _
      (AddCommGrpCat.subsingleton_of_isZero hstalk_zero) b 0).symm]⟩

/-- Short exact sequence from a closed immersion: `0 → ker(η) → F → i_*(i^*F) → 0`
where `η` is the adjunction unit. -/
theorem closedImmersionSES
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
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i
  let η := adj.unit.app F
  haveI : Epi η := epi_unit_of_closedImmersion Z hZ F
  exact ⟨ShortComplex.mk (kernel.ι η) η (kernel.condition η), shortExact_of_epi η, rfl, rfl⟩

/-- Vanishing for a sheaf supported on the complement of an open V, via closed-immersion SES.
    Given:
    - C is a sheaf on irreducible Noetherian X
    - V ≠ ⊥ is an open with n > dim X
    - IH gives vanishing on all spaces of smaller dimension
    - Stalks of C vanish at all points of V (the `hStalksOnV` hypothesis)
    Concludes H^n(C) = 0 by building the SES on Y = Vᶜ. -/
theorem closedComplementVanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (hV : V ≠ ⊥)
    (C : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (hn : ↑n > topologicalKrullDim X)
    (ih : VanishingIH (X := X))
    (hStalksOnV : ∀ x ∈ V,
      ∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj C.val), a = 0) :
    Subsingleton (Sheaf.H C n) := by
  set Y := (V : Set X)ᶜ
  have hYcl : IsClosed Y := V.2.isClosed_compl
  have hY_dim_lt : topologicalKrullDim Y < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl (compl_ne_univ_of_ne_bot hV)
      (lt_of_le_of_lt (topologicalKrullDim_subspace_le (X := (↑X : Type u)) Y)
        (lt_of_lt_of_le hn le_top))
  let i : TopCat.of Y ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app C
  haveI : Epi η := epi_unit_of_closedImmersion Y hYcl C
  let S := ShortComplex.mk (kernel.ι η) η (kernel.condition η)
  have hSE : S.ShortExact := shortExact_of_epi η
  exact subsingleton_sheafH_of_shortExact_middle hSE n
    (by apply subsingleton_sheafH_of_isZero'; apply sheaf_isZero_of_zero_stalks X; intro x a
        by_cases hxY : x ∈ Y
        · haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val) :=
            TopCat.closedIncl_unit_stalk_isIso hYcl C ⟨x, hxY⟩
          exact stalk_zero_of_ses_g_iso hSE x inferInstance a
        · exact stalk_zero_of_shortExact_kernel hSE x
            (fun b => hStalksOnV x (by rwa [Set.mem_compl_iff, not_not] at hxY) b) a)
    (pushforwardHVanishing Y hYcl _ n
      (@ih (TopCat.of Y) _ n _ hY_dim_lt (lt_trans hY_dim_lt hn)))
