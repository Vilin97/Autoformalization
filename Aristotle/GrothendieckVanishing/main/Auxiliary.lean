/-
  Auxiliary.lean — Topology and dimension helper lemmas

  Key results:
  - On irreducible spaces of dimension 0, the only opens are ⊥ and ⊤
  - Any morphism to a terminal object in an abelian category is epi
  - F(⊥) is terminal for any sheaf F on a topological space
-/
import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits

/-! ## Abelian category helpers -/

/-- In an abelian category, any morphism to a terminal (= zero) object is epi. -/
theorem epi_of_isTerminal_tgt {C : Type*} [Category C] [Abelian C] {X Y : C}
    (t : IsTerminal Y) (f : X ⟶ Y) : Epi f := by
  have hzero : IsZero Y := by
    rw [IsZero.iff_id_eq_zero]
    exact t.hom_ext _ _
  constructor
  intro Z g h _
  have hg : g = 0 := hzero.eq_of_src g 0
  have hh : h = 0 := hzero.eq_of_src h 0
  rw [hg, hh]

/-! ## Sheaf at the empty open set -/

/-- For any sheaf F on a topological space, F(⊥) = F(∅) is a terminal object.
    This follows from the sheaf condition on the empty cover. -/
noncomputable def isTerminal_sheaf_bot {X : Type u} [TopologicalSpace X]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    IsTerminal (F.val.obj (Opposite.op ⊥)) := by
  apply Sheaf.isTerminalOfBotCover
  intro x hx
  exact (Opens.mem_bot.mp hx).elim

/-! ## Irreducible spaces of dimension 0 -/

/-- On an irreducible space with topologicalKrullDim ≤ 0, every irreducible closed set
    equals the whole space. -/
theorem irreducibleCloseds_unique_of_dim_zero {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 0)
    (S : IrreducibleCloseds X) : (S : Set X) = Set.univ := by
  have hmax := (Order.krullDim_nonpos_iff_forall_isMax).mp hdim S
  have hle : S ≤ ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ :=
    Set.subset_univ _
  exact le_antisymm (Set.subset_univ _) (hmax hle)

/-- On an irreducible space of dimension 0, every point is dense. -/
theorem closure_singleton_eq_univ_of_dim_zero {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 0)
    (x : X) : closure ({x} : Set X) = Set.univ :=
  irreducibleCloseds_unique_of_dim_zero hdim
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- On an irreducible space of dimension ≤ 0, the only opens are ⊥ and ⊤.
    Every point is dense, so any nonempty open contains every point. -/
theorem opens_eq_bot_or_top_of_irreducibleSpace_dim_zero
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 0) (U : Opens X) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hne : (U : Set X).Nonempty
  · right
    ext x
    constructor
    · exact fun _ => trivial
    · intro _
      by_contra hx
      have hcl := closure_singleton_eq_univ_of_dim_zero hdim x
      have hsub : closure ({x} : Set X) ⊆ (U : Set X)ᶜ :=
        closure_minimal (Set.singleton_subset_iff.mpr hx) U.isOpen.isClosed_compl
      rw [hcl] at hsub
      obtain ⟨y, hy⟩ := hne
      exact hsub (Set.mem_univ y) hy
  · left
    exact Opens.ext (Set.not_nonempty_iff_eq_empty.mp hne)

/-- Every nonempty open subset of an irreducible space is irreducible. -/
theorem isIrreducible_of_nonempty_open {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] (W : Opens X) (hW : (W : Set X).Nonempty) :
    IsIrreducible (W : Set X) :=
  (IrreducibleSpace.isIrreducible_univ X).isPreirreducible.subset_irreducible
    hW W.isOpen le_rfl (Set.subset_univ _)

/-! ## Dimension helpers -/

/-- On an irreducible space, the topological Krull dimension is ≥ 0. -/
theorem topologicalKrullDim_nonneg_of_irreducible {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] : topologicalKrullDim X ≥ 0 := by
  rw [topologicalKrullDim, ge_iff_le, Order.krullDim_nonneg_iff]
  exact ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩

/-- The image of the map from IrreducibleCloseds Y to IrreducibleCloseds X
    is contained in Y when Y is closed. -/
private lemma map_subtype_carrier_subset {X : Type u} [TopologicalSpace X]
    {Y : Set X} (hY : IsClosed Y) (s : IrreducibleCloseds Y) :
    (IrreducibleCloseds.map (Subtype.val : Y → X) continuous_subtype_val s).carrier ⊆ Y := by
  show closure (Subtype.val '' s.carrier) ⊆ Y
  apply closure_minimal _ hY
  rintro x ⟨⟨y, hy⟩, _, rfl⟩
  exact hy

/-- Every element in the image of IrreducibleCloseds Y → IrreducibleCloseds X
    is strictly below the whole space X, when Y ⊊ X. -/
private lemma map_subtype_lt_top {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    {Y : Set X} (hY : IsClosed Y) (hne : Y ≠ Set.univ)
    (s : IrreducibleCloseds Y) :
    IrreducibleCloseds.map (Subtype.val : Y → X) continuous_subtype_val s <
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ := by
  refine lt_of_le_of_ne ?_ ?_ <;> simp_all +decide [IrreducibleCloseds.map]
  · exact Set.subset_univ _
  · rw [Set.eq_univ_iff_forall] at *; contrapose! hne; aesop

/-- For each s : IrreducibleCloseds Y, height(s) + 1 ≤ topologicalKrullDim X. -/
private lemma height_add_one_le_dim {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    {Y : Set X} (hY : IsClosed Y) (hne : Y ≠ Set.univ)
    (s : IrreducibleCloseds Y) :
    (Order.height s : WithBot ℕ∞) + 1 ≤ topologicalKrullDim X := by
  set f : IrreducibleCloseds Y → IrreducibleCloseds X :=
    IrreducibleCloseds.map (Subtype.val : Y → X) continuous_subtype_val
  have hf_strict : StrictMono f :=
    IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  have h_height_le : Order.height s ≤ Order.height (f s) :=
    Order.height_le_height_apply_of_strictMono f hf_strict s
  have h_height_add_one : (Order.height (f s) : WithBot ℕ∞) + 1 ≤
      (Order.height (⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ :
        IrreducibleCloseds X)) := by
    convert Order.height_add_one_le (map_subtype_lt_top hY hne s)
    norm_cast
  refine le_trans ?_ (h_height_add_one.trans ?_)
  · gcongr; norm_cast
  · convert Order.height_le_krullDim _

private lemma iSup_height_add_one_eq {Y : Type u} [TopologicalSpace Y]
    [Nonempty (IrreducibleCloseds Y)] :
    (⨆ s : IrreducibleCloseds Y, (Order.height s : WithBot ℕ∞)) + 1 =
    ⨆ s : IrreducibleCloseds Y, ((Order.height s : WithBot ℕ∞) + 1) := by
  have bdd : BddAbove (Set.range (fun s : IrreducibleCloseds Y => Order.height s)) :=
    OrderTop.bddAbove _
  conv_lhs =>
    rw [show (⨆ s : IrreducibleCloseds Y, (Order.height s : WithBot ℕ∞)) =
        ↑(⨆ s, Order.height s) from
      (WithBot.coe_iSup (f := fun s => Order.height s) bdd).symm]
  rw [show (↑(⨆ s, Order.height s) : WithBot ℕ∞) + 1 = ↑((⨆ s, Order.height s) + 1) from
    by push_cast; ring]
  rw [ENat.iSup_add]
  rw [WithBot.coe_iSup (f := fun s => Order.height s + 1) (OrderTop.bddAbove _)]
  simp_rw [show ∀ s : IrreducibleCloseds Y,
      (↑(Order.height s + 1 : ℕ∞) : WithBot ℕ∞) = (↑(Order.height s) : WithBot ℕ∞) + 1 from
    by intro s; push_cast; ring]

private lemma wbot_lt_of_add_one_le_of_lt_top {x y : WithBot ℕ∞}
    (h1 : x + 1 ≤ y) (h2 : x < ⊤) (h3 : ⊥ < y) : x < y := by
  rcases x with _ | v
  · exact h3
  · have hv_ne_top : v ≠ ⊤ := by intro h; subst h; exact absurd h2 (lt_irrefl _)
    have hlt : v < v + 1 := (ENat.lt_add_one_iff hv_ne_top).mpr le_rfl
    calc (↑v : WithBot ℕ∞) < ↑(v + 1) := WithBot.coe_lt_coe.mpr hlt
      _ = ↑v + 1 := by push_cast; ring
      _ ≤ y := h1

/-- Unconditional: topologicalKrullDim Y + 1 ≤ topologicalKrullDim X for
    Y ⊊ X closed in irreducible X. -/
theorem topologicalKrullDim_add_one_le_of_isIrreducible_of_isClosed {X : Type u}
    [TopologicalSpace X] [IrreducibleSpace X] {Y : Set X} (hY : IsClosed Y)
    (hne : Y ≠ Set.univ) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim X := by
  have h_le : ∀ s : IrreducibleCloseds Y,
      (Order.height s : WithBot ℕ∞) + 1 ≤ topologicalKrullDim X :=
    fun s => height_add_one_le_dim hY hne s
  rcases isEmpty_or_nonempty (IrreducibleCloseds Y) with h | h
  · simp [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  · rw [topologicalKrullDim, Order.krullDim_eq_iSup_height, iSup_height_add_one_eq]
    exact iSup_le fun s => h_le s

/-- On an irreducible space, a proper closed subset with finite Krull dimension has
    strictly smaller Krull dimension. The finiteness hypothesis excludes the case where
    both Y and X have infinite dimension. Proved by Aristotle (72e670ee). -/
theorem topologicalKrullDim_lt_of_isIrreducible_of_isClosed {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] {Y : Set X} (hY : IsClosed Y) (hne : Y ≠ Set.univ)
    (hfin : topologicalKrullDim Y < ⊤) :
    topologicalKrullDim Y < topologicalKrullDim X := by
  apply wbot_lt_of_add_one_le_of_lt_top
  · exact topologicalKrullDim_add_one_le_of_isIrreducible_of_isClosed hY hne
  · exact hfin
  · rw [topologicalKrullDim]
    have : Nonempty (IrreducibleCloseds X) :=
      ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
    exact (WithBot.bot_lt_coe _).trans_le Order.krullDim_nonneg

/-! ## Projective ULift ℤ in AddCommGrpCat -/

/-- `ULift ℤ` is projective in `AddCommGrpCat` (via the equivalence with `ModuleCat ℤ`). -/
noncomputable instance ulift_int_projective :
    Projective (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  set e := (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence with he
  have : e.inverse.PreservesEpimorphisms := by
    constructor; intro X Y f hf; exact e.symm.functor.map_epi f
  have hp := e.toAdjunction.map_projective _
    (inferInstance : Projective (ModuleCat.of ℤ (ULift.{u} ℤ)))
  simp only [he, Functor.asEquivalence, ModuleCat.forget₂_obj] at hp
  exact hp

/-! ## Covering sieve lemma for dim 0 -/

/-- On a dim 0 irreducible nonempty space, every covering sieve of ⊤ contains the identity.
    This is because the only nonempty open is ⊤ itself. -/
theorem covering_sieve_top_has_id {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 0) [Nonempty X]
    (S : Sieve (⊤ : Opens X)) (hS : S ∈ Opens.grothendieckTopology X ⊤) :
    S.arrows (𝟙 ⊤) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨V, f, hfS, hxV⟩ := hS x trivial
  have hVtop : V = ⊤ := by
    rcases opens_eq_bot_or_top_of_irreducibleSpace_dim_zero hdim V with rfl | rfl
    · simp [Opens.coe_bot] at hxV
    · rfl
  subst hVtop
  rwa [show f = 𝟙 ⊤ from Subsingleton.elim _ _] at hfS

/-! ## Epi → surjective at ⊤ on dim 0 irreducible -/

-- IsLocallySurjective typeclass resolution needs extra heartbeats
set_option maxHeartbeats 400000 in
/-- On a dim 0 irreducible nonempty space, an epi sheaf morphism is surjective at ⊤.
    Proof: epi ↔ IsLocallySurjective → imageSieve covers ⊤ → id ∈ imageSieve → surjective. -/
theorem epi_app_top_surjective {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 0) [Nonempty X]
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (ConcreteCategory.hom (φ.val.app (Opposite.op ⊤))) := by
  have hls : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} φ).mpr inferInstance
  intro s
  have hmem := hls.imageSieve_mem (U := ⊤) s
  have hid := covering_sieve_top_has_id hdim _ hmem
  obtain ⟨t, ht⟩ := hid
  exact ⟨t, by simpa using ht⟩

/-! ## Counterexample: flasque does NOT imply injective

   On X = point, every sheaf is flasque (only restriction is F(X) → F(∅) = 0),
   but ℤ is not injective in Ab (not divisible). So flasque ⟹ injective is FALSE.
   The correct result is: flasque ⟹ Γ-acyclic (Bredon).
   Proved by Aristotle (99a8a5d6). -/

/-- Every group homomorphism ℚ →+ ℤ is zero (ℤ is not divisible). -/
theorem addMonoidHom_rat_int_eq_zero (f : ℚ →+ ℤ) : f = 0 := by
  ext q; simp only [AddMonoidHom.zero_apply]
  by_contra hfq
  have key : ∀ (n : ℕ) (hn : 0 < n), (n : ℤ) ∣ f q := by
    intro n hn
    exact ⟨f (q / n), by
      have h1 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      calc f q = f (n • (q / n)) := by congr 1; rw [nsmul_eq_mul]; field_simp
        _ = n • f (q / n) := map_nsmul f n _
        _ = n * f (q / n) := nsmul_eq_mul n _⟩
  have h1 : (0 : ℤ) < |f q| := abs_pos.mpr hfq
  have h2 := key (|f q|.toNat + 1) (by omega)
  rw [show ((|f q|.toNat + 1 : ℕ) : ℤ) = |f q| + 1 from by omega] at h2
  exact absurd (Int.le_of_dvd h1 ((dvd_abs _ _).mpr h2)) (by omega)

/-- ℤ is not injective in AddCommGrpCat (counterexample to flasque → injective). -/
theorem not_injective_int : ¬ Injective (AddCommGrpCat.of ℤ) := by
  intro ⟨hext⟩
  let inc : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℚ :=
    AddCommGrpCat.ofHom (Int.castRingHom ℚ).toAddMonoidHom
  have hinc_mono : Mono inc := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab; simp [inc, AddCommGrpCat.ofHom] at hab; exact_mod_cast hab
  obtain ⟨h, hh⟩ := @hext _ _ (𝟙 (AddCommGrpCat.of ℤ)) inc hinc_mono
  have h_zero : ConcreteCategory.hom h = 0 :=
    addMonoidHom_rat_int_eq_zero (ConcreteCategory.hom h)
  have h1 : (ConcreteCategory.hom (inc ≫ h)) (1 : ℤ) = (1 : ℤ) := by rw [hh]; rfl
  simp [AddCommGrpCat.hom_comp, h_zero] at h1
