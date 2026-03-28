import Mathlib

universe u

open TopologicalSpace Order

/-- The image of the map from IrreducibleCloseds Y to IrreducibleCloseds X
    is contained in Y when Y is closed. -/
private lemma map_subtype_carrier_subset {X : Type u} [TopologicalSpace X]
    {Y : Set X} (hY : IsClosed Y) (s : IrreducibleCloseds Y) :
    (IrreducibleCloseds.map (Subtype.val : Y → X) continuous_subtype_val s).carrier ⊆ Y := by
  show closure (Subtype.val '' s.carrier) ⊆ Y
  apply closure_minimal _ hY
  rintro x ⟨⟨y, hy⟩, _, rfl⟩
  exact hy

/-- Every element in the image of the map from IrreducibleCloseds Y to
    IrreducibleCloseds X is strictly less than ⟨Set.univ, ...⟩ when Y ⊊ X. -/
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
    (height s : WithBot ℕ∞) + 1 ≤ topologicalKrullDim X := by
  set f : IrreducibleCloseds Y → IrreducibleCloseds X :=
    IrreducibleCloseds.map (Subtype.val : Y → X) continuous_subtype_val
  have h_height_le : height s ≤ height (f s) := by
    apply Order.height_le_height_apply_of_strictMono
    exact IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  have h_height_add_one : (height (f s) : WithBot ℕ∞) + 1 ≤
      (height (⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ :
        IrreducibleCloseds X)) := by
    have h_lt : f s < ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ :=
      map_subtype_lt_top hY hne s
    convert Order.height_add_one_le h_lt
    norm_cast
  refine le_trans ?_ (h_height_add_one.trans ?_)
  · gcongr; norm_cast
  · convert Order.height_le_krullDim _

private lemma iSup_height_add_one_eq {Y : Type u} [TopologicalSpace Y]
    [Nonempty (IrreducibleCloseds Y)] :
    (⨆ s : IrreducibleCloseds Y, (height s : WithBot ℕ∞)) + 1 =
    ⨆ s : IrreducibleCloseds Y, ((height s : WithBot ℕ∞) + 1) := by
  have bdd : BddAbove (Set.range (fun s : IrreducibleCloseds Y => height s)) :=
    OrderTop.bddAbove _
  conv_lhs =>
    rw [show (⨆ s : IrreducibleCloseds Y, (height s : WithBot ℕ∞)) =
        ↑(⨆ s, height s) from (WithBot.coe_iSup (f := fun s => height s) bdd).symm]
  rw [show (↑(⨆ s, height s) : WithBot ℕ∞) + 1 = ↑((⨆ s, height s) + 1) from
    by push_cast; ring]
  rw [ENat.iSup_add]
  rw [WithBot.coe_iSup (f := fun s => height s + 1) (OrderTop.bddAbove _)]
  simp_rw [show ∀ s : IrreducibleCloseds Y,
      (↑(height s + 1 : ℕ∞) : WithBot ℕ∞) = (↑(height s) : WithBot ℕ∞) + 1 from
    by intro s; push_cast; ring]

/-- In WithBot ℕ∞, if x + 1 ≤ y, x < ⊤, and ⊥ < y, then x < y. -/
private lemma wbot_lt_of_add_one_le_of_lt_top {x y : WithBot ℕ∞}
    (h1 : x + 1 ≤ y) (h2 : x < ⊤) (h3 : ⊥ < y) : x < y := by
  rcases x with _ | v
  · exact h3
  · have hv_ne_top : v ≠ ⊤ := by
      intro h; subst h; exact absurd h2 (lt_irrefl _)
    have hlt : v < v + 1 := (ENat.lt_add_one_iff hv_ne_top).mpr le_rfl
    calc (↑v : WithBot ℕ∞) < ↑(v + 1) := WithBot.coe_lt_coe.mpr hlt
      _ = ↑v + 1 := by push_cast; ring
      _ ≤ y := h1

/-- Unconditional version: topologicalKrullDim Y + 1 ≤ topologicalKrullDim X.
    This is the strongest statement that holds without finiteness assumptions. -/
theorem topologicalKrullDim_add_one_le_of_isIrreducible_of_isClosed {X : Type u}
    [TopologicalSpace X] [IrreducibleSpace X] {Y : Set X} (hY : IsClosed Y)
    (hne : Y ≠ Set.univ) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim X := by
  have h_le : ∀ s : IrreducibleCloseds Y,
      (height s : WithBot ℕ∞) + 1 ≤ topologicalKrullDim X :=
    fun s => height_add_one_le_dim hY hne s
  rcases isEmpty_or_nonempty (IrreducibleCloseds Y) with h | h
  · simp [topologicalKrullDim, krullDim_eq_iSup_height]
  · rw [topologicalKrullDim, krullDim_eq_iSup_height, iSup_height_add_one_eq]
    exact iSup_le fun s => h_le s

-- The original theorem statement is false in general when topologicalKrullDim Y = ⊤
-- (e.g., Spec(k[x₁,x₂,...]) with Y = V(x₁)), since ⊤ < ⊤ is false in WithBot ℕ∞.
-- The corrected version below adds the finiteness hypothesis topologicalKrullDim Y < ⊤.
/-
theorem topologicalKrullDim_lt_of_isIrreducible_of_isClosed_ORIGINAL {X : Type u}
    [TopologicalSpace X] [IrreducibleSpace X] {Y : Set X}
    (hY : IsClosed Y) (hne : Y ≠ Set.univ) :
    topologicalKrullDim Y < topologicalKrullDim X := by
  sorry
-/

/-- Corrected version: On an irreducible space, a proper closed subset with finite Krull
    dimension has strictly smaller Krull dimension.
    The hypothesis `topologicalKrullDim Y < ⊤` excludes the infinite-dimensional case
    where both sides equal ⊤ and strict inequality fails. -/
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
