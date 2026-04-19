import Mathlib

/-!
# Topological Krull Dimension

API for topological Krull dimension on irreducible spaces.

## Main results

- `irreducibleCloseds_unique_of_dim_zero`: on an irreducible space with dim ≤ 0,
  every irreducible closed set is the whole space
- `opens_eq_bot_or_top_of_irreducibleSpace_dim_zero`: on an irreducible dim-0 space,
  the only opens are ⊥ and ⊤
- `topologicalKrullDim_nonneg`: non-empty spaces have dim ≥ 0
- `topologicalKrullDim_lt_of_isIrreducible_of_isClosed`: proper closed subsets of
  irreducible spaces with finite dim have strictly smaller dim
- `lt_coe_nat_of_lt_of_lt_coe_nat_succ`: in `WithBot ℕ∞`, from `a < b < ↑↑(n+1)` deduce `a < ↑↑n`
- `exists_closed_subset_lt_dim_of_irreducible_pos`: on an irreducible Noetherian space of
  positive Krull dimension, there exists a proper closed subset of strictly smaller dimension
-/

universe u

open CategoryTheory TopologicalSpace Limits

/-! ## Irreducible spaces of dimension 0 -/

/-- On an irreducible space with topologicalKrullDim ≤ 0, every irreducible closed set
    equals the whole space. -/
theorem irreducibleCloseds_unique_of_dim_zero {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 0)
    (S : IrreducibleCloseds X) : (S : Set X) = Set.univ :=
  le_antisymm (Set.subset_univ _)
    ((Order.krullDim_nonpos_iff_forall_isMax).mp hdim S
      (show S ≤ ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ from
        Set.subset_univ _))

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
  · right; ext x; refine ⟨fun _ => trivial, fun _ => by_contra fun hx => ?_⟩
    have := closure_singleton_eq_univ_of_dim_zero hdim x ▸
      closure_minimal (Set.singleton_subset_iff.mpr hx) U.isOpen.isClosed_compl
    exact this (Set.mem_univ hne.some) hne.some_mem
  · exact Or.inl (Opens.ext (Set.not_nonempty_iff_eq_empty.mp hne))

/-! ## Dimension helpers -/

/-- On a non-empty topological space, the topological Krull dimension is ≥ 0. -/
theorem topologicalKrullDim_nonneg {X : Type u} [TopologicalSpace X]
    [Nonempty X] : topologicalKrullDim X ≥ 0 := by
  rw [topologicalKrullDim, ge_iff_le, Order.krullDim_nonneg_iff]
  obtain ⟨x⟩ := ‹Nonempty X›
  exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩

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
  have h_lt_top : f s < ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ := by
    refine lt_of_le_of_ne (Set.subset_univ _) fun h_eq => hne ?_
    have h_sub : (f s : Set X) ⊆ Y :=
      closure_minimal (fun _ ⟨⟨_, hy⟩, _, rfl⟩ => hy) hY
    rwa [show (f s : Set X) = Set.univ from congrArg IrreducibleCloseds.carrier h_eq,
      Set.univ_subset_iff] at h_sub
  have h_height_add_one : (Order.height (f s) : WithBot ℕ∞) + 1 ≤
      (Order.height (⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ :
        IrreducibleCloseds X)) := by
    convert Order.height_add_one_le h_lt_top
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
  rw [ENat.iSup_add, WithBot.coe_iSup (f := fun s => Order.height s + 1) (OrderTop.bddAbove _)]
  simp_rw [show ∀ s : IrreducibleCloseds Y,
      (↑(Order.height s + 1 : ℕ∞) : WithBot ℕ∞) = (↑(Order.height s) : WithBot ℕ∞) + 1 from
    by intro s; push_cast; ring]

/-- Unconditional: topologicalKrullDim Y + 1 ≤ topologicalKrullDim X for
    Y ⊊ X closed in irreducible X. -/
theorem topologicalKrullDim_add_one_le_of_isIrreducible_of_isClosed {X : Type u}
    [TopologicalSpace X] [IrreducibleSpace X] {Y : Set X} (hY : IsClosed Y)
    (hne : Y ≠ Set.univ) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim X := by
  rcases isEmpty_or_nonempty (IrreducibleCloseds Y) with h | h
  · simp [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  · rw [topologicalKrullDim, Order.krullDim_eq_iSup_height, iSup_height_add_one_eq]
    exact iSup_le (fun s => height_add_one_le_dim hY hne s)

/-- On an irreducible space, a proper closed subset with finite Krull dimension has
    strictly smaller Krull dimension. The finiteness hypothesis excludes the case where
    both Y and X have infinite dimension. Proved by Aristotle (72e670ee). -/
theorem topologicalKrullDim_lt_of_isIrreducible_of_isClosed {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] {Y : Set X} (hY : IsClosed Y) (hne : Y ≠ Set.univ)
    (hfin : topologicalKrullDim Y < ⊤) :
    topologicalKrullDim Y < topologicalKrullDim X := by
  have h1 := topologicalKrullDim_add_one_le_of_isIrreducible_of_isClosed hY hne
  generalize topologicalKrullDim Y = x at h1 hfin ⊢
  rcases x with _ | v
  · rw [topologicalKrullDim]
    have : Nonempty (IrreducibleCloseds X) :=
      ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
    exact (WithBot.bot_lt_coe _).trans_le Order.krullDim_nonneg
  · have hv_ne_top : v ≠ ⊤ := by intro h; subst h; exact absurd hfin (lt_irrefl _)
    exact lt_of_lt_of_le (show (↑v : WithBot ℕ∞) < ↑v + 1 by
      rw [← show (↑(v + 1) : WithBot ℕ∞) = ↑v + 1 from by push_cast; ring]
      exact WithBot.coe_lt_coe.mpr ((ENat.lt_add_one_iff hv_ne_top).mpr le_rfl)) h1

/-- In `WithBot ℕ∞`, if `a < b` and `b < ↑↑(n+1)`, then `a < ↑↑n`.
    Used for dimension arithmetic: from `dim Y < dim X` and `dim X < n+1`,
    conclude `dim Y < n` (predecessor step through the double coercion). -/
theorem lt_coe_nat_of_lt_of_lt_coe_nat_succ {a b : WithBot ℕ∞} {n : ℕ}
    (hab : a < b) (hbn : b < ↑↑(n + 1 : ℕ)) : a < ↑↑(n : ℕ) := by
  have hb_ne_bot : b ≠ ⊥ := ne_bot_of_gt hab
  lift b to ℕ∞ using hb_ne_bot with b'
  norm_cast at hbn ⊢
  have hb_ne_top : b' ≠ ⊤ := ne_top_of_lt hbn
  lift b' to ℕ using hb_ne_top with b''
  rw [ENat.coe_lt_coe] at hbn
  exact lt_of_lt_of_le hab (by exact_mod_cast Nat.lt_succ_iff.mp hbn)

/-- On an irreducible noetherian space of positive Krull dimension, one can choose a proper
closed subset `Z ⊊ X` of strictly smaller Krull dimension, and the ambient cohomological bound
`n > dim X` automatically implies `n > dim Z`. This isolates the closed-subset selection used at
the start of Hartshorne Step 3. -/
theorem exists_closed_subset_lt_dim_of_irreducible_pos
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X) (hpos : topologicalKrullDim X > 0) :
    ∃ Z : Set X, IsClosed Z ∧ Z ≠ Set.univ ∧
      topologicalKrullDim (TopCat.of Z) < topologicalKrullDim X ∧
      ↑n > topologicalKrullDim (TopCat.of Z) := by
  simp only [topologicalKrullDim, gt_iff_lt] at hpos
  rw [Order.krullDim_pos_iff] at hpos
  obtain ⟨a, b, hab⟩ := hpos
  have hZ_ne_univ : a.carrier ≠ Set.univ := by
    intro h; exact lt_irrefl a (lt_of_lt_of_le hab
      (show b.carrier ⊆ a.carrier from by rw [h]; exact Set.subset_univ _))
  have hZ_dim : topologicalKrullDim (TopCat.of a.carrier) < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed a.isClosed' hZ_ne_univ
      (lt_of_le_of_lt (topologicalKrullDim_subspace_le X a.carrier)
        (lt_of_lt_of_le hn le_top))
  refine ⟨a.carrier, a.isClosed', hZ_ne_univ, hZ_dim, lt_trans hZ_dim hn⟩


