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

namespace TopologicalSpace
namespace IrreducibleCloseds

variable {X : Type u} [TopologicalSpace X]

/-- The height of an irreducible closed subset in the inclusion order. -/
noncomputable def height (S : IrreducibleCloseds X) : ℕ∞ :=
  Order.height S

@[simp] theorem height_eq_order_height (S : IrreducibleCloseds X) :
    S.height = Order.height S :=
  rfl

@[gcongr] theorem height_mono : Monotone (height (X := X)) := by
  intro S T hST
  simpa [height] using (Order.height_mono hST)

theorem height_add_one_le {S T : IrreducibleCloseds X} (hST : S < T) :
    S.height + 1 ≤ T.height := by
  simpa [height] using (Order.height_add_one_le hST)

theorem height_le_topologicalKrullDim (S : IrreducibleCloseds X) :
    S.height ≤ topologicalKrullDim X := by
  simpa [height, topologicalKrullDim] using (Order.height_le_krullDim S)

theorem height_le_height_map_of_isInducing {Y : Type*} [TopologicalSpace Y] {f : Y → X}
    (hf : Topology.IsInducing f) (S : IrreducibleCloseds Y) :
    S.height ≤ (IrreducibleCloseds.map f hf.continuous S).height := by
  simpa [height] using Order.height_le_height_apply_of_strictMono
    (IrreducibleCloseds.map f hf.continuous)
    (IrreducibleCloseds.map_strictMono_of_isInducing hf)
    S

/-- An irreducible closed subset of a proper closed subspace of an irreducible space has height
at most one less than the ambient topological Krull dimension. -/
theorem height_add_one_le_topologicalKrullDim_of_isClosed_of_ne_univ
    [IrreducibleSpace X] {Y : Set X} (hY : IsClosed Y) (hne : Y ≠ Set.univ)
    (S : IrreducibleCloseds Y) :
    (S.height : WithBot ℕ∞) + 1 ≤ topologicalKrullDim X := by
  let T : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  set f : IrreducibleCloseds Y → IrreducibleCloseds X :=
    IrreducibleCloseds.map (Subtype.val : Y → X) continuous_subtype_val
  have h_height_le : S.height ≤ (f S).height :=
    height_le_height_map_of_isInducing Topology.IsInducing.subtypeVal S
  have h_lt_top : f S < T := by
    refine lt_of_le_of_ne (Set.subset_univ _) fun h_eq => hne ?_
    have h_sub : (f S : Set X) ⊆ Y :=
      closure_minimal (fun _ ⟨⟨_, hy⟩, _, rfl⟩ => hy) hY
    have h_eq' : (f S : Set X) = Set.univ := by
      simpa [T] using congrArg IrreducibleCloseds.carrier h_eq
    rwa [h_eq', Set.univ_subset_iff] at h_sub
  have h_height_add_one : ((f S).height : WithBot ℕ∞) + 1 ≤ T.height := by
    exact_mod_cast height_add_one_le h_lt_top
  refine le_trans ?_ (h_height_add_one.trans ?_)
  · gcongr
    exact_mod_cast h_height_le
  · simpa [T] using (height_le_topologicalKrullDim T : _)

end IrreducibleCloseds

/-- The topological Krull dimension is the supremum of the heights of irreducible closed sets. -/
theorem topologicalKrullDim_eq_iSup_height (X : Type u) [TopologicalSpace X] :
    topologicalKrullDim X = ⨆ S : IrreducibleCloseds X, ↑S.height := by
  simpa [IrreducibleCloseds.height, topologicalKrullDim] using
    (Order.krullDim_eq_iSup_height (α := IrreducibleCloseds X))

/-- The topological Krull dimension plus one is the supremum of the heights of irreducible
closed sets, each shifted by one. -/
theorem topologicalKrullDim_add_one_eq_iSup_height_add_one (X : Type u) [TopologicalSpace X] :
    topologicalKrullDim X + 1 =
      ⨆ S : IrreducibleCloseds X, ((S.height : WithBot ℕ∞) + 1) := by
  cases isEmpty_or_nonempty (IrreducibleCloseds X) with
  | inl h =>
      rw [topologicalKrullDim_eq_iSup_height]
      letI := h
      simp
  | inr h =>
      letI := h
      rw [topologicalKrullDim_eq_iSup_height]
      have bdd :
          BddAbove (Set.range (fun S : IrreducibleCloseds X => IrreducibleCloseds.height S)) :=
        OrderTop.bddAbove _
      rw [show (⨆ S : IrreducibleCloseds X, (S.height : WithBot ℕ∞)) =
          ↑(⨆ S : IrreducibleCloseds X, IrreducibleCloseds.height S) from
        (WithBot.coe_iSup
          (f := fun S : IrreducibleCloseds X => IrreducibleCloseds.height S) bdd).symm]
      rw [show (↑(⨆ S : IrreducibleCloseds X, IrreducibleCloseds.height S) : WithBot ℕ∞) + 1 =
          ↑((⨆ S : IrreducibleCloseds X, IrreducibleCloseds.height S) + 1) from
        by push_cast; ring]
      rw [ENat.iSup_add,
        WithBot.coe_iSup
          (f := fun S : IrreducibleCloseds X => IrreducibleCloseds.height S + 1)
          (OrderTop.bddAbove _)]
      simp_rw [show ∀ S : IrreducibleCloseds X,
          (↑(S.height + 1 : ℕ∞) : WithBot ℕ∞) = (↑S.height : WithBot ℕ∞) + 1 from
        by
          intro S
          push_cast
          ring]

end TopologicalSpace

/-- Unconditional: topologicalKrullDim Y + 1 ≤ topologicalKrullDim X for
    Y ⊊ X closed in irreducible X. -/
theorem topologicalKrullDim_add_one_le_of_isIrreducible_of_isClosed {X : Type u}
    [TopologicalSpace X] [IrreducibleSpace X] {Y : Set X} (hY : IsClosed Y)
    (hne : Y ≠ Set.univ) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim_add_one_eq_iSup_height_add_one]
  exact iSup_le (fun s =>
    IrreducibleCloseds.height_add_one_le_topologicalKrullDim_of_isClosed_of_ne_univ hY hne s)

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
