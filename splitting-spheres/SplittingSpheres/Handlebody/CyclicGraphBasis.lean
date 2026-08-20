/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CyclicGraph

/-!
# A spanning arborescence in the cyclic rose cover

This file makes the elementary spanning-tree calculation behind `cyclicRoseCover` explicit.  The
rose-cover API has oriented, labelled edges, so we use the corresponding finite directed notion:
a set of edges spans from the base and admits a strictly increasing natural-number rank.  The rank
also proves that no nonempty directed path closes up.

For the degree-`m` cyclic cover, the tree consists of the label-`1` edges which advance through
the standard representatives `0, ..., m - 1`, with the single wraparound edge omitted.  Its
complement consists of all `m` label-`0` loops and that one wraparound edge, hence has `m + 1`
elements.
-/

@[expose] public section

noncomputable section

namespace SplittingSpheres

namespace RoseCover

/-- A step along one of the selected oriented edges. -/
def EdgeStep (C : RoseCover) (T : Set C.Edge) (x y : C.Vertex) : Prop :=
  ∃ i, C.edgeAt x i ∈ T ∧ C.step i x = y

/-- Reachability using only selected oriented edges. -/
def ReachableWithin (C : RoseCover) (T : Set C.Edge) (x y : C.Vertex) : Prop :=
  Relation.ReflTransGen (C.EdgeStep T) x y

/-- Every vertex is reachable from the chosen base using selected edges. -/
def SpansFromBase (C : RoseCover) (T : Set C.Edge) : Prop :=
  ∀ v, C.ReachableWithin T C.base v

/-- An explicit acyclicity certificate: every selected step strictly increases a natural rank. -/
def HasIncreasingRank (C : RoseCover) (T : Set C.Edge) : Prop :=
  ∃ rank : C.Vertex → ℕ, ∀ ⦃x y⦄, C.EdgeStep T x y → rank x < rank y

/-- The directed spanning-tree notion appropriate to the oriented `RoseCover` edge DSL.

Besides spanning and an acyclicity certificate, the selected edge set is required to have exactly
one fewer edge than the vertex set.  Thus this predicate does not classify a redundant spanning
DAG as a tree. -/
def IsSpanningArborescence (C : RoseCover) (T : Set C.Edge) : Prop :=
  C.SpansFromBase T ∧ C.HasIncreasingRank T ∧ Nat.card T + 1 = Nat.card C.Vertex

/-- An increasing rank rules out every nonempty closed directed path. -/
theorem HasIncreasingRank.no_directed_cycle {C : RoseCover} {T : Set C.Edge}
    (h : C.HasIncreasingRank T) (v : C.Vertex) :
    ¬ Relation.TransGen (C.EdgeStep T) v v := by
  rintro hv
  obtain ⟨rank, hrank⟩ := h
  have hlt : ∀ {x y}, Relation.TransGen (C.EdgeStep T) x y → rank x < rank y := by
    intro x y hxy
    induction hxy with
    | single hstep => exact hrank hstep
    | tail _ hstep ih => exact ih.trans (hrank hstep)
  exact (hlt hv).false

end RoseCover

namespace cyclicRoseCover

variable (m : ℕ) [NeZero m]

/-- The final standard residue, used as the source of the omitted wraparound edge. -/
def lastVertex : ZMod m := ((m - 1 : ℕ) : ZMod m)

/-- All advancing (label-`1`) edges except the wraparound edge. -/
def spanningTreeEdges : Set (cyclicRoseCover m).Edge :=
  {e | e.2 = 1 ∧ e.1 ≠ lastVertex m}

private theorem m_pos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)

@[simp]
theorem lastVertex_val : (lastVertex m).val = m - 1 := by
  have hm := m_pos m
  apply ZMod.val_natCast_of_lt
  omega

@[simp]
theorem mem_spanningTreeEdges_iff (e : (cyclicRoseCover m).Edge) :
    e ∈ spanningTreeEdges m ↔ e.2 = 1 ∧ e.1 ≠ lastVertex m :=
  Iff.rfl

/-- The omitted advancing edge is exactly the edge which wraps the final residue back to `0`. -/
@[simp]
theorem edgeTarget_lastVertex_one :
    (cyclicRoseCover m).edgeTarget (lastVertex m, 1) = 0 := by
  change lastVertex m + (1 : ZMod m) = 0
  calc
    lastVertex m + (1 : ZMod m) = (((m - 1) + 1 : ℕ) : ZMod m) := by
      rw [lastVertex, Nat.cast_add, Nat.cast_one]
    _ = (m : ZMod m) := by
      congr 1
      exact Nat.sub_add_cancel (by have := m_pos m; omega)
    _ = 0 := ZMod.natCast_self m

private theorem tree_reachable_nat : ∀ n : ℕ, n < m →
    (cyclicRoseCover m).ReachableWithin (spanningTreeEdges m) 0 (n : ZMod m)
  | 0, _ => by
      simpa [RoseCover.ReachableWithin] using
        (Relation.ReflTransGen.refl :
          Relation.ReflTransGen
            ((cyclicRoseCover m).EdgeStep (spanningTreeEdges m))
            (0 : ZMod m) (0 : ZMod m))
  | n + 1, hn => by
      have hm := m_pos m
      apply (tree_reachable_nat n (by omega)).tail
      refine ⟨1, ?_, ?_⟩
      · refine ⟨rfl, ?_⟩
        change (n : ZMod m) ≠ lastVertex m
        exact fun hlast ↦ by
          have hval := congr_arg ZMod.val hlast
          rw [ZMod.val_natCast_of_lt (by omega), lastVertex_val] at hval
          omega
      · simp [Nat.cast_add, Nat.cast_one]

/-- The selected advancing edges reach every vertex from `0`. -/
theorem spanningTreeEdges_spans :
    (cyclicRoseCover m).SpansFromBase (spanningTreeEdges m) := by
  intro v
  rw [← ZMod.natCast_zmod_val v]
  exact tree_reachable_nat m v.val v.val_lt

/-- Residue value is a strictly increasing rank along every selected edge. -/
theorem spanningTreeEdges_hasIncreasingRank :
    (cyclicRoseCover m).HasIncreasingRank (spanningTreeEdges m) := by
  refine ⟨ZMod.val, ?_⟩
  rintro x y ⟨i, hi, hxy⟩
  obtain ⟨rfl, hxlast⟩ := hi
  change x ≠ lastVertex m at hxlast
  rw [step_one] at hxy
  subst y
  have hm := m_pos m
  have hxbound := x.val_lt
  have hxlt : x.val + 1 < m := by
    by_contra h
    have hxadd : x.val + 1 = m := by omega
    have hxval : x.val = m - 1 := Nat.eq_sub_of_add_eq hxadd
    apply hxlast
    apply ZMod.val_injective m
    simpa using hxval
  calc
    x.val < x.val + 1 := Nat.lt_succ_self _
    _ = (x + 1 : ZMod m).val := by
      have hsum : (x + 1 : ZMod m) = ((x.val + 1 : ℕ) : ZMod m) := by
        rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
      rw [hsum, ZMod.val_natCast_of_lt hxlt]

/-- In particular, no nonempty directed path in the selected edges is a cycle. -/
theorem spanningTreeEdges_no_directed_cycle (v : ZMod m) :
    ¬ Relation.TransGen
      ((cyclicRoseCover m).EdgeStep (spanningTreeEdges m)) v v :=
  (spanningTreeEdges_hasIncreasingRank m).no_directed_cycle v

/-- A non-tree edge is encoded either by the source of a label-`0` loop or by the unique
wraparound label-`1` edge. -/
def nonTreeEdgeCode :
    {e : (cyclicRoseCover m).Edge // e ∉ spanningTreeEdges m} → ZMod m ⊕ PUnit.{1} :=
  fun e ↦ Fin.cases (Sum.inl e.1.1) (fun _ ↦ Sum.inr PUnit.unit) e.1.2

/-- Decode the `m` loop codes and the one wraparound code as non-tree edges. -/
def nonTreeEdgeDecode :
    ZMod m ⊕ PUnit.{1} → {e : (cyclicRoseCover m).Edge // e ∉ spanningTreeEdges m}
  | Sum.inl v => ⟨(v, 0), by simp [spanningTreeEdges]⟩
  | Sum.inr _ => ⟨(lastVertex m, 1), by simp [spanningTreeEdges]⟩

theorem nonTreeEdgeDecode_code
    (e : {e : (cyclicRoseCover m).Edge // e ∉ spanningTreeEdges m}) :
    nonTreeEdgeDecode m (nonTreeEdgeCode m e) = e := by
  rcases e with ⟨⟨v, i⟩, he⟩
  fin_cases i
  · rfl
  · have hv : v = lastVertex m := by
      by_contra hv
      exact he ⟨rfl, hv⟩
    subst v
    rfl

theorem nonTreeEdgeCode_decode (e : ZMod m ⊕ PUnit.{1}) :
    nonTreeEdgeCode m (nonTreeEdgeDecode m e) = e := by
  rcases e with (v | u)
  · rfl
  · cases u
    rfl

/-- The complement of the spanning tree is exactly `ZMod m ⊕ PUnit`: all label-`0` loops plus
the wraparound label-`1` edge. -/
def nonTreeEdgeEquiv :
    {e : (cyclicRoseCover m).Edge // e ∉ spanningTreeEdges m} ≃ ZMod m ⊕ PUnit.{1} where
  toFun := nonTreeEdgeCode m
  invFun := nonTreeEdgeDecode m
  left_inv := nonTreeEdgeDecode_code m
  right_inv := nonTreeEdgeCode_decode m

/-- There are exactly `m + 1` edges outside the spanning tree. -/
@[simp]
theorem nonTreeEdge_card :
    Nat.card {e : (cyclicRoseCover m).Edge // e ∉ spanningTreeEdges m} = m + 1 := by
  rw [Nat.card_congr (nonTreeEdgeEquiv m), Nat.card_sum, Nat.card_zmod, Nat.card_unique]

/-- Set-complement form of `nonTreeEdge_card`. -/
@[simp]
theorem spanningTreeEdges_compl_card :
    Nat.card ((spanningTreeEdges m)ᶜ : Set (cyclicRoseCover m).Edge) = m + 1 := by
  let e : ((spanningTreeEdges m)ᶜ : Set (cyclicRoseCover m).Edge) ≃
      {e : (cyclicRoseCover m).Edge // e ∉ spanningTreeEdges m} :=
    { toFun := fun x ↦ ⟨x, x.2⟩
      invFun := fun x ↦ ⟨x, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact (Nat.card_congr e).trans (nonTreeEdge_card m)

/-- The spanning tree itself has the expected `m - 1` edges. -/
@[simp]
theorem spanningTreeEdge_card : Nat.card (spanningTreeEdges m) = m - 1 := by
  classical
  have hsplit :
      Nat.card (spanningTreeEdges m) +
          Nat.card {e : (cyclicRoseCover m).Edge // e ∉ spanningTreeEdges m} =
        Nat.card (cyclicRoseCover m).Edge := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun e ↦ e ∈ spanningTreeEdges m))
  rw [nonTreeEdge_card, edge_card] at hsplit
  have hm := m_pos m
  omega

/-- The non-wrapping advancing edges form a spanning arborescence. -/
theorem spanningTreeEdges_isSpanningArborescence :
    (cyclicRoseCover m).IsSpanningArborescence (spanningTreeEdges m) := by
  refine ⟨spanningTreeEdges_spans m, spanningTreeEdges_hasIncreasingRank m, ?_⟩
  rw [spanningTreeEdge_card, vertex_card]
  have hm := m_pos m
  omega

end cyclicRoseCover

end SplittingSpheres
