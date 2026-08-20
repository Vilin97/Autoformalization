/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CyclicGraphBasis

/-!
# Lifted pieces of the cyclic rose cover

The degree-`m` cyclic rose cover has `m` lifted left loops and one right `m`-cycle.  This file
makes that decomposition, its deck action, and its compatibility with divisibility factor maps
literal at the finite labelled-graph level.

These are combinatorial statements only.  Their interpretation as one-handle pieces and neck
spheres in the partial `S²`-spin of a planar ribbon surface remains a separate geometric theorem.
-/

@[expose] public section

open Function Set

noncomputable section

namespace SplittingSpheres

namespace RoseCover

/-- The oriented edges carrying one fixed rose-edge label. -/
def edgesWithLabel (C : RoseCover) (i : Fin 2) : Set C.Edge :=
  {e | e.2 = i}

/-- Edges with a fixed label are canonically indexed by their source vertices. -/
def vertexEquivEdgesWithLabel (C : RoseCover) (i : Fin 2) :
    C.Vertex ≃ {e : C.Edge // e ∈ C.edgesWithLabel i} where
  toFun v := ⟨(v, i), rfl⟩
  invFun e := e.1.1
  left_inv _ := rfl
  right_inv e := by
    apply Subtype.ext
    exact Prod.ext rfl e.2.symm

/-- Every label contributes exactly one edge per vertex. -/
theorem edgesWithLabel_card (C : RoseCover) (i : Fin 2) :
    Nat.card (C.edgesWithLabel i) = Nat.card C.Vertex :=
  (Nat.card_congr (C.vertexEquivEdgesWithLabel i)).symm

/-- The two labelled edge families are disjoint. -/
theorem disjoint_edgesWithLabel_zero_one (C : RoseCover) :
    Disjoint (C.edgesWithLabel 0) (C.edgesWithLabel 1) := by
  rw [Set.disjoint_left]
  intro e he0 he1
  change e.2 = 0 at he0
  change e.2 = 1 at he1
  omega

/-- The two labelled edge families exhaust all oriented edges. -/
theorem union_edgesWithLabel_zero_one (C : RoseCover) :
    C.edgesWithLabel 0 ∪ C.edgesWithLabel 1 = Set.univ := by
  ext e
  rcases e with ⟨v, i⟩
  fin_cases i <;> simp [edgesWithLabel]

end RoseCover

namespace cyclicRoseCover

variable (m : ℕ) [NeZero m]

/-- The `m` lifted copies of the left loop. -/
abbrev leftEdges : Set (cyclicRoseCover m).Edge :=
  (cyclicRoseCover m).edgesWithLabel 0

/-- The edges forming the connected right `m`-cycle. -/
abbrev rightEdges : Set (cyclicRoseCover m).Edge :=
  (cyclicRoseCover m).edgesWithLabel 1

@[simp]
theorem leftEdges_card : Nat.card (leftEdges m) = m := by
  rw [RoseCover.edgesWithLabel_card, vertex_card]

@[simp]
theorem rightEdges_card : Nat.card (rightEdges m) = m := by
  rw [RoseCover.edgesWithLabel_card, vertex_card]

theorem disjoint_leftEdges_rightEdges : Disjoint (leftEdges m) (rightEdges m) :=
  (cyclicRoseCover m).disjoint_edgesWithLabel_zero_one

theorem union_leftEdges_rightEdges :
    leftEdges m ∪ rightEdges m = Set.univ :=
  (cyclicRoseCover m).union_edgesWithLabel_zero_one

/-- Every lifted left edge is a loop at its source vertex. -/
@[simp]
theorem edgeTarget_left (v : ZMod m) :
    (cyclicRoseCover m).edgeTarget (v, 0) = v :=
  step_zero m v

/-- Every lifted right edge advances one vertex around the cyclic cover. -/
@[simp]
theorem edgeTarget_right (v : ZMod m) :
    (cyclicRoseCover m).edgeTarget (v, 1) = v + 1 :=
  step_one m v

/-- A deck translation acts on edges by translating the source and retaining the label. -/
def deckTranslationEdge (a : ZMod m) : Equiv.Perm (cyclicRoseCover m).Edge :=
  (deckTranslation m a).prodCongr (Equiv.refl (Fin 2))

@[simp]
theorem deckTranslationEdge_apply (a : ZMod m)
    (e : (cyclicRoseCover m).Edge) :
    deckTranslationEdge m a e = (e.1 + a, e.2) :=
  rfl

/-- Edge deck translation commutes with the source map. -/
@[simp]
theorem edgeSource_deckTranslationEdge (a : ZMod m)
    (e : (cyclicRoseCover m).Edge) :
    (cyclicRoseCover m).edgeSource (deckTranslationEdge m a e) =
      deckTranslation m a ((cyclicRoseCover m).edgeSource e) :=
  rfl

/-- Edge deck translation commutes with the target map. -/
@[simp]
theorem edgeTarget_deckTranslationEdge (a : ZMod m)
    (e : (cyclicRoseCover m).Edge) :
    (cyclicRoseCover m).edgeTarget (deckTranslationEdge m a e) =
      deckTranslation m a ((cyclicRoseCover m).edgeTarget e) := by
  exact (deckTranslation_comm_step m a e.2 e.1).symm

/-- The edge deck action preserves the rose-edge label. -/
@[simp]
theorem deckTranslationEdge_label (a : ZMod m)
    (e : (cyclicRoseCover m).Edge) :
    (deckTranslationEdge m a e).2 = e.2 :=
  rfl

/-- A deck translation fixing one oriented edge is the identity translation. -/
theorem deckTranslationEdge_fixed_iff (a : ZMod m)
    (e : (cyclicRoseCover m).Edge) :
    deckTranslationEdge m a e = e ↔ a = 0 := by
  constructor
  · intro h
    have hsource := congrArg Prod.fst h
    change e.1 + a = e.1 at hsource
    exact add_left_cancel (hsource.trans (add_zero e.1).symm)
  · rintro rfl
    simp

/-- Deck translations act transitively on the edges of either fixed label. -/
theorem exists_deckTranslationEdge_eq_of_label_eq
    (e f : (cyclicRoseCover m).Edge) (hlabel : e.2 = f.2) :
    ∃ a : ZMod m, deckTranslationEdge m a e = f := by
  refine ⟨f.1 - e.1, ?_⟩
  apply Prod.ext
  · simp
  · exact hlabel

/-- Reduction modulo a divisor on vertices extends labelwise to oriented edges. -/
def factorEdge {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m) :
    (cyclicRoseCover m).Edge → (cyclicRoseCover k).Edge :=
  fun e ↦ (factor h e.1, e.2)

@[simp]
theorem factorEdge_apply {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m)
    (e : (cyclicRoseCover m).Edge) :
    factorEdge h e = (ZMod.cast e.1, e.2) :=
  rfl

/-- The edge factor map is surjective. -/
theorem factorEdge_surjective {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m) :
    Function.Surjective (factorEdge h) := by
  rintro ⟨v, i⟩
  obtain ⟨w, rfl⟩ := factor_surjective h v
  exact ⟨(w, i), rfl⟩

/-- The edge factor map commutes with sources. -/
@[simp]
theorem edgeSource_factorEdge {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m)
    (e : (cyclicRoseCover m).Edge) :
    (cyclicRoseCover k).edgeSource (factorEdge h e) =
      factor h ((cyclicRoseCover m).edgeSource e) :=
  rfl

/-- The edge factor map commutes with targets. -/
@[simp]
theorem edgeTarget_factorEdge {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m)
    (e : (cyclicRoseCover m).Edge) :
    (cyclicRoseCover k).edgeTarget (factorEdge h e) =
      factor h ((cyclicRoseCover m).edgeTarget e) := by
  exact ((factor h).map_step e.2 e.1).symm

/-- Factor maps intertwine deck translations with reduction of their translation parameter. -/
theorem factorEdge_deckTranslationEdge {k m : ℕ} [NeZero k] [NeZero m]
    (h : k ∣ m) (a : ZMod m) (e : (cyclicRoseCover m).Edge) :
    factorEdge h (deckTranslationEdge m a e) =
      deckTranslationEdge k (ZMod.cast a) (factorEdge h e) := by
  apply Prod.ext
  · exact map_add (ZMod.castHom h (ZMod k)) e.1 a
  · rfl

/-- The non-tree edges split exactly into the `m` lifted left loops and the single omitted
wraparound edge of the right cycle. -/
theorem spanningTreeEdges_compl_eq_leftEdges_union_wrap :
    (spanningTreeEdges m)ᶜ =
      leftEdges m ∪ {(lastVertex m, (1 : Fin 2))} := by
  ext e
  rcases e with ⟨v, i⟩
  fin_cases i <;> simp [spanningTreeEdges, RoseCover.edgesWithLabel]

end cyclicRoseCover

end SplittingSpheres
