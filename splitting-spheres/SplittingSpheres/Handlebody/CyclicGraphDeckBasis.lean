/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CyclicGraphBasis
public import SplittingSpheres.Handlebody.CyclicGraphPieces

/-!
# Deck transformations, factor maps, and the cyclic graph basis

The spanning arborescence in `CyclicGraphBasis` is rooted at `0`, so a nontrivial deck
translation does not preserve it.  Instead, translation carries it to the analogous tree with a
translated omitted right edge.  This file records that moving family of bases, the genuine deck
permutation on the left-loop part, and the maps on non-tree edges induced by divisibility factor
maps.

Everything here concerns finite labelled graphs.  No topological handlebody, fundamental-group,
or free-group interpretation is asserted.
-/

@[expose] public section

open Function Set

noncomputable section

namespace SplittingSpheres

namespace RoseCover

/-- Every vertex is reachable from a specified root using selected oriented edges. -/
def SpansFromVertex (C : RoseCover) (T : Set C.Edge) (root : C.Vertex) : Prop :=
  ∀ v, C.ReachableWithin T root v

/-- The rooted version of `IsSpanningArborescence`, allowing deck transformations to move the
root along with the selected edge set. -/
def IsSpanningArborescenceAt (C : RoseCover) (T : Set C.Edge) (root : C.Vertex) : Prop :=
  C.SpansFromVertex T root ∧ C.HasIncreasingRank T ∧
    Nat.card T + 1 = Nat.card C.Vertex

@[simp]
theorem isSpanningArborescenceAt_base_iff (C : RoseCover) (T : Set C.Edge) :
    C.IsSpanningArborescenceAt T C.base ↔ C.IsSpanningArborescence T :=
  Iff.rfl

end RoseCover

namespace cyclicRoseCover

variable (m : ℕ) [NeZero m]

/-- The translated tree omits the right edge whose source is `lastVertex m + a`.  At `a = 0`
this is the original spanning tree. -/
def translatedSpanningTreeEdges (a : ZMod m) : Set (cyclicRoseCover m).Edge :=
  {e | e.2 = 1 ∧ e.1 ≠ lastVertex m + a}

@[simp]
theorem mem_translatedSpanningTreeEdges_iff (a : ZMod m)
    (e : (cyclicRoseCover m).Edge) :
    e ∈ translatedSpanningTreeEdges m a ↔ e.2 = 1 ∧ e.1 ≠ lastVertex m + a :=
  Iff.rfl

@[simp]
theorem translatedSpanningTreeEdges_zero :
    translatedSpanningTreeEdges m 0 = spanningTreeEdges m := by
  ext e
  simp [translatedSpanningTreeEdges, spanningTreeEdges]

/-- The complement of a translated tree consists of all left edges and its one omitted right
edge. -/
theorem translatedSpanningTreeEdges_compl_eq_leftEdges_union_wrap (a : ZMod m) :
    (translatedSpanningTreeEdges m a)ᶜ =
      leftEdges m ∪ {(lastVertex m + a, (1 : Fin 2))} := by
  ext e
  rcases e with ⟨v, i⟩
  fin_cases i <;> simp [translatedSpanningTreeEdges, RoseCover.edgesWithLabel]

/-- Deck translation takes membership in the tree based at `a` to membership in the tree based
at `a + b`. -/
@[simp]
theorem deckTranslationEdge_mem_translatedSpanningTreeEdges_iff
    (a b : ZMod m) (e : (cyclicRoseCover m).Edge) :
    deckTranslationEdge m b e ∈ translatedSpanningTreeEdges m (a + b) ↔
      e ∈ translatedSpanningTreeEdges m a := by
  simp only [mem_translatedSpanningTreeEdges_iff, deckTranslationEdge_apply]
  constructor
  · rintro ⟨hi, hne⟩
    refine ⟨hi, ?_⟩
    intro heq
    apply hne
    simp only [heq, add_assoc]
  · rintro ⟨hi, hne⟩
    refine ⟨hi, ?_⟩
    intro heq
    apply hne
    apply add_right_cancel (b := b)
    simpa only [add_assoc] using heq

/-- On complements, deck translation has the corresponding membership equivalence. -/
@[simp]
theorem deckTranslationEdge_not_mem_translatedSpanningTreeEdges_iff
    (a b : ZMod m) (e : (cyclicRoseCover m).Edge) :
    deckTranslationEdge m b e ∉ translatedSpanningTreeEdges m (a + b) ↔
      e ∉ translatedSpanningTreeEdges m a :=
  not_congr (deckTranslationEdge_mem_translatedSpanningTreeEdges_iff m a b e)

/-- Translating every edge of one member of the tree family produces the next member. -/
theorem deckTranslationEdge_image_translatedSpanningTreeEdges (a b : ZMod m) :
    deckTranslationEdge m b '' translatedSpanningTreeEdges m a =
      translatedSpanningTreeEdges m (a + b) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨e, he, rfl⟩
    exact (deckTranslationEdge_mem_translatedSpanningTreeEdges_iff m a b e).2 he
  · intro e he
    refine ⟨deckTranslationEdge m (-b) e, ?_, ?_⟩
    · have hmem :=
        (deckTranslationEdge_mem_translatedSpanningTreeEdges_iff m (a + b) (-b) e).2 he
      simpa only [add_neg_cancel_right] using hmem
    · apply Prod.ext
      · simp [deckTranslationEdge_apply, add_assoc]
      · rfl

/-- Deck translation carries the complement basis at `a` onto the complement basis at `a + b`.
This is the set-level form of the moving-basis action. -/
theorem deckTranslationEdge_image_translatedSpanningTreeEdges_compl (a b : ZMod m) :
    deckTranslationEdge m b '' (translatedSpanningTreeEdges m a)ᶜ =
      (translatedSpanningTreeEdges m (a + b))ᶜ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨e, he, rfl⟩
    exact (deckTranslationEdge_not_mem_translatedSpanningTreeEdges_iff m a b e).2 he
  · intro e he
    refine ⟨deckTranslationEdge m (-b) e, ?_, ?_⟩
    · have hmem :=
        (deckTranslationEdge_not_mem_translatedSpanningTreeEdges_iff
          m (a + b) (-b) e).2 he
      change deckTranslationEdge m (-b) e ∉ translatedSpanningTreeEdges m a
      simpa only [add_neg_cancel_right] using hmem
    · apply Prod.ext
      · simp [deckTranslationEdge_apply, add_assoc]
      · rfl

/-- The original tree is carried to the tree whose omitted edge is translated by `a`. -/
theorem deckTranslationEdge_image_spanningTreeEdges (a : ZMod m) :
    deckTranslationEdge m a '' spanningTreeEdges m =
      translatedSpanningTreeEdges m a := by
  rw [← translatedSpanningTreeEdges_zero m,
    deckTranslationEdge_image_translatedSpanningTreeEdges]
  simp

/-- A translated tree equals the chosen tree precisely for the identity translation. -/
theorem translatedSpanningTreeEdges_eq_spanningTreeEdges_iff (a : ZMod m) :
    translatedSpanningTreeEdges m a = spanningTreeEdges m ↔ a = 0 := by
  constructor
  · intro h
    have hnot : (lastVertex m + a, (1 : Fin 2)) ∉ spanningTreeEdges m := by
      rw [← h]
      simp [translatedSpanningTreeEdges]
    have hsource : lastVertex m + a = lastVertex m := by
      simpa [spanningTreeEdges] using hnot
    exact add_left_cancel (hsource.trans (add_zero (lastVertex m)).symm)
  · rintro rfl
    exact translatedSpanningTreeEdges_zero m

/-- Different translation parameters give different omitted-edge trees. -/
theorem translatedSpanningTreeEdges_eq_iff (a b : ZMod m) :
    translatedSpanningTreeEdges m a = translatedSpanningTreeEdges m b ↔ a = b := by
  constructor
  · intro h
    have hnot : (lastVertex m + a, (1 : Fin 2)) ∉
        translatedSpanningTreeEdges m b := by
      rw [← h]
      simp [translatedSpanningTreeEdges]
    have hab : lastVertex m + a = lastVertex m + b := by
      simpa [translatedSpanningTreeEdges] using hnot
    exact add_left_cancel hab
  · rintro rfl
    rfl

/-- The family of translated trees is indexed injectively by the deck group. -/
theorem translatedSpanningTreeEdges_injective :
    Function.Injective (translatedSpanningTreeEdges m) := by
  intro a b h
  exact (translatedSpanningTreeEdges_eq_iff m a b).1 h

/-- The deck orbit of the chosen tree is canonically indexed by its translation parameter. -/
def translatedSpanningTreeOrbitEquiv :
    ZMod m ≃ Set.range (translatedSpanningTreeEdges m) where
  toFun a := ⟨translatedSpanningTreeEdges m a, ⟨a, rfl⟩⟩
  invFun T := Classical.choose T.2
  left_inv a := by
    apply translatedSpanningTreeEdges_injective m
    exact Classical.choose_spec
      (show translatedSpanningTreeEdges m a ∈
        Set.range (translatedSpanningTreeEdges m) from ⟨a, rfl⟩)
  right_inv T := by
    apply Subtype.ext
    exact Classical.choose_spec T.2

/-- There are exactly `m` distinct trees in the deck orbit of the chosen rooted tree. -/
@[simp]
theorem translatedSpanningTreeOrbit_card :
    Nat.card (Set.range (translatedSpanningTreeEdges m)) = m := by
  calc
    Nat.card (Set.range (translatedSpanningTreeEdges m)) = Nat.card (ZMod m) :=
      Nat.card_congr (translatedSpanningTreeOrbitEquiv m).symm
    _ = m := Nat.card_zmod m

/-- Consequently, the stabilizer of the chosen spanning tree in the deck-translation group is
trivial. -/
theorem deckTranslationEdge_image_spanningTreeEdges_eq_iff (a : ZMod m) :
    deckTranslationEdge m a '' spanningTreeEdges m = spanningTreeEdges m ↔ a = 0 := by
  rw [deckTranslationEdge_image_spanningTreeEdges,
    translatedSpanningTreeEdges_eq_spanningTreeEdges_iff]

/-- The fixed non-tree basis is preserved setwise only by the identity deck translation. -/
theorem deckTranslationEdge_image_spanningTreeEdges_compl_eq_iff (a : ZMod m) :
    deckTranslationEdge m a '' (spanningTreeEdges m)ᶜ =
      (spanningTreeEdges m)ᶜ ↔ a = 0 := by
  rw [← translatedSpanningTreeEdges_zero m,
    deckTranslationEdge_image_translatedSpanningTreeEdges_compl]
  simp only [zero_add]
  rw [compl_inj_iff, translatedSpanningTreeEdges_eq_iff]

/-- A selected edge step transports along a deck translation when the selected edge set is
translated by image. -/
theorem edgeStep_deckTranslation {T : Set (cyclicRoseCover m).Edge}
    (a : ZMod m) {x y : ZMod m}
    (h : (cyclicRoseCover m).EdgeStep T x y) :
    (cyclicRoseCover m).EdgeStep (deckTranslationEdge m a '' T)
      (deckTranslation m a x) (deckTranslation m a y) := by
  rcases h with ⟨i, hi, hxy⟩
  refine ⟨i, ?_, ?_⟩
  · exact ⟨(cyclicRoseCover m).edgeAt x i, hi, rfl⟩
  · calc
      (cyclicRoseCover m).step i (deckTranslation m a x) =
          deckTranslation m a ((cyclicRoseCover m).step i x) :=
        (deckTranslation_comm_step m a i x).symm
      _ = deckTranslation m a y := congrArg (deckTranslation m a) hxy

/-- Reachability transports along a deck translation together with the edge set. -/
theorem reachableWithin_deckTranslation {T : Set (cyclicRoseCover m).Edge}
    (a : ZMod m) {x y : ZMod m}
    (h : (cyclicRoseCover m).ReachableWithin T x y) :
    (cyclicRoseCover m).ReachableWithin (deckTranslationEdge m a '' T)
      (deckTranslation m a x) (deckTranslation m a y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (edgeStep_deckTranslation m a hstep)

/-- The translated tree spans from the translated base vertex. -/
theorem translatedSpanningTreeEdges_spansFromVertex (a : ZMod m) :
    (cyclicRoseCover m).SpansFromVertex (translatedSpanningTreeEdges m a) a := by
  intro v
  let w : ZMod m := v - a
  have hreach := reachableWithin_deckTranslation m a
    (spanningTreeEdges_spans m w)
  rw [deckTranslationEdge_image_spanningTreeEdges] at hreach
  simpa [w, deckTranslation_apply, sub_eq_add_neg, add_assoc] using hreach

/-- A translated residue rank proves directed acyclicity of every translated tree. -/
theorem translatedSpanningTreeEdges_hasIncreasingRank (a : ZMod m) :
    (cyclicRoseCover m).HasIncreasingRank (translatedSpanningTreeEdges m a) := by
  obtain ⟨rank, hrank⟩ := spanningTreeEdges_hasIncreasingRank m
  refine ⟨fun v ↦ rank (v - a), ?_⟩
  rintro x y ⟨i, hi, hxy⟩
  obtain ⟨hi, hx⟩ := hi
  change i = 1 at hi
  change x ≠ lastVertex m + a at hx
  subst i
  have hstep : (cyclicRoseCover m).EdgeStep (spanningTreeEdges m) (x - a) (y - a) := by
    refine ⟨1, ?_, ?_⟩
    · refine ⟨rfl, ?_⟩
      intro hlast
      apply hx
      calc
        x = (x - a) + a := (sub_add_cancel x a).symm
        _ = lastVertex m + a := congrArg (fun z ↦ z + a) hlast
    · rw [step_one]
      rw [step_one] at hxy
      rw [← hxy]
      simp only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  exact hrank hstep

/-- Code a non-tree edge for the tree omitting the right edge at `lastVertex m + a`. -/
def translatedNonTreeEdgeCode (a : ZMod m) :
    {e : (cyclicRoseCover m).Edge // e ∉ translatedSpanningTreeEdges m a} →
      ZMod m ⊕ PUnit.{1} :=
  fun e ↦ Fin.cases (Sum.inl e.1.1) (fun _ ↦ Sum.inr PUnit.unit) e.1.2

/-- Decode a left-loop code or the unique translated omitted-edge code. -/
def translatedNonTreeEdgeDecode (a : ZMod m) :
    ZMod m ⊕ PUnit.{1} →
      {e : (cyclicRoseCover m).Edge // e ∉ translatedSpanningTreeEdges m a}
  | Sum.inl v => ⟨(v, 0), by simp [translatedSpanningTreeEdges]⟩
  | Sum.inr _ => ⟨(lastVertex m + a, 1), by simp [translatedSpanningTreeEdges]⟩

theorem translatedNonTreeEdgeDecode_code (a : ZMod m)
    (e : {e : (cyclicRoseCover m).Edge // e ∉ translatedSpanningTreeEdges m a}) :
    translatedNonTreeEdgeDecode m a (translatedNonTreeEdgeCode m a e) = e := by
  rcases e with ⟨⟨v, i⟩, he⟩
  fin_cases i
  · rfl
  · have hv : v = lastVertex m + a := by
      by_contra hv
      exact he ⟨rfl, hv⟩
    subst v
    rfl

theorem translatedNonTreeEdgeCode_decode (a : ZMod m) (c : ZMod m ⊕ PUnit.{1}) :
    translatedNonTreeEdgeCode m a (translatedNonTreeEdgeDecode m a c) = c := by
  rcases c with (v | u)
  · rfl
  · cases u
    rfl

/-- Every translated non-tree basis is canonically `ZMod m ⊕ PUnit`: its `m` left loops and
its one omitted right edge. -/
def translatedNonTreeEdgeEquiv (a : ZMod m) :
    {e : (cyclicRoseCover m).Edge // e ∉ translatedSpanningTreeEdges m a} ≃
      ZMod m ⊕ PUnit.{1} where
  toFun := translatedNonTreeEdgeCode m a
  invFun := translatedNonTreeEdgeDecode m a
  left_inv := translatedNonTreeEdgeDecode_code m a
  right_inv := translatedNonTreeEdgeCode_decode m a

/-- Every member of the translated basis family has `m + 1` non-tree edges. -/
@[simp]
theorem translatedNonTreeEdge_card (a : ZMod m) :
    Nat.card {e : (cyclicRoseCover m).Edge // e ∉ translatedSpanningTreeEdges m a} =
      m + 1 := by
  rw [Nat.card_congr (translatedNonTreeEdgeEquiv m a), Nat.card_sum,
    Nat.card_zmod, Nat.card_unique]

/-- Every translated tree still has `m - 1` selected edges. -/
@[simp]
theorem translatedSpanningTreeEdge_card (a : ZMod m) :
    Nat.card (translatedSpanningTreeEdges m a) = m - 1 := by
  classical
  have hsplit :
      Nat.card (translatedSpanningTreeEdges m a) +
          Nat.card {e : (cyclicRoseCover m).Edge //
            e ∉ translatedSpanningTreeEdges m a} =
        Nat.card (cyclicRoseCover m).Edge := by
    rw [← Nat.card_sum]
    exact Nat.card_congr
      (Equiv.sumCompl (fun e ↦ e ∈ translatedSpanningTreeEdges m a))
  rw [translatedNonTreeEdge_card, edge_card] at hsplit
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  omega

/-- The deck-translated edge set is a spanning arborescence rooted at the translated base. -/
theorem translatedSpanningTreeEdges_isSpanningArborescenceAt (a : ZMod m) :
    (cyclicRoseCover m).IsSpanningArborescenceAt
      (translatedSpanningTreeEdges m a) a := by
  refine ⟨translatedSpanningTreeEdges_spansFromVertex m a,
    translatedSpanningTreeEdges_hasIncreasingRank m a, ?_⟩
  rw [translatedSpanningTreeEdge_card, vertex_card]
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  omega

/-- Deck translation gives an equivalence between the non-tree bases associated to `a` and
`a + b`.  It is not in general a permutation of the single basis associated to `0`. -/
def deckTranslationNonTreeEdge (a b : ZMod m) :
    {e : (cyclicRoseCover m).Edge // e ∉ translatedSpanningTreeEdges m a} ≃
      {e : (cyclicRoseCover m).Edge // e ∉ translatedSpanningTreeEdges m (a + b)} where
  toFun e := ⟨deckTranslationEdge m b e.1,
    (deckTranslationEdge_not_mem_translatedSpanningTreeEdges_iff m a b e.1).2 e.2⟩
  invFun e := ⟨deckTranslationEdge m (-b) e.1, by
    have h := (deckTranslationEdge_not_mem_translatedSpanningTreeEdges_iff
      m (a + b) (-b) e.1).2 e.2
    simpa only [add_neg_cancel_right] using h⟩
  left_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · simp [deckTranslationEdge_apply, add_assoc]
    · rfl
  right_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · simp [deckTranslationEdge_apply, add_assoc]
    · rfl

@[simp]
theorem deckTranslationNonTreeEdge_apply (a b : ZMod m)
    (e : {e : (cyclicRoseCover m).Edge // e ∉ translatedSpanningTreeEdges m a}) :
    (deckTranslationNonTreeEdge m a b e).1 = deckTranslationEdge m b e.1 :=
  rfl

/-- Under the explicit codes, deck translation translates the left-loop code and fixes the
distinguished omitted-right-edge code while moving to the translated basis. -/
theorem translatedNonTreeEdgeCode_deckTranslationNonTreeEdge (a b : ZMod m)
    (e : {e : (cyclicRoseCover m).Edge // e ∉ translatedSpanningTreeEdges m a}) :
    translatedNonTreeEdgeCode m (a + b) (deckTranslationNonTreeEdge m a b e) =
      Sum.map (deckTranslation m b) (Equiv.refl PUnit) (translatedNonTreeEdgeCode m a e) := by
  rcases e with ⟨⟨v, i⟩, he⟩
  fin_cases i <;> rfl

/-- Successive changes of translated basis add their deck parameters. -/
theorem deckTranslationNonTreeEdge_comp_apply (a b c : ZMod m)
    (e : {e : (cyclicRoseCover m).Edge // e ∉ translatedSpanningTreeEdges m a}) :
    (deckTranslationNonTreeEdge m (a + b) c
      (deckTranslationNonTreeEdge m a b e)).1 =
      (deckTranslationNonTreeEdge m a (b + c) e).1 := by
  apply Prod.ext
  · simp [deckTranslationEdge_apply, add_assoc]
  · rfl

/-- Deck translations restrict to genuine permutations of the left-loop part of every non-tree
basis. -/
def deckTranslationLeftEdge (a : ZMod m) :
    Equiv.Perm {e : (cyclicRoseCover m).Edge // e ∈ leftEdges m} where
  toFun e := ⟨deckTranslationEdge m a e.1, by
    change (deckTranslationEdge m a e.1).2 = 0
    exact (deckTranslationEdge_label m a e.1).trans e.2⟩
  invFun e := ⟨deckTranslationEdge m (-a) e.1, by
    change (deckTranslationEdge m (-a) e.1).2 = 0
    exact (deckTranslationEdge_label m (-a) e.1).trans e.2⟩
  left_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · simp [deckTranslationEdge_apply, add_assoc]
    · rfl
  right_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · simp [deckTranslationEdge_apply, add_assoc]
    · rfl

@[simp]
theorem deckTranslationLeftEdge_apply (a : ZMod m)
    (e : {e : (cyclicRoseCover m).Edge // e ∈ leftEdges m}) :
    (deckTranslationLeftEdge m a e).1 = deckTranslationEdge m a e.1 :=
  rfl

/-- The induced permutation of left-loop basis edges is free in its deck parameter. -/
theorem deckTranslationLeftEdge_fixed_iff (a : ZMod m)
    (e : {e : (cyclicRoseCover m).Edge // e ∈ leftEdges m}) :
    deckTranslationLeftEdge m a e = e ↔ a = 0 := by
  rw [Subtype.ext_iff]
  exact deckTranslationEdge_fixed_iff m a e.1

/-- The induced deck permutations act transitively on the left-loop part of the basis. -/
theorem exists_deckTranslationLeftEdge_eq
    (e f : {e : (cyclicRoseCover m).Edge // e ∈ leftEdges m}) :
    ∃ a : ZMod m, deckTranslationLeftEdge m a e = f := by
  obtain ⟨a, ha⟩ := exists_deckTranslationEdge_eq_of_label_eq m e.1 f.1
    (e.2.trans f.2.symm)
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact ha

/-- The deck orbit of the omitted right edge is the entire right-edge family, explaining why a
nontrivial deck translation cannot act on the fixed non-tree basis. -/
theorem range_deckTranslationEdge_wrap :
    Set.range (fun a : ZMod m ↦ deckTranslationEdge m a (lastVertex m, (1 : Fin 2))) =
      rightEdges m := by
  ext e
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · intro he
    refine ⟨e.1 - lastVertex m, ?_⟩
    apply Prod.ext
    · simp [deckTranslationEdge_apply]
    · exact he.symm

/-- Reduction modulo a divisor carries the omitted source `-1` to the omitted source `-1`. -/
@[simp]
theorem factor_lastVertex {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m) :
    factor h (lastVertex m) = lastVertex k := by
  have hmwrap := edgeTarget_lastVertex_one m
  have hkwrap := edgeTarget_lastVertex_one k
  change lastVertex m + (1 : ZMod m) = 0 at hmwrap
  change lastVertex k + (1 : ZMod k) = 0 at hkwrap
  change (ZMod.castHom h (ZMod k)) (lastVertex m) = lastVertex k
  apply add_right_cancel (b := (1 : ZMod k))
  calc
    (ZMod.castHom h (ZMod k)) (lastVertex m) + 1 =
        (ZMod.castHom h (ZMod k)) (lastVertex m + 1) := by
      simpa only [ZMod.castHom_apply, ZMod.cast_one (R := ZMod k) h] using
        (map_add (ZMod.castHom h (ZMod k)) (lastVertex m) 1).symm
    _ = 0 := by
      rw [hmwrap]
      exact map_zero _
    _ = lastVertex k + 1 := hkwrap.symm

/-- The omitted source in a translated basis is compatible with reduction of the deck
parameter. -/
@[simp]
theorem factor_lastVertex_add {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m)
    (a : ZMod m) :
    factor h (lastVertex m + a) = lastVertex k + factor h a := by
  change (ZMod.castHom h (ZMod k)) (lastVertex m + a) =
    lastVertex k + (ZMod.castHom h (ZMod k)) a
  calc
    (ZMod.castHom h (ZMod k)) (lastVertex m + a) =
        (ZMod.castHom h (ZMod k)) (lastVertex m) +
          (ZMod.castHom h (ZMod k)) a := map_add _ _ _
    _ = lastVertex k + (ZMod.castHom h (ZMod k)) a := by
      have hlast := factor_lastVertex h
      change (ZMod.castHom h (ZMod k)) (lastVertex m) = lastVertex k at hlast
      rw [hlast]

/-- Factor maps preserve the right-edge label on every translated tree edge.  They need not
preserve the chosen omitted edge, so the codomain here is the full right-edge family. -/
theorem factorEdge_mem_rightEdges_of_mem_translatedSpanningTreeEdges
    {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m) (a : ZMod m)
    {e : (cyclicRoseCover m).Edge}
    (he : e ∈ translatedSpanningTreeEdges m a) :
    factorEdge h e ∈ rightEdges k :=
  he.1

/-- If a factor image lies in the lower translated tree, then the source edge lay in the upper
translated tree. -/
theorem mem_translatedSpanningTreeEdges_of_factorEdge_mem
    {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m) (a : ZMod m)
    {e : (cyclicRoseCover m).Edge}
    (he : factorEdge h e ∈ translatedSpanningTreeEdges k (factor h a)) :
    e ∈ translatedSpanningTreeEdges m a := by
  rcases e with ⟨v, i⟩
  change i = 1 ∧ factor h v ≠ lastVertex k + factor h a at he
  refine ⟨he.1, ?_⟩
  intro hv
  change v = lastVertex m + a at hv
  apply he.2
  subst v
  exact factor_lastVertex_add h a

/-- Every edge of the lower translated tree has a preimage in the upper translated tree.  The
entire image may be larger, since other upper right edges can hit the lower omitted edge. -/
theorem translatedSpanningTreeEdges_subset_factorEdge_image
    {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m) (a : ZMod m) :
    translatedSpanningTreeEdges k (factor h a) ⊆
      factorEdge h '' translatedSpanningTreeEdges m a := by
  rintro ⟨w, i⟩ he
  change i = 1 ∧ w ≠ lastVertex k + factor h a at he
  obtain ⟨v, hv⟩ := factor_surjective h w
  refine ⟨(v, i), ?_, ?_⟩
  · refine ⟨he.1, ?_⟩
    intro hlast
    change v = lastVertex m + a at hlast
    subst v
    apply he.2
    exact hv.symm.trans (factor_lastVertex_add h a)
  · apply Prod.ext
    · exact hv
    · rfl

/-- A divisibility factor map sends a non-tree edge for the basis at `a` to a non-tree edge for
the basis at the reduced parameter. -/
theorem factorEdge_not_mem_translatedSpanningTreeEdges {k m : ℕ}
    [NeZero k] [NeZero m] (h : k ∣ m) (a : ZMod m)
    (e : (cyclicRoseCover m).Edge)
    (he : e ∉ translatedSpanningTreeEdges m a) :
    factorEdge h e ∉ translatedSpanningTreeEdges k (factor h a) := by
  rcases e with ⟨v, i⟩
  fin_cases i
  · simp [translatedSpanningTreeEdges]
  · have hv : v = lastVertex m + a := by
      by_contra hv
      exact he ⟨rfl, hv⟩
    subst v
    change ¬ ((1 : Fin 2) = 1 ∧
      factor h (lastVertex m + a) ≠ lastVertex k + factor h a)
    simp only [true_and, not_ne_iff]
    exact factor_lastVertex_add h a

/-- The factor map induced on the non-tree bases at compatible deck parameters. -/
def factorTranslatedNonTreeEdge {k m : ℕ} [NeZero k] [NeZero m]
    (h : k ∣ m) (a : ZMod m) :
    {e : (cyclicRoseCover m).Edge // e ∉ translatedSpanningTreeEdges m a} →
      {e : (cyclicRoseCover k).Edge //
        e ∉ translatedSpanningTreeEdges k (factor h a)} :=
  fun e ↦ ⟨factorEdge h e.1,
    factorEdge_not_mem_translatedSpanningTreeEdges h a e.1 e.2⟩

@[simp]
theorem factorTranslatedNonTreeEdge_apply {k m : ℕ} [NeZero k] [NeZero m]
    (h : k ∣ m) (a : ZMod m)
    (e : {e : (cyclicRoseCover m).Edge // e ∉ translatedSpanningTreeEdges m a}) :
    (factorTranslatedNonTreeEdge h a e).1 = factorEdge h e.1 :=
  rfl

/-- In explicit codes, the induced factor map reduces the left-loop source and fixes the unique
omitted-right-edge symbol. -/
theorem translatedNonTreeEdgeCode_factorTranslatedNonTreeEdge
    {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m) (a : ZMod m)
    (e : {e : (cyclicRoseCover m).Edge // e ∉ translatedSpanningTreeEdges m a}) :
    translatedNonTreeEdgeCode k (factor h a) (factorTranslatedNonTreeEdge h a e) =
      Sum.map (factor h) (Equiv.refl PUnit) (translatedNonTreeEdgeCode m a e) := by
  rcases e with ⟨⟨v, i⟩, he⟩
  fin_cases i <;> rfl

/-- The induced factor map on each translated non-tree basis is surjective.  Notice that its
fibres are not claimed to have constant cardinality: the single omitted right edge behaves
differently from the left-loop family. -/
theorem factorTranslatedNonTreeEdge_surjective {k m : ℕ}
    [NeZero k] [NeZero m] (h : k ∣ m) (a : ZMod m) :
    Function.Surjective (factorTranslatedNonTreeEdge h a) := by
  intro e
  generalize hc : translatedNonTreeEdgeCode k (factor h a) e = c
  rcases c with (v | u)
  · obtain ⟨w, hw⟩ := factor_surjective h v
    let d := translatedNonTreeEdgeDecode m a (Sum.inl w)
    refine ⟨d, ?_⟩
    apply (translatedNonTreeEdgeEquiv k (factor h a)).injective
    calc
      translatedNonTreeEdgeCode k (factor h a) (factorTranslatedNonTreeEdge h a d) =
          Sum.map (factor h) (Equiv.refl PUnit)
            (translatedNonTreeEdgeCode m a d) :=
        translatedNonTreeEdgeCode_factorTranslatedNonTreeEdge h a d
      _ = Sum.inl v := by
        change Sum.map (factor h) (Equiv.refl PUnit)
          (translatedNonTreeEdgeCode m a
            (translatedNonTreeEdgeDecode m a (Sum.inl w))) = Sum.inl v
        rw [translatedNonTreeEdgeCode_decode]
        change Sum.inl (factor h w) = Sum.inl v
        rw [hw]
      _ = translatedNonTreeEdgeCode k (factor h a) e := hc.symm
  · cases u
    let d := translatedNonTreeEdgeDecode m a (Sum.inr PUnit.unit)
    refine ⟨d, ?_⟩
    apply (translatedNonTreeEdgeEquiv k (factor h a)).injective
    calc
      translatedNonTreeEdgeCode k (factor h a) (factorTranslatedNonTreeEdge h a d) =
          Sum.map (factor h) (Equiv.refl PUnit)
            (translatedNonTreeEdgeCode m a d) :=
        translatedNonTreeEdgeCode_factorTranslatedNonTreeEdge h a d
      _ = Sum.inr PUnit.unit := by
        change Sum.map (factor h) (Equiv.refl PUnit)
          (translatedNonTreeEdgeCode m a
            (translatedNonTreeEdgeDecode m a (Sum.inr PUnit.unit))) =
          Sum.inr PUnit.unit
        rw [translatedNonTreeEdgeCode_decode]
        rfl
      _ = translatedNonTreeEdgeCode k (factor h a) e := hc.symm

/-- Factor maps compose on translated non-tree bases.  The equality is stated on underlying
edges because the two target subtype predicates differ by associativity of the divisibility
proofs and modular casts. -/
theorem factorTranslatedNonTreeEdge_comp_apply {k m d : ℕ}
    [NeZero k] [NeZero m] [NeZero d]
    (hkm : k ∣ m) (hmd : m ∣ d) (a : ZMod d)
    (e : {e : (cyclicRoseCover d).Edge // e ∉ translatedSpanningTreeEdges d a}) :
    (factorTranslatedNonTreeEdge hkm (factor hmd a)
      (factorTranslatedNonTreeEdge hmd a e)).1 =
      (factorTranslatedNonTreeEdge (dvd_trans hkm hmd) a e).1 := by
  apply Prod.ext
  · exact congrFun (factor_comp hkm hmd) e.1.1
  · rfl

/-- Deck translation and factor maps commute on the moving non-tree bases. -/
theorem factorTranslatedNonTreeEdge_deckTranslationNonTreeEdge
    {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m)
    (a b : ZMod m)
    (e : {e : (cyclicRoseCover m).Edge // e ∉ translatedSpanningTreeEdges m a}) :
    (factorTranslatedNonTreeEdge h (a + b)
      (deckTranslationNonTreeEdge m a b e)).1 =
      (deckTranslationNonTreeEdge k (factor h a) (factor h b)
        (factorTranslatedNonTreeEdge h a e)).1 := by
  exact factorEdge_deckTranslationEdge h b e.1

/-- Specialization to the originally chosen non-tree bases. -/
theorem factorEdge_not_mem_spanningTreeEdges {k m : ℕ}
    [NeZero k] [NeZero m] (h : k ∣ m) (e : (cyclicRoseCover m).Edge)
    (he : e ∉ spanningTreeEdges m) :
    factorEdge h e ∉ spanningTreeEdges k := by
  have he' : e ∉ translatedSpanningTreeEdges m 0 := by
    simpa using he
  have hout := factorEdge_not_mem_translatedSpanningTreeEdges h 0 e he'
  simpa using hout

/-- The factor map on the explicit non-tree basis from `CyclicGraphBasis`. -/
def factorNonTreeEdge {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m) :
    {e : (cyclicRoseCover m).Edge // e ∉ spanningTreeEdges m} →
      {e : (cyclicRoseCover k).Edge // e ∉ spanningTreeEdges k} :=
  fun e ↦ ⟨factorEdge h e.1, factorEdge_not_mem_spanningTreeEdges h e.1 e.2⟩

@[simp]
theorem factorNonTreeEdge_apply {k m : ℕ} [NeZero k] [NeZero m]
    (h : k ∣ m) (e : {e : (cyclicRoseCover m).Edge // e ∉ spanningTreeEdges m}) :
    (factorNonTreeEdge h e).1 = factorEdge h e.1 :=
  rfl

/-- The original `nonTreeEdgeCode` makes the induced factor map literal modular reduction on
left-loop codes and the identity on the omitted-right-edge code. -/
theorem nonTreeEdgeCode_factorNonTreeEdge {k m : ℕ}
    [NeZero k] [NeZero m] (h : k ∣ m)
    (e : {e : (cyclicRoseCover m).Edge // e ∉ spanningTreeEdges m}) :
    nonTreeEdgeCode k (factorNonTreeEdge h e) =
      Sum.map (factor h) (Equiv.refl PUnit) (nonTreeEdgeCode m e) := by
  rcases e with ⟨⟨v, i⟩, he⟩
  fin_cases i <;> rfl

/-- Divisibility factor maps compose on the original explicit non-tree bases. -/
theorem factorNonTreeEdge_comp_apply {k m d : ℕ}
    [NeZero k] [NeZero m] [NeZero d]
    (hkm : k ∣ m) (hmd : m ∣ d)
    (e : {e : (cyclicRoseCover d).Edge // e ∉ spanningTreeEdges d}) :
    factorNonTreeEdge hkm (factorNonTreeEdge hmd e) =
      factorNonTreeEdge (dvd_trans hkm hmd) e := by
  apply Subtype.ext
  apply Prod.ext
  · exact congrFun (factor_comp hkm hmd) e.1.1
  · rfl

/-- The induced map on the originally chosen non-tree bases is surjective. -/
theorem factorNonTreeEdge_surjective {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m) :
    Function.Surjective (factorNonTreeEdge h) := by
  intro e
  let e' : {e : (cyclicRoseCover k).Edge //
      e ∉ translatedSpanningTreeEdges k (factor h (0 : ZMod m))} :=
    ⟨e.1, by simpa using e.2⟩
  obtain ⟨d, hd⟩ := factorTranslatedNonTreeEdge_surjective h (0 : ZMod m) e'
  let d' : {e : (cyclicRoseCover m).Edge // e ∉ spanningTreeEdges m} :=
    ⟨d.1, by simpa using d.2⟩
  refine ⟨d', ?_⟩
  apply Subtype.ext
  simpa [factorNonTreeEdge, factorTranslatedNonTreeEdge, d', e'] using
    congrArg Subtype.val hd

end cyclicRoseCover

end SplittingSpheres
