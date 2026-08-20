/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The cyclic graph encoding of the cover character

The two generators of the relevant fundamental group are encoded by a rose with a left and a
right loop. Its degree-`m` cyclic cover has vertices `ZMod m`; the left edge is a loop at every
vertex and the right edge moves a vertex by `+1`. This file isolates that finite graph
calculation from the later ribbon-surface and partial-spin constructions. It does not assert that
the compact four-dimensional exterior deformation retracts onto this graph.

A `RoseCover` records the two edge permutations. Thus the local covering condition is built into
the data: at every vertex and for each label there is one outgoing and one incoming edge. We prove
connectedness of the cyclic example, its `m` vertices, its `2m` edges, cycle rank `m+1`, and the
factor maps induced by divisibility.
-/

@[expose] public section

noncomputable section

namespace SplittingSpheres

universe u

/-- A finite labelled covering graph of the rose with two loops. For every label, `step` is a
permutation, encoding the unique lift of both orientations of that labelled edge. -/
structure RoseCover where
  Vertex : Type u
  [finiteVertex : Finite Vertex]
  base : Vertex
  step : Fin 2 → Equiv.Perm Vertex

namespace RoseCover

instance (C : RoseCover) : Finite C.Vertex := C.finiteVertex

/-- Oriented edges are a starting vertex together with one of the two rose-edge labels. -/
abbrev Edge (C : RoseCover) := C.Vertex × Fin 2

/-- Initial vertex of an oriented edge. -/
def edgeSource (C : RoseCover) (e : C.Edge) : C.Vertex := e.1

/-- Terminal vertex of an oriented edge. -/
def edgeTarget (C : RoseCover) (e : C.Edge) : C.Vertex := C.step e.2 e.1

/-- The unique outgoing edge at `v` with label `i`. -/
def edgeAt (C : RoseCover) (v : C.Vertex) (i : Fin 2) : C.Edge := (v, i)

@[simp]
theorem edgeSource_edgeAt (C : RoseCover) (v : C.Vertex) (i : Fin 2) :
    C.edgeSource (C.edgeAt v i) = v := rfl

@[simp]
theorem edgeTarget_edgeAt (C : RoseCover) (v : C.Vertex) (i : Fin 2) :
    C.edgeTarget (C.edgeAt v i) = C.step i v := rfl

/-- Edges leaving a fixed vertex are canonically identified with the two base labels. -/
def outgoingEquiv (C : RoseCover) (v : C.Vertex) :
    {e : C.Edge // C.edgeSource e = v} ≃ Fin 2 where
  toFun e := e.1.2
  invFun i := ⟨C.edgeAt v i, rfl⟩
  left_inv e := by
    apply Subtype.ext
    exact Prod.ext e.2.symm rfl
  right_inv _ := rfl

/-- Edges arriving at a fixed vertex are canonically identified with the two base labels. -/
def incomingEquiv (C : RoseCover) (v : C.Vertex) :
    {e : C.Edge // C.edgeTarget e = v} ≃ Fin 2 where
  toFun e := e.1.2
  invFun i := ⟨((C.step i).symm v, i), by simp [edgeTarget]⟩
  left_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · exact (C.step e.1.2).injective (by simpa [edgeTarget] using e.2.symm)
    · rfl
  right_inv _ := rfl

/-- A based morphism of rose covers commutes with both edge permutations. -/
structure Hom (C D : RoseCover) where
  toFun : C.Vertex → D.Vertex
  map_base : toFun C.base = D.base
  map_step : ∀ i v, toFun (C.step i v) = D.step i (toFun v)

instance {C D : RoseCover} : CoeFun (Hom C D) (fun _ ↦ C.Vertex → D.Vertex) :=
  ⟨Hom.toFun⟩

/-- Directed reachability from the chosen base vertex. -/
def ReachableFromBase (C : RoseCover) (v : C.Vertex) : Prop :=
  Relation.ReflTransGen (fun x y ↦ ∃ i, C.step i x = y) C.base v

/-- A based rose cover is connected when every vertex is reachable from its base. -/
def IsConnected (C : RoseCover) : Prop := ∀ v, C.ReachableFromBase v

/-- The Euler cycle-rank expression for a finite connected graph. Its later topological
interpretation is supplied by the ribbon-surface development. -/
def cycleRank (C : RoseCover) : ℕ := Nat.card C.Edge - Nat.card C.Vertex + 1

end RoseCover

/-- The graph of the degree-`m` cyclic cover: the left label fixes vertices and the right label
adds one modulo `m`. -/
abbrev cyclicRoseCover (m : ℕ) [NeZero m] : RoseCover where
  Vertex := ZMod m
  base := 0
  step i := if i = 0 then Equiv.refl _ else Equiv.addRight 1

namespace cyclicRoseCover

variable (m : ℕ) [NeZero m]

@[simp]
theorem step_zero (v : (cyclicRoseCover m).Vertex) :
    (cyclicRoseCover m).step 0 v = v := by
  simp [cyclicRoseCover]

@[simp]
theorem step_one (v : (cyclicRoseCover m).Vertex) :
    (cyclicRoseCover m).step 1 v = v + 1 := by
  simp [cyclicRoseCover]

private theorem reachable_nat : ∀ n : ℕ,
    (cyclicRoseCover m).ReachableFromBase (n : ZMod m)
  | 0 => by
      rw [RoseCover.ReachableFromBase]
      have hbase : (cyclicRoseCover m).base = (0 : ZMod m) := rfl
      have hcast : ((0 : ℕ) : ZMod m) = 0 := by simp
      rw [hbase, hcast]
  | n + 1 => (reachable_nat n).tail ⟨1, by simp [Nat.cast_add, Nat.cast_one]⟩

/-- The right-hand cycle reaches every vertex, so the cyclic cover graph is connected. -/
theorem isConnected : (cyclicRoseCover m).IsConnected := by
  intro v
  rw [← ZMod.natCast_zmod_val v]
  exact reachable_nat m v.val

@[simp]
theorem vertex_card : Nat.card (cyclicRoseCover m).Vertex = m :=
  Nat.card_zmod m

@[simp]
theorem edge_card : Nat.card (cyclicRoseCover m).Edge = 2 * m := by
  rw [Nat.card_prod, Nat.card_zmod, Nat.card_fin]
  omega

/-- The connected cyclic graph has cycle rank `m+1`.  Relating this number to the summands of
the four-dimensional partial spin requires a separate ribbon-surface and handle theorem. -/
theorem cycleRank_eq : (cyclicRoseCover m).cycleRank = m + 1 := by
  rw [RoseCover.cycleRank, edge_card, vertex_card]
  omega

/-- Reduction modulo a divisor gives the graph factor map between cyclic covers. -/
def factor {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m) :
    RoseCover.Hom (cyclicRoseCover m) (cyclicRoseCover k) where
  toFun := ZMod.castHom h (ZMod k)
  map_base := map_zero _
  map_step i v := by
    fin_cases i
    · simp
    · simp [map_add, ZMod.cast_one (R := ZMod k) h]

@[simp]
theorem factor_apply {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m) (v : ZMod m) :
    factor h v = ZMod.cast v := rfl

/-- The factor map is onto on vertices. -/
theorem factor_surjective {k m : ℕ} [NeZero k] [NeZero m] (h : k ∣ m) :
    Function.Surjective (factor h) :=
  ZMod.castHom_surjective h

/-- Divisibility factor maps compose exactly as the corresponding modular reductions. -/
theorem factor_comp {k m d : ℕ} [NeZero k] [NeZero m] [NeZero d]
    (hkm : k ∣ m) (hmd : m ∣ d) :
    (factor hkm : ZMod m → ZMod k) ∘ (factor hmd : ZMod d → ZMod m) =
      (factor (dvd_trans hkm hmd) : ZMod d → ZMod k) := by
  funext v
  exact DFunLike.congr_fun (ZMod.castHom_comp hkm hmd) v

/-- Translation of the cyclic vertices is a deck transformation of the labelled graph. -/
abbrev deckTranslation (a : ZMod m) : Equiv.Perm (cyclicRoseCover m).Vertex :=
  Equiv.addRight a

@[simp]
theorem deckTranslation_apply (a v : ZMod m) : deckTranslation m a v = v + a := rfl

/-- Deck translations commute with both labelled edge permutations. -/
theorem deckTranslation_comm_step (a : ZMod m) (i : Fin 2) (v : ZMod m) :
    deckTranslation m a ((cyclicRoseCover m).step i v) =
      (cyclicRoseCover m).step i (deckTranslation m a v) := by
  fin_cases i
  · simp
  · simp [add_assoc, add_comm a 1]

/-- A deck translation sends the base vertex to its translation parameter. -/
@[simp]
theorem deckTranslation_base (a : ZMod m) : deckTranslation m a 0 = a := by
  simp

/-- Distinct translation parameters give distinct deck transformations. -/
theorem deckTranslation_injective : Function.Injective (deckTranslation m) := by
  intro a b h
  have h0 := Equiv.ext_iff.mp h (0 : ZMod m)
  simpa using h0

end cyclicRoseCover

end SplittingSpheres
