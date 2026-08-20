/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CyclicGraph

/-!
# Boundary cycles of the cyclic rose as a ribbon graph

A labelled graph does not determine a thickened surface: one must also specify a cyclic order of
the incident half-edges.  This file records the order inherited from the planar twice-punctured
disk and computes the resulting boundary cycles in the cyclic rose cover.

At every vertex the four darts are ordered
`leftOut, leftIn, rightOut, rightIn`.  The boundary successor first rotates to the next dart in
this order and then reverses across that edge.  For the degree-`m` cyclic cover its orbits are:

* one fixed `leftOut` dart at every vertex;
* one cycle containing all `rightOut` darts;
* one cycle alternating between all `leftIn` and all `rightIn` darts.

Thus the combinatorial ribbon boundary has `m + 2` cycles.  This is deliberately only a finite
permutation calculation.  Identifying these cycles with boundary circles of the planar power
pullback still requires a ribbon-thickening or compact-surface classification theorem.
-/

@[expose] public section

open Function

noncomputable section

namespace SplittingSpheres

/-- The four oriented half-edge positions in the planar cyclic order at a rose vertex. -/
inductive RoseRibbonSide
  | leftOut
  | leftIn
  | rightOut
  | rightIn
  deriving DecidableEq

namespace RoseRibbonSide

/-- Counterclockwise rotation in the chosen planar order. -/
def rotate : Equiv.Perm RoseRibbonSide where
  toFun
    | leftOut => leftIn
    | leftIn => rightOut
    | rightOut => rightIn
    | rightIn => leftOut
  invFun
    | leftOut => rightIn
    | leftIn => leftOut
    | rightOut => leftIn
    | rightIn => rightOut
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

@[simp] theorem rotate_leftOut : rotate leftOut = leftIn := rfl
@[simp] theorem rotate_leftIn : rotate leftIn = rightOut := rfl
@[simp] theorem rotate_rightOut : rotate rightOut = rightIn := rfl
@[simp] theorem rotate_rightIn : rotate rightIn = leftOut := rfl

end RoseRibbonSide

namespace RoseCover

/-- A ribbon dart is a vertex together with one of the four oriented half-edge positions. -/
abbrev RibbonDart (C : RoseCover) := C.Vertex × RoseRibbonSide

/-- Reverse a dart across its underlying edge. -/
def reverseRibbonDartFun (C : RoseCover) : C.RibbonDart → C.RibbonDart
  | (v, .leftOut) => (C.step 0 v, .leftIn)
  | (v, .leftIn) => ((C.step 0).symm v, .leftOut)
  | (v, .rightOut) => (C.step 1 v, .rightIn)
  | (v, .rightIn) => ((C.step 1).symm v, .rightOut)

/-- Reversing a ribbon dart across its edge is an involutive permutation. -/
def reverseRibbonDart (C : RoseCover) : Equiv.Perm C.RibbonDart where
  toFun := C.reverseRibbonDartFun
  invFun := C.reverseRibbonDartFun
  left_inv d := by
    rcases d with ⟨v, s⟩
    cases s <;> simp [reverseRibbonDartFun]
  right_inv d := by
    rcases d with ⟨v, s⟩
    cases s <;> simp [reverseRibbonDartFun]

@[simp]
theorem reverseRibbonDart_leftOut (C : RoseCover) (v : C.Vertex) :
    C.reverseRibbonDart (v, .leftOut) = (C.step 0 v, .leftIn) := rfl

@[simp]
theorem reverseRibbonDart_leftIn (C : RoseCover) (v : C.Vertex) :
    C.reverseRibbonDart (v, .leftIn) = ((C.step 0).symm v, .leftOut) := rfl

@[simp]
theorem reverseRibbonDart_rightOut (C : RoseCover) (v : C.Vertex) :
    C.reverseRibbonDart (v, .rightOut) = (C.step 1 v, .rightIn) := rfl

@[simp]
theorem reverseRibbonDart_rightIn (C : RoseCover) (v : C.Vertex) :
    C.reverseRibbonDart (v, .rightIn) = ((C.step 1).symm v, .rightOut) := rfl

/-- Rotate a ribbon dart at its current vertex. -/
def rotateRibbonDart (C : RoseCover) : Equiv.Perm C.RibbonDart :=
  (Equiv.refl C.Vertex).prodCongr RoseRibbonSide.rotate

/-- The boundary successor of the chosen ribbon structure: rotate at the vertex, then reverse
across the resulting edge. -/
def ribbonBoundaryPerm (C : RoseCover) : Equiv.Perm C.RibbonDart :=
  C.rotateRibbonDart.trans C.reverseRibbonDart

@[simp]
theorem ribbonBoundaryPerm_leftOut (C : RoseCover) (v : C.Vertex) :
    C.ribbonBoundaryPerm (v, .leftOut) = ((C.step 0).symm v, .leftOut) := rfl

@[simp]
theorem ribbonBoundaryPerm_leftIn (C : RoseCover) (v : C.Vertex) :
    C.ribbonBoundaryPerm (v, .leftIn) = (C.step 1 v, .rightIn) := rfl

@[simp]
theorem ribbonBoundaryPerm_rightOut (C : RoseCover) (v : C.Vertex) :
    C.ribbonBoundaryPerm (v, .rightOut) = ((C.step 1).symm v, .rightOut) := rfl

@[simp]
theorem ribbonBoundaryPerm_rightIn (C : RoseCover) (v : C.Vertex) :
    C.ribbonBoundaryPerm (v, .rightIn) = (C.step 0 v, .leftIn) := rfl

/-- Directed reachability under repeated applications of the ribbon boundary successor. -/
abbrev RibbonBoundaryReachable (C : RoseCover) (d e : C.RibbonDart) : Prop :=
  Relation.ReflTransGen (fun x y ↦ C.ribbonBoundaryPerm x = y) d e

theorem ribbonBoundaryReachable_refl (C : RoseCover) (d : C.RibbonDart) :
    C.RibbonBoundaryReachable d d :=
  Relation.ReflTransGen.refl

theorem ribbonBoundaryReachable_step (C : RoseCover) (d : C.RibbonDart) :
    C.RibbonBoundaryReachable d (C.ribbonBoundaryPerm d) :=
  Relation.ReflTransGen.single rfl

theorem RibbonBoundaryReachable.trans {C : RoseCover} {d e f : C.RibbonDart}
    (hde : C.RibbonBoundaryReachable d e) (hef : C.RibbonBoundaryReachable e f) :
    C.RibbonBoundaryReachable d f :=
  Relation.ReflTransGen.trans hde hef

end RoseCover

namespace cyclicRoseCover

variable (m : ℕ) [NeZero m]

/-- Labels for the three kinds of ribbon boundary cycles: `m` left circles, one right circle,
and one outer circle. -/
abbrev RibbonBoundaryCode := ZMod m ⊕ Fin 2

/-- The explicit boundary-cycle label of a cyclic-cover ribbon dart. -/
def ribbonBoundaryCode : (cyclicRoseCover m).RibbonDart → RibbonBoundaryCode m
  | (v, .leftOut) => Sum.inl v
  | (_, .rightOut) => Sum.inr 0
  | (_, .leftIn) => Sum.inr 1
  | (_, .rightIn) => Sum.inr 1

@[simp]
theorem ribbonBoundaryCode_leftOut (v : ZMod m) :
    ribbonBoundaryCode m (v, .leftOut) = Sum.inl v := rfl

@[simp]
theorem ribbonBoundaryCode_leftIn (v : ZMod m) :
    ribbonBoundaryCode m (v, .leftIn) = Sum.inr 1 := rfl

@[simp]
theorem ribbonBoundaryCode_rightOut (v : ZMod m) :
    ribbonBoundaryCode m (v, .rightOut) = Sum.inr 0 := rfl

@[simp]
theorem ribbonBoundaryCode_rightIn (v : ZMod m) :
    ribbonBoundaryCode m (v, .rightIn) = Sum.inr 1 := rfl

@[simp]
theorem ribbonBoundaryPerm_leftOut (v : ZMod m) :
    (cyclicRoseCover m).ribbonBoundaryPerm (v, .leftOut) = (v, .leftOut) := by
  rw [RoseCover.ribbonBoundaryPerm_leftOut]
  simp [cyclicRoseCover]

@[simp]
theorem ribbonBoundaryPerm_leftIn (v : ZMod m) :
    (cyclicRoseCover m).ribbonBoundaryPerm (v, .leftIn) = (v + 1, .rightIn) := by
  rw [RoseCover.ribbonBoundaryPerm_leftIn]
  exact Prod.ext (step_one m v) rfl

@[simp]
theorem ribbonBoundaryPerm_rightOut (v : ZMod m) :
    (cyclicRoseCover m).ribbonBoundaryPerm (v, .rightOut) = (v - 1, .rightOut) := by
  rw [RoseCover.ribbonBoundaryPerm_rightOut]
  apply Prod.ext
  · change (Equiv.addRight (1 : ZMod m)).symm v = v - 1
    simp [sub_eq_add_neg]
  · rfl

@[simp]
theorem ribbonBoundaryPerm_rightIn (v : ZMod m) :
    (cyclicRoseCover m).ribbonBoundaryPerm (v, .rightIn) = (v, .leftIn) := by
  rw [RoseCover.ribbonBoundaryPerm_rightIn]
  exact Prod.ext (step_zero m v) rfl

/-- The cycle label is invariant under the ribbon boundary successor. -/
theorem ribbonBoundaryCode_perm (d : (cyclicRoseCover m).RibbonDart) :
    ribbonBoundaryCode m ((cyclicRoseCover m).ribbonBoundaryPerm d) =
      ribbonBoundaryCode m d := by
  rcases d with ⟨v, s⟩
  cases s with
  | leftOut => rw [cyclicRoseCover.ribbonBoundaryPerm_leftOut]
  | leftIn => rw [cyclicRoseCover.ribbonBoundaryPerm_leftIn]; rfl
  | rightOut => rw [cyclicRoseCover.ribbonBoundaryPerm_rightOut]; rfl
  | rightIn => rw [cyclicRoseCover.ribbonBoundaryPerm_rightIn]; rfl

/-- Every declared boundary-cycle label is represented by a ribbon dart. -/
theorem ribbonBoundaryCode_surjective : Surjective (ribbonBoundaryCode m) := by
  rintro (v | i)
  · exact ⟨(v, .leftOut), rfl⟩
  · fin_cases i
    · exact ⟨(0, .rightOut), rfl⟩
    · exact ⟨(0, .leftIn), rfl⟩

/-- A graph deck translation acts on ribbon darts by translating the vertex and preserving its
position in the cyclic order. -/
def deckTranslationRibbonDart (a : ZMod m) :
    Equiv.Perm (cyclicRoseCover m).RibbonDart :=
  (deckTranslation m a).prodCongr (Equiv.refl RoseRibbonSide)

@[simp]
theorem deckTranslationRibbonDart_apply
    (a : ZMod m) (d : (cyclicRoseCover m).RibbonDart) :
    deckTranslationRibbonDart m a d = (d.1 + a, d.2) :=
  rfl

/-- Deck translation commutes with the ribbon boundary successor. -/
theorem deckTranslationRibbonDart_boundaryPerm
    (a : ZMod m) (d : (cyclicRoseCover m).RibbonDart) :
    deckTranslationRibbonDart m a ((cyclicRoseCover m).ribbonBoundaryPerm d) =
      (cyclicRoseCover m).ribbonBoundaryPerm (deckTranslationRibbonDart m a d) := by
  rcases d with ⟨v, s⟩
  cases s with
  | leftOut =>
      simp only [deckTranslationRibbonDart_apply]
      rw [cyclicRoseCover.ribbonBoundaryPerm_leftOut,
        cyclicRoseCover.ribbonBoundaryPerm_leftOut]
  | leftIn =>
      simp only [deckTranslationRibbonDart_apply]
      rw [cyclicRoseCover.ribbonBoundaryPerm_leftIn,
        cyclicRoseCover.ribbonBoundaryPerm_leftIn]
      exact Prod.ext (add_right_comm v 1 a) rfl
  | rightOut =>
      simp only [deckTranslationRibbonDart_apply]
      rw [cyclicRoseCover.ribbonBoundaryPerm_rightOut,
        cyclicRoseCover.ribbonBoundaryPerm_rightOut]
      apply Prod.ext
      · simpa only [Prod.fst, sub_eq_add_neg] using add_right_comm v (-1) a
      · rfl
  | rightIn =>
      simp only [deckTranslationRibbonDart_apply]
      rw [cyclicRoseCover.ribbonBoundaryPerm_rightIn,
        cyclicRoseCover.ribbonBoundaryPerm_rightIn]

/-- The induced deck permutation on boundary-cycle labels: it translates the `m` left labels
and fixes the right and outer labels. -/
def deckTranslationRibbonBoundaryCode (a : ZMod m) :
    Equiv.Perm (RibbonBoundaryCode m) :=
  (deckTranslation m a).sumCongr (Equiv.refl (Fin 2))

@[simp]
theorem deckTranslationRibbonBoundaryCode_left
    (a v : ZMod m) :
    deckTranslationRibbonBoundaryCode m a (Sum.inl v) = Sum.inl (v + a) :=
  rfl

@[simp]
theorem deckTranslationRibbonBoundaryCode_right
    (a : ZMod m) :
    deckTranslationRibbonBoundaryCode m a (Sum.inr 0) = Sum.inr 0 :=
  rfl

@[simp]
theorem deckTranslationRibbonBoundaryCode_outer
    (a : ZMod m) :
    deckTranslationRibbonBoundaryCode m a (Sum.inr 1) = Sum.inr 1 :=
  rfl

/-- The explicit boundary-cycle classification is equivariant for deck translations. -/
theorem ribbonBoundaryCode_deckTranslation
    (a : ZMod m) (d : (cyclicRoseCover m).RibbonDart) :
    ribbonBoundaryCode m (deckTranslationRibbonDart m a d) =
      deckTranslationRibbonBoundaryCode m a (ribbonBoundaryCode m d) := by
  rcases d with ⟨v, s⟩
  cases s <;> rfl

/-- The deck group acts transitively on the `m` left boundary-cycle labels. -/
theorem exists_deckTranslationRibbonBoundaryCode_left_eq
    (v w : ZMod m) :
    ∃ a : ZMod m,
      deckTranslationRibbonBoundaryCode m a (Sum.inl v) = Sum.inl w := by
  exact ⟨w - v, by simp⟩

private theorem boundaryReachable_code_eq
    {d e : (cyclicRoseCover m).RibbonDart}
    (h : (cyclicRoseCover m).RibbonBoundaryReachable d e) :
    ribbonBoundaryCode m d = ribbonBoundaryCode m e := by
  induction h with
  | refl => rfl
  | tail hxy hstep ih =>
      rw [← hstep, ribbonBoundaryCode_perm]
      exact ih

private theorem rightBoundaryReachable_nat (v : ZMod m) : ∀ n : ℕ,
    (cyclicRoseCover m).RibbonBoundaryReachable (v, .rightOut)
      (v - (n : ZMod m), .rightOut)
  | 0 => by simpa using (cyclicRoseCover m).ribbonBoundaryReachable_refl (v, .rightOut)
  | n + 1 => by
      have h := rightBoundaryReachable_nat v n
      have hstep := ribbonBoundaryPerm_rightOut m (v - (n : ZMod m))
      simpa [Nat.cast_add, Nat.cast_one, sub_sub] using h.tail hstep

private theorem rightBoundaryReachable (v w : ZMod m) :
    (cyclicRoseCover m).RibbonBoundaryReachable (v, .rightOut) (w, .rightOut) := by
  have h := rightBoundaryReachable_nat m v (v - w).val
  simpa [ZMod.natCast_zmod_val, sub_sub] using h

private theorem outerLeftBoundaryReachable_nat (v : ZMod m) : ∀ n : ℕ,
    (cyclicRoseCover m).RibbonBoundaryReachable (v, .leftIn)
      (v + (n : ZMod m), .leftIn)
  | 0 => by simpa using (cyclicRoseCover m).ribbonBoundaryReachable_refl (v, .leftIn)
  | n + 1 => by
      have h := outerLeftBoundaryReachable_nat v n
      have hfirst := ribbonBoundaryPerm_leftIn m (v + (n : ZMod m))
      have hsecond := ribbonBoundaryPerm_rightIn m (v + (n : ZMod m) + 1)
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using (h.tail hfirst).tail hsecond

private theorem outerLeftBoundaryReachable (v w : ZMod m) :
    (cyclicRoseCover m).RibbonBoundaryReachable (v, .leftIn) (w, .leftIn) := by
  have h := outerLeftBoundaryReachable_nat m v (w - v).val
  simpa [ZMod.natCast_zmod_val] using h

private theorem outerBoundaryReachable
    (v w : ZMod m) (s t : RoseRibbonSide)
    (hs : s = .leftIn ∨ s = .rightIn) (ht : t = .leftIn ∨ t = .rightIn) :
    (cyclicRoseCover m).RibbonBoundaryReachable (v, s) (w, t) := by
  rcases hs with rfl | rfl
  · rcases ht with rfl | rfl
    · exact outerLeftBoundaryReachable m v w
    · exact (outerLeftBoundaryReachable m v (w - 1)).tail
        (by simpa using ribbonBoundaryPerm_leftIn m (w - 1))
  · rcases ht with rfl | rfl
    · exact ((cyclicRoseCover m).ribbonBoundaryReachable_step (v, .rightIn)).trans
        (outerLeftBoundaryReachable m v w)
    · exact (((cyclicRoseCover m).ribbonBoundaryReachable_step (v, .rightIn)).trans
        (outerLeftBoundaryReachable m v (w - 1))).tail
          (by simpa using ribbonBoundaryPerm_leftIn m (w - 1))

/-- Two darts lie in the same orbit of the boundary successor exactly when they have the same
explicit boundary-cycle label. -/
theorem ribbonBoundaryReachable_iff_code_eq
    (d e : (cyclicRoseCover m).RibbonDart) :
    (cyclicRoseCover m).RibbonBoundaryReachable d e ↔
      ribbonBoundaryCode m d = ribbonBoundaryCode m e := by
  constructor
  · exact boundaryReachable_code_eq m
  · rcases d with ⟨v, s⟩
    rcases e with ⟨w, t⟩
    intro hcode
    cases s with
    | leftOut =>
        cases t with
        | leftOut =>
            change (Sum.inl v : RibbonBoundaryCode m) = Sum.inl w at hcode
            have hvw : v = w := Sum.inl.inj hcode
            subst w
            exact (cyclicRoseCover m).ribbonBoundaryReachable_refl (v, .leftOut)
        | leftIn =>
            change (Sum.inl v : RibbonBoundaryCode m) = Sum.inr 1 at hcode
            contradiction
        | rightOut =>
            change (Sum.inl v : RibbonBoundaryCode m) = Sum.inr 0 at hcode
            contradiction
        | rightIn =>
            change (Sum.inl v : RibbonBoundaryCode m) = Sum.inr 1 at hcode
            contradiction
    | leftIn =>
        cases t with
        | leftOut =>
            change (Sum.inr 1 : RibbonBoundaryCode m) = Sum.inl w at hcode
            contradiction
        | leftIn =>
            exact outerBoundaryReachable m v w .leftIn .leftIn (Or.inl rfl) (Or.inl rfl)
        | rightOut =>
            change (Sum.inr 1 : RibbonBoundaryCode m) = Sum.inr 0 at hcode
            simp at hcode
        | rightIn =>
            exact outerBoundaryReachable m v w .leftIn .rightIn (Or.inl rfl) (Or.inr rfl)
    | rightOut =>
        cases t with
        | leftOut =>
            change (Sum.inr 0 : RibbonBoundaryCode m) = Sum.inl w at hcode
            contradiction
        | leftIn =>
            change (Sum.inr 0 : RibbonBoundaryCode m) = Sum.inr 1 at hcode
            simp at hcode
        | rightOut => exact rightBoundaryReachable m v w
        | rightIn =>
            change (Sum.inr 0 : RibbonBoundaryCode m) = Sum.inr 1 at hcode
            simp at hcode
    | rightIn =>
        cases t with
        | leftOut =>
            change (Sum.inr 1 : RibbonBoundaryCode m) = Sum.inl w at hcode
            contradiction
        | leftIn =>
            exact outerBoundaryReachable m v w .rightIn .leftIn (Or.inr rfl) (Or.inl rfl)
        | rightOut =>
            change (Sum.inr 1 : RibbonBoundaryCode m) = Sum.inr 0 at hcode
            simp at hcode
        | rightIn =>
            exact outerBoundaryReachable m v w .rightIn .rightIn (Or.inr rfl) (Or.inr rfl)

/-- The explicit type of ribbon boundary cycles has cardinality `m + 2`. -/
@[simp]
theorem ribbonBoundaryCode_card : Nat.card (RibbonBoundaryCode m) = m + 2 := by
  rw [Nat.card_sum, Nat.card_zmod, Nat.card_fin]

/-- The degree-`m` cyclic rose with the chosen planar ribbon order has exactly `m + 2`
combinatorial boundary cycles. -/
theorem exists_boundaryCycleClassification :
    ∃ code : (cyclicRoseCover m).RibbonDart → RibbonBoundaryCode m,
      Surjective code ∧
        (∀ d e, (cyclicRoseCover m).RibbonBoundaryReachable d e ↔ code d = code e) ∧
        Nat.card (RibbonBoundaryCode m) = m + 2 :=
  ⟨ribbonBoundaryCode m, ribbonBoundaryCode_surjective m,
    ribbonBoundaryReachable_iff_code_eq m, ribbonBoundaryCode_card m⟩

end cyclicRoseCover

end SplittingSpheres
