/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Tactic

/-!
# Conjugacy classes of the generalized quaternion group of order sixteen

The five cyclic classes are represented by `a⁰`, `a⁴`, `a¹`, `a²`, and
`a³`; the reflection coset splits into the even and odd classes represented
by `x` and `xa`.  The finite certificate below proves that every element has
exactly one of these seven representatives.
-/

namespace McKayConjecture
namespace QuaternionGroupFour

noncomputable section

/-- Finite index for the seven conjugacy classes of `QuaternionGroup 4`. -/
abbrev ConjugacyClass := Fin 7

/-- A representative of each conjugacy class. -/
def conjugacyRepresentative :
    ConjugacyClass → QuaternionGroup 4 :=
  ![
    QuaternionGroup.a 0,
    QuaternionGroup.a 4,
    QuaternionGroup.a 1,
    QuaternionGroup.a 2,
    QuaternionGroup.a 3,
    QuaternionGroup.xa 0,
    QuaternionGroup.xa 1
  ]

/-- The class invariant: cyclic exponents are identified up to sign and
reflection exponents are identified by parity. -/
def conjugacyClassIndex :
    QuaternionGroup 4 → ConjugacyClass
  | QuaternionGroup.a i =>
      if i = 0 then 0
      else if i = 4 then 1
      else if i = 1 ∨ i = 7 then 2
      else if i = 2 ∨ i = 6 then 3
      else 4
  | QuaternionGroup.xa i =>
      if i.val % 2 = 0 then 5 else 6

/-- Conjugating an element does not change its displayed class index. -/
theorem conjugacyClassIndex_conj
    (x g : QuaternionGroup 4) :
    conjugacyClassIndex (x * g * x⁻¹) =
      conjugacyClassIndex g := by
  rcases x with i | i <;>
    rcases g with j | j <;>
    fin_cases i <;> fin_cases j <;> decide

/-- Each element is conjugate to the representative selected by its class
index. -/
theorem isConj_conjugacyRepresentative
    (g : QuaternionGroup 4) :
    IsConj g
      (conjugacyRepresentative (conjugacyClassIndex g)) := by
  rcases g with i | i <;> fin_cases i <;>
    rw [isConj_iff]
  all_goals
    first
    | exact ⟨1, by decide⟩
    | exact ⟨QuaternionGroup.xa 0, by decide⟩
    | exact ⟨QuaternionGroup.a 1, by decide⟩
    | exact ⟨QuaternionGroup.a 2, by decide⟩
    | exact ⟨QuaternionGroup.a 3, by decide⟩

/-- The displayed representatives have the expected pairwise-distinct class
indices. -/
@[simp]
theorem conjugacyClassIndex_representative
    (c : ConjugacyClass) :
    conjugacyClassIndex (conjugacyRepresentative c) = c := by
  fin_cases c <;> decide

/-- Every element of `QuaternionGroup 4` is conjugate to exactly one of the
seven displayed representatives. -/
theorem existsUnique_conjugacyClass
    (g : QuaternionGroup 4) :
    ∃! c : ConjugacyClass,
      IsConj g (conjugacyRepresentative c) := by
  refine
    ⟨conjugacyClassIndex g,
      isConj_conjugacyRepresentative g, ?_⟩
  intro c hc
  obtain ⟨x, hx⟩ := isConj_iff.mp hc
  have hindex := conjugacyClassIndex_conj x g
  rw [hx, conjugacyClassIndex_representative] at hindex
  exact hindex

/-- The displayed representatives enumerate the abstract conjugacy-class
quotient without repetition. -/
def conjugacyClassEquiv :
    ConjugacyClass ≃ ConjClasses (QuaternionGroup 4) :=
  Equiv.ofBijective
    (fun c => ConjClasses.mk (conjugacyRepresentative c)) <| by
      constructor
      · intro c d h
        have hcd :
            IsConj
              (conjugacyRepresentative c)
              (conjugacyRepresentative d) :=
          ConjClasses.mk_eq_mk_iff_isConj.mp h
        obtain ⟨e, he, heUnique⟩ :=
          existsUnique_conjugacyClass
            (conjugacyRepresentative c)
        exact
          (heUnique c (IsConj.refl _)).trans
            (heUnique d hcd).symm
      · intro q
        refine Quotient.inductionOn' q ?_
        intro g
        obtain ⟨c, hc, _⟩ :=
          existsUnique_conjugacyClass g
        exact
          ⟨c,
            (ConjClasses.mk_eq_mk_iff_isConj.mpr hc).symm⟩

/-- `QuaternionGroup 4` has exactly seven conjugacy classes. -/
@[simp]
theorem natCard_conjClasses :
    Nat.card (ConjClasses (QuaternionGroup 4)) = 7 := by
  calc
    Nat.card (ConjClasses (QuaternionGroup 4)) =
        Nat.card ConjugacyClass :=
      Nat.card_congr conjugacyClassEquiv.symm
    _ = 7 := by
      rw [Nat.card_eq_fintype_card]
      decide

end

end QuaternionGroupFour
end McKayConjecture
