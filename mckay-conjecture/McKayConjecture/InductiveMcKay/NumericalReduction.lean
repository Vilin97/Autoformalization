/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalizerInduction
import McKayConjecture.Proof.Correspondence

/-!
# From local correspondences to the Sylow normalizer

This file formalizes the final, elementary induction in the McKay proof.  Its
input is the numerical core of the inductive McKay condition: for every finite
group and Sylow subgroup, a character correspondence to a suitable
intermediate subgroup.  The output is a correspondence all the way to the
Sylow normalizer.

The classification-dependent reduction theorem is not used here.  It must
eventually construct the `LocalCorrespondence` input, together with the
stronger equivariance and character-triple compatibility recorded in later
layers.
-/

noncomputable section

universe u

namespace McKayConjecture.InductiveMcKay

variable {X : Type u} [Group X] {p : ℕ}

/-- The numerical core of the inductive McKay condition at a fixed Sylow
subgroup.

The intermediate subgroup must contain the Sylow normalizer and must be
proper unless that normalizer is already the whole group.
-/
structure LocalCorrespondence (Q : Sylow p X) where
  /-- The local subgroup supplied by the inductive condition. -/
  intermediate : Subgroup X
  /-- The Sylow normalizer lies in the local subgroup. -/
  normalizer_le :
    Subgroup.normalizer (Q : Set X) ≤ intermediate
  /-- The local subgroup is proper in the nontrivial induction case. -/
  proper_of_normalizer_ne_top :
    Subgroup.normalizer (Q : Set X) ≠ ⊤ → intermediate < ⊤
  /-- The local bijection on irreducible characters of `p'`-degree. -/
  correspondence :
    PPrimeIrreducibleCharacter X p ≃
      PPrimeIrreducibleCharacter intermediate p

namespace LocalCorrespondence

/-- The identity local correspondence in the base case where the Sylow
normalizer is the whole group. -/
def of_normalizer_eq_top (Q : Sylow p X)
    (hQ : Subgroup.normalizer (Q : Set X) = ⊤) :
    LocalCorrespondence Q where
  intermediate := ⊤
  normalizer_le := hQ.le
  proper_of_normalizer_ne_top h := (h hQ).elim
  correspondence :=
    PPrimeCorrespondence.ofMulEquiv p Subgroup.topEquiv

/-- A normal Sylow subgroup has the identity local correspondence through
the full ambient group. -/
def of_normal_sylow (Q : Sylow p X)
    [hQ : (Q : Subgroup X).Normal] :
    LocalCorrespondence Q :=
  of_normalizer_eq_top Q
    (Subgroup.normalizer_eq_top (H := (Q : Subgroup X)))

end LocalCorrespondence

/-- The numerical part of the inductive McKay condition for every finite
group in a universe.  The actual inductive McKay condition strengthens each
local correspondence with automorphism equivariance and central character
triple compatibility. -/
def NumericalInductiveMcKay (p : ℕ) : Prop :=
  ∀ (Y : Type u) [Group Y] [Finite Y] (Q : Sylow p Y),
    Nonempty (LocalCorrespondence Q)

/-- A local correspondence for every finite group implies an explicit McKay
correspondence for every finite group.

This is the fully formal normalizer induction underlying the implication
"inductive McKay implies McKay".  The induction measure is group cardinality,
and the only recursive call is made on a certified proper subgroup.
-/
def correspondenceOfLocal
    (localData :
      ∀ (Y : Type u) [Group Y] [Finite Y] (Q : Sylow p Y),
        LocalCorrespondence Q)
    (G : Type u) [Group G] [Finite G] (P : Sylow p G) :
    McKayCorrespondence G p P := by
  have all :
      ∀ n : ℕ,
        (∀ m < n, ∀ (Y : Type u) [Group Y] [Finite Y],
          Nat.card Y = m → ∀ Q : Sylow p Y,
            Nonempty (McKayCorrespondence Y p Q)) →
        ∀ (Y : Type u) [Group Y] [Finite Y],
          Nat.card Y = n → ∀ Q : Sylow p Y,
            Nonempty (McKayCorrespondence Y p Q) := by
    intro n ih Y _ _ hcard Q
    let datum := localData Y Q
    by_cases hnormalizer :
        Subgroup.normalizer (Q : Set Y) = ⊤
    · let e : SylowNormalizer Q ≃* Y :=
        (MulEquiv.subgroupCongr hnormalizer).trans Subgroup.topEquiv
      exact ⟨IrreducibleCharacter.pPrimeComapEquiv p e⟩
    · have hproper : datum.intermediate < ⊤ :=
        datum.proper_of_normalizer_ne_top hnormalizer
      have hsmall : Nat.card datum.intermediate < n := by
        rw [← hcard]
        exact natCard_lt_of_lt_top hproper
      let hQle : (Q : Subgroup Y) ≤ datum.intermediate :=
        Subgroup.le_normalizer.trans datum.normalizer_le
      let Q' : Sylow p datum.intermediate :=
        sylowIn Q datum.intermediate hQle
      obtain ⟨inductionCorrespondence⟩ :=
        ih (Nat.card datum.intermediate) hsmall
          datum.intermediate rfl Q'
      let step : CharacterCorrespondenceStep Q :=
        { intermediate := datum.intermediate
          normalizer_le := datum.normalizer_le
          proper := hproper
          ambientToIntermediate := datum.correspondence
          intermediateToLocalNormalizer := inductionCorrespondence }
      exact ⟨step.equiv⟩
  exact Classical.choice
    (Nat.strong_induction_on (Nat.card G)
      (p := fun n =>
        ∀ (Y : Type u) [Group Y] [Finite Y],
          Nat.card Y = n → ∀ Q : Sylow p Y,
            Nonempty (McKayCorrespondence Y p Q))
      all G rfl P)

/-- The cardinal form of the preceding normalizer induction. -/
theorem statement_of_local [Fact p.Prime]
    (localData :
      ∀ (Y : Type u) [Group Y] [Finite Y] (Q : Sylow p Y),
        LocalCorrespondence Q)
    (G : Type u) [Group G] [Finite G] (P : Sylow p G) :
    Statement G p P :=
  Statement.of_correspondence (correspondenceOfLocal localData G P)

namespace NumericalInductiveMcKay

/-- Choose the numerical local datum supplied by the condition. -/
def localData (h : NumericalInductiveMcKay.{u} p)
    (Y : Type u) [Group Y] [Finite Y] (Q : Sylow p Y) :
    LocalCorrespondence Q :=
  Classical.choice (h Y Q)

/-- The numerical inductive McKay condition produces a bijection with every
Sylow normalizer. -/
def correspondence (h : NumericalInductiveMcKay.{u} p)
    (G : Type u) [Group G] [Finite G] (P : Sylow p G) :
    McKayCorrespondence G p P :=
  correspondenceOfLocal h.localData G P

/-- Therefore the numerical inductive McKay condition implies the cardinal
statement of the McKay conjecture. -/
theorem statement [Fact p.Prime]
    (h : NumericalInductiveMcKay.{u} p)
    (G : Type u) [Group G] [Finite G] (P : Sylow p G) :
    Statement G p P :=
  Statement.of_correspondence (h.correspondence G P)

end NumericalInductiveMcKay

end McKayConjecture.InductiveMcKay
