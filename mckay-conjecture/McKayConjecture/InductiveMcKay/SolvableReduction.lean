/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SolvableLayer
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanExistence
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45CentralTriples
import McKayConjecture.InductiveMcKay.SolvableNormalSubgroupProposition42

/-!
# The no-layer reduction for finite solvable groups

Finite solvable groups have trivial layer, while the structural output of a
Rossi minimal counterexample has noncentral layer.  Consequently no
solvable group can satisfy `MinimalCounterexampleStructure`.

This eliminates both the tensor-permutation layer construction and the
quasisimple input from the solvable-group central-index induction.  The
proved solvable version of Proposition 4.2 and the proved classical
Glauberman correspondence leave exactly one residual input: the ambient
Proposition-4.5 coherence lifting the correspondence from `CS` to `G`.
That input is stated below only for solvable ambient groups.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open NormalSubgroupCentralIntersectionReduction
open NormalSubgroupProposition42CentralScalar
open scoped IsMulCommutative

namespace MinimalCounterexampleStructure

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {P : Sylow p G}

/-- A finite solvable group cannot have the structural output of a Rossi
minimal counterexample. -/
theorem not_of_isSolvable
    [Group.IsSolvable G] :
    ¬MinimalCounterexampleStructure P := by
  intro h
  apply h.not_layer_le_center
  rw [layer_eq_bot_of_isSolvable]
  exact bot_le

end MinimalCounterexampleStructure

namespace CentralScalarNormalSubgroupLocalReductionPrinciples

variable {G : Type} [Group G] [Finite G] [Group.IsSolvable G]
variable {p : ℕ} [Fact p.Prime]
variable {P : Sylow p G}

/-- Once the two normal-subgroup principles have been constructed, the
triviality of the layer rules out failure of the local correspondence.
No layer correspondence or quasisimple hypothesis is used. -/
theorem localCorrespondence_of_isSolvable
    (r : CentralScalarNormalSubgroupLocalReductionPrinciples P) :
    Nonempty (CentralScalarLocalCorrespondence P) := by
  by_cases hcommutative : IsMulCommutative G
  · exact
      ⟨(LocalInductiveMcKayData.of_isMulCommutative
        hcommutative P).toCentralScalarLocal⟩
  · by_contra hnoLocal
    exact
      MinimalCounterexampleStructure.not_of_isSolvable
        (r.minimalCounterexampleStructure
          hcommutative hnoLocal)

end CentralScalarNormalSubgroupLocalReductionPrinciples

namespace NormalSubgroupCentralIntersectionReduction

open ComplementReduction
open Proposition45

/-- The exact residual Proposition-4.5 assertion needed only for solvable
ambient groups.  The classical Glauberman correspondence itself is no
longer part of this hypothesis. -/
def SolvableCentralScalarCentralIntersectionAmbientLiftHypothesis
    (q : ℕ) [Fact q.Prime] : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [Group.IsSolvable X]
    (S : Sylow q X) (C : Subgroup X)
    (hCnormal : C.Normal)
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤),
      letI : C.Normal := hCnormal
      ∀ g :
          ProductGlaubermanCorrespondence S C hcentral,
        Nonempty
          (ProductAmbientGlaubermanLiftData
            S C hcentral hgenerate g)

/-- The unrestricted ambient Proposition-4.5 input specializes to solvable
ambient groups. -/
theorem solvableAmbientLiftHypothesis_of_ambientLift
    {q : ℕ} [Fact q.Prime]
    (h : CentralScalarCentralIntersectionAmbientLiftHypothesis q) :
    SolvableCentralScalarCentralIntersectionAmbientLiftHypothesis q := by
  intro X _ _ _ S C hCnormal hcentral hgenerate
  exact h X S C hCnormal hcentral hgenerate

/-- The standard central-triple form of the exact residual Proposition-4.5
assertion, restricted to solvable ambient groups. -/
def SolvableCentralScalarCentralIntersectionCentralTripleHypothesis
    (q : ℕ) [Fact q.Prime] : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [Group.IsSolvable X]
    (S : Sylow q X) (C : Subgroup X)
    (hCnormal : C.Normal)
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤),
      letI : C.Normal := hCnormal
      ∀ g :
          ProductGlaubermanCorrespondence S C hcentral,
        Nonempty
          (ProductAmbientGlaubermanCentralTripleLiftData
            S C hcentral hgenerate g)

/-- The standard central-triple statement supplies the numerical ambient
lift used by the solvable reduction. -/
theorem solvableAmbientLiftHypothesis_of_centralTriples
    {q : ℕ} [Fact q.Prime]
    (h :
      SolvableCentralScalarCentralIntersectionCentralTripleHypothesis q) :
    SolvableCentralScalarCentralIntersectionAmbientLiftHypothesis q := by
  intro X _ _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g
  obtain ⟨d⟩ :=
    h X S C hCnormal hcentral hgenerate g
  exact
    ⟨d.toProductAmbientGlaubermanLiftData
      S C hcentral hgenerate g⟩

/-- The proved classical Glauberman correspondence plus the residual
solvable ambient Proposition-4.5 lift gives the central-intersection local
correspondence. -/
theorem centralScalarLocalCorrespondence_of_solvableAmbientLift
    {X : Type} [Group X] [Finite X] [Group.IsSolvable X]
    {q : ℕ} [Fact q.Prime]
    (ambient :
      SolvableCentralScalarCentralIntersectionAmbientLiftHypothesis q)
    (S : Sylow q X) (C : Subgroup X)
    (hCnormal : C.Normal)
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤) :
    Nonempty (CentralScalarLocalCorrespondence S) := by
  letI : C.Normal := hCnormal
  obtain ⟨g⟩ :=
    ComplementReduction.exists_productGlaubermanCorrespondence
      S C hcentral
  obtain ⟨d⟩ :=
    ambient X S C hCnormal hcentral hgenerate g
  exact
    ⟨d.toCentralScalarLocalCorrespondence
      S C hcentral hgenerate g⟩

end NormalSubgroupCentralIntersectionReduction

/-- The central-scalar numerical local condition restricted to finite
solvable groups. -/
def SolvableCentralScalarNumericalInductiveMcKay
    (p : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G]
    (P : Sylow p G),
    Nonempty (CentralScalarLocalCorrespondence P)

/-- One central-index induction step restricted to finite solvable groups. -/
def SolvableCentralScalarCentralIndexInductionStep
    (p : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G]
    (P : Sylow p G),
    (∀ (H : Type u) [Group H] [Finite H] [Group.IsSolvable H],
      centralIndex H < centralIndex G →
        ∀ Q : Sylow p H,
          Nonempty (CentralScalarLocalCorrespondence Q)) →
      Nonempty (CentralScalarLocalCorrespondence P)

/-- A solvable central-index step proves the scalar local condition for
every finite solvable group. -/
theorem solvableCentralScalarNumericalInductiveMcKay_of_centralIndexStep
    {p : ℕ}
    (step :
      SolvableCentralScalarCentralIndexInductionStep.{u} p) :
    SolvableCentralScalarNumericalInductiveMcKay.{u} p := by
  intro G _ _ _ P
  have all :
      ∀ n : ℕ,
        (∀ m < n,
          ∀ (H : Type u) [Group H] [Finite H] [Group.IsSolvable H],
            centralIndex H = m →
              ∀ Q : Sylow p H,
                Nonempty
                  (CentralScalarLocalCorrespondence Q)) →
          ∀ (H : Type u) [Group H] [Finite H] [Group.IsSolvable H],
            centralIndex H = n →
              ∀ Q : Sylow p H,
                Nonempty
                  (CentralScalarLocalCorrespondence Q) := by
    intro n ih H _ _ _ hmeasure Q
    apply step H Q
    intro K _ _ _ hsmall R
    exact
      ih (centralIndex K)
        (by simpa only [hmeasure] using hsmall)
        K rfl R
  exact
    Nat.strong_induction_on
      (centralIndex G)
      (p := fun n =>
        ∀ (H : Type u) [Group H] [Finite H] [Group.IsSolvable H],
          centralIndex H = n →
            ∀ Q : Sylow p H,
              Nonempty
                (CentralScalarLocalCorrespondence Q))
      all G rfl P

/-- Solvable Proposition 4.2, the proved Glauberman theorem, and the exact
ambient Proposition-4.5 lift form a solvable central-index step. -/
theorem solvableCentralScalarCentralIndexStep_of_ambientLift
    {q : ℕ} [Fact q.Prime]
    (ambient :
      SolvableCentralScalarCentralIntersectionAmbientLiftHypothesis q) :
    SolvableCentralScalarCentralIndexInductionStep.{0} q := by
  intro G _ _ _ P ih
  by_cases hcommutative : IsMulCommutative G
  · exact
      ⟨(LocalInductiveMcKayData.of_isMulCommutative
        hcommutative P).toCentralScalarLocal⟩
  · let second :
        ∀ K : Subgroup G,
          K.Normal →
          K ⊓ (P : Subgroup G) ≤ Subgroup.center G →
          ¬K ≤ Subgroup.center G →
          K ⊔ Subgroup.normalizer (P : Set G) = ⊤ →
          Nonempty (CentralScalarLocalCorrespondence P) :=
      fun K hKnormal hcentral _hKnoncentral hgenerate ↦
        centralScalarLocalCorrespondence_of_solvableAmbientLift
          ambient P K hKnormal hcentral hgenerate
    let r :=
      localReductionPrinciplesOfSolvableCentralScalarLocalIH
        P ih second
    exact r.localCorrespondence_of_isSolvable

/-- The solvable scalar local condition, conditional only on the explicitly
isolated ambient Proposition-4.5 lift. -/
theorem solvableCentralScalarNumericalInductiveMcKay_of_ambientLift
    {q : ℕ} [Fact q.Prime]
    (ambient :
      SolvableCentralScalarCentralIntersectionAmbientLiftHypothesis q) :
    SolvableCentralScalarNumericalInductiveMcKay.{0} q :=
  solvableCentralScalarNumericalInductiveMcKay_of_centralIndexStep
    (solvableCentralScalarCentralIndexStep_of_ambientLift ambient)

/-! ### Solvable normalizer induction -/

/-- Local correspondences on all finite solvable groups recursively produce
a McKay correspondence for a finite solvable ambient group. -/
def correspondenceOfSolvableLocal
    (localData :
      ∀ (Y : Type u) [Group Y] [Finite Y] [Group.IsSolvable Y]
        (Q : Sylow p Y),
        LocalCorrespondence Q)
    (G : Type u) [Group G] [Finite G] [Group.IsSolvable G]
    (P : Sylow p G) :
    McKayCorrespondence G p P := by
  have all :
      ∀ n : ℕ,
        (∀ m < n,
          ∀ (Y : Type u) [Group Y] [Finite Y] [Group.IsSolvable Y],
            Nat.card Y = m →
              ∀ Q : Sylow p Y,
                Nonempty (McKayCorrespondence Y p Q)) →
        ∀ (Y : Type u) [Group Y] [Finite Y] [Group.IsSolvable Y],
          Nat.card Y = n →
            ∀ Q : Sylow p Y,
              Nonempty (McKayCorrespondence Y p Q) := by
    intro n ih Y _ _ _ hcard Q
    let datum := localData Y Q
    by_cases hnormalizer :
        Subgroup.normalizer (Q : Set Y) = ⊤
    · let e : SylowNormalizer Q ≃* Y :=
        (MulEquiv.subgroupCongr hnormalizer).trans
          Subgroup.topEquiv
      exact
        ⟨IrreducibleCharacter.pPrimeComapEquiv p e⟩
    · have hproper : datum.intermediate < ⊤ :=
        datum.proper_of_normalizer_ne_top hnormalizer
      have hsmall :
          Nat.card datum.intermediate < n := by
        rw [← hcard]
        exact natCard_lt_of_lt_top hproper
      let hQle :
          (Q : Subgroup Y) ≤ datum.intermediate :=
        Subgroup.le_normalizer.trans
          datum.normalizer_le
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
          intermediateToLocalNormalizer :=
            inductionCorrespondence }
      exact ⟨step.equiv⟩
  exact
    Classical.choice
      (Nat.strong_induction_on
        (Nat.card G)
        (p := fun n =>
          ∀ (Y : Type u) [Group Y] [Finite Y] [Group.IsSolvable Y],
            Nat.card Y = n →
              ∀ Q : Sylow p Y,
                Nonempty (McKayCorrespondence Y p Q))
        all G rfl P)

namespace SolvableCentralScalarNumericalInductiveMcKay

/-- Choose the underlying local correspondence supplied on a solvable
group. -/
def localData
    (h : SolvableCentralScalarNumericalInductiveMcKay.{u} p)
    (Y : Type u) [Group Y] [Finite Y] [Group.IsSolvable Y]
    (Q : Sylow p Y) :
    LocalCorrespondence Q :=
  (Classical.choice (h Y Q)).toLocal

/-- A solvable scalar local condition gives the McKay correspondence. -/
def correspondence
    (h : SolvableCentralScalarNumericalInductiveMcKay.{u} p)
    (G : Type u) [Group G] [Finite G] [Group.IsSolvable G]
    (P : Sylow p G) :
    McKayCorrespondence G p P :=
  correspondenceOfSolvableLocal h.localData G P

/-- Cardinal form of the solvable normalizer induction. -/
theorem statement
    [Fact p.Prime]
    (h : SolvableCentralScalarNumericalInductiveMcKay.{u} p)
    (G : Type u) [Group G] [Finite G] [Group.IsSolvable G]
    (P : Sylow p G) :
    Statement G p P :=
  Statement.of_correspondence (h.correspondence G P)

end SolvableCentralScalarNumericalInductiveMcKay

/-- McKay's cardinal equality for finite solvable groups, with the exact
remaining solvable ambient Proposition-4.5 lift exposed as the sole input. -/
theorem statement_of_solvableAmbientLift
    {q : ℕ} [Fact q.Prime]
    (ambient :
      SolvableCentralScalarCentralIntersectionAmbientLiftHypothesis q)
    (G : Type) [Group G] [Finite G] [Group.IsSolvable G]
    (P : Sylow q G) :
    Statement G q P :=
  (solvableCentralScalarNumericalInductiveMcKay_of_ambientLift
    ambient).statement G P

/-- McKay's cardinal equality for finite solvable groups from the standard
central-triple formulation of the sole remaining Proposition-4.5 input. -/
theorem statement_of_solvableCentralTriples
    {q : ℕ} [Fact q.Prime]
    (centralTriples :
      SolvableCentralScalarCentralIntersectionCentralTripleHypothesis q)
    (G : Type) [Group G] [Finite G] [Group.IsSolvable G]
    (P : Sylow q G) :
    Statement G q P :=
  statement_of_solvableAmbientLift
    (solvableAmbientLiftHypothesis_of_centralTriples
      centralTriples)
    G P

/-- The unrestricted ambient Proposition-4.5 input proves McKay for all
finite solvable groups without any layer or quasisimple hypothesis. -/
theorem statement_of_ambientLift_of_isSolvable
    {q : ℕ} [Fact q.Prime]
    (ambient :
      CentralScalarCentralIntersectionAmbientLiftHypothesis q)
    (G : Type) [Group G] [Finite G] [Group.IsSolvable G]
    (P : Sylow q G) :
    Statement G q P :=
  statement_of_solvableAmbientLift
    (solvableAmbientLiftHypothesis_of_ambientLift ambient)
    G P

end InductiveMcKay
end McKayConjecture
