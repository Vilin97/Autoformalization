/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.UniversalCentralExtension
import McKayConjecture.InductiveMcKay.Condition

/-!
# The quasisimple hypothesis in the McKay reduction

The Isaacs--Malle--Navarro/Rossi reduction assumes the inductive McKay
condition for universal covering groups of all nonabelian finite simple
groups.  This file states that hypothesis with genuine central-extension
data.  It deliberately does not postulate the reduction theorem.
-/

noncomputable section

universe u

namespace McKayConjecture.InductiveMcKay

open McKayConjecture.GroupTheory
open scoped IsMulCommutative

/-- Every universal covering group of a nonabelian finite simple group has
full local inductive-McKay data at `p`. -/
def UniversalCoverInductiveMcKayHypothesis (p : ℕ) : Prop :=
  ∀ (S : Type u) [Group S] [Finite S]
    (_hs : IsSimpleGroup S) (_hnoncomm : ¬IsMulCommutative S)
    (U : Type u) [Group U] [Finite U]
    (_E : UniversalCentralExtension U S)
    (P : Sylow p U),
    Nonempty (LocalInductiveMcKayData P)

/-- A stronger, often convenient formulation: every finite quasisimple
group has full local inductive-McKay data. -/
def QuasisimpleInductiveMcKayHypothesis (p : ℕ) : Prop :=
  ∀ (U : Type u) [Group U] [Finite U],
    IsQuasisimple U →
      ∀ P : Sylow p U,
        Nonempty (LocalInductiveMcKayData P)

/-- Verification for all finite quasisimple groups implies the exact
universal-cover hypothesis used by the reduction theorem. -/
theorem QuasisimpleInductiveMcKayHypothesis.toUniversalCover
    {p : ℕ}
    (h : QuasisimpleInductiveMcKayHypothesis.{u} p) :
    UniversalCoverInductiveMcKayHypothesis.{u} p := by
  intro S _ _ hs hnoncomm U _ _ E P
  exact h U (E.source_isQuasisimple hs hnoncomm) P

/-- The still-missing Rossi reduction has this precise proposition as its
kernel-checked target.  Naming the proposition makes the dependency visible
without introducing an axiom or a theorem-shaped placeholder. -/
def RossiReductionTarget (p : ℕ) : Prop :=
  UniversalCoverInductiveMcKayHypothesis.{u} p →
    ∀ (G : Type u) [Group G] [Finite G] (P : Sylow p G),
      Nonempty (McKayCorrespondence G p P)

/-- Once a proof of the Rossi target is supplied, its conclusion gives the
public McKay statement.  This theorem performs only the final, already
formalized cardinal step. -/
theorem statement_of_rossi_reduction
    {p : ℕ} [Fact p.Prime]
    (reduction : RossiReductionTarget.{u} p)
    (covers : UniversalCoverInductiveMcKayHypothesis.{u} p)
    (G : Type u) [Group G] [Finite G] (P : Sylow p G) :
    Statement G p P := by
  obtain ⟨e⟩ := reduction covers G P
  exact Statement.of_correspondence e

end McKayConjecture.InductiveMcKay
