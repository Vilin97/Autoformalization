/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.TransferInstance
import McKayConjecture.Proof.Isomorphism

/-!
# Reduction to universe-zero finite group models

Every finite group, in any universe, is isomorphic to a finite group whose
carrier lies in `Type`.  Since the McKay correspondence is invariant under
group isomorphism, it is enough to construct correspondences for
universe-zero carriers.  This removes the universe boundary inherited from
the present `FDRep` exhaustivity theorems without weakening the public
statement.
-/

noncomputable section

universe u

namespace McKayConjecture

variable {p : ℕ}

namespace McKayCorrespondence

/-- Explicit McKay correspondences for all finite groups in `Type` imply
the existence of correspondences for finite groups in every universe. -/
theorem nonempty_of_universeZero
    (h :
      ∀ (H : Type) [Group H] [Finite H]
        (Q : Sylow p H),
        McKayCorrespondence H p Q)
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Nonempty (McKayCorrespondence G p P) := by
  obtain ⟨H, groupH, fintypeH, ⟨e⟩⟩ :=
    Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} G
  letI : Group H := groupH
  letI : Fintype H := fintypeH
  let P' : Sylow p H :=
    Sylow.transport e P
  let f' : McKayCorrespondence H p P' :=
    h H P'
  have transported :
      McKayCorrespondence G p
        (Sylow.transport e.symm P') :=
    McKayCorrespondence.transport e.symm P' f'
  exact ⟨by simpa [P'] using transported⟩

/-- Chosen cross-universe McKay correspondence obtained from
universe-zero correspondences. -/
def of_universeZero
    (h :
      ∀ (H : Type) [Group H] [Finite H]
        (Q : Sylow p H),
        McKayCorrespondence H p Q)
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    McKayCorrespondence G p P :=
  Classical.choice
    (nonempty_of_universeZero h G P)

end McKayCorrespondence

namespace Statement

/-- It suffices to prove the McKay statement for finite group carriers in
`Type`; isomorphism transport then proves the statement in every universe. -/
theorem of_universeZero
    [Fact p.Prime]
    (h :
      ∀ (H : Type) [Group H] [Finite H]
        (Q : Sylow p H),
        Statement H p Q)
    (G : Type u) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P := by
  obtain ⟨H, groupH, fintypeH, ⟨e⟩⟩ :=
    Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} G
  letI : Group H := groupH
  letI : Fintype H := fintypeH
  let P' : Sylow p H :=
    Sylow.transport e P
  have hH : Statement H p P' :=
    h H P'
  simpa [P'] using
    Statement.transport e.symm P' hH

end Statement

end McKayConjecture
