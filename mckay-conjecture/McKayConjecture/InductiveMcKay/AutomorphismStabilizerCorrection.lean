/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AutomorphismStabilizer

/-!
# Correcting an automorphism to stabilize a fixed Sylow subgroup

An automorphism sends a fixed Sylow subgroup to another Sylow subgroup.
Sylow conjugacy therefore supplies an inner correction carrying the image
back to the original subgroup.  This file packages that construction as a
reusable element of `SylowAutStabilizer`.

The construction is deliberately noncanonical: the correcting conjugator is
chosen from Sylow conjugacy.  Its defining action equation and the literal
underlying automorphism of the resulting stabilizer element are exposed for
downstream calculations.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

namespace SylowAutStabilizer

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A chosen element carrying the automorphic image of `P` back to `P`. -/
def correctionConjugator
    (P : Sylow p G)
    (a : MulAut G) :
    G :=
  Classical.choose
    (MulAction.exists_smul_eq G (a • P) P)

/-- The chosen correction carries the image of `P` under `a` back to `P`. -/
theorem correctionConjugator_smul
    (P : Sylow p G)
    (a : MulAut G) :
    correctionConjugator P a • (a • P) = P :=
  Classical.choose_spec
    (MulAction.exists_smul_eq G (a • P) P)

/-- Correct an arbitrary automorphism by conjugation so that it stabilizes
the fixed Sylow subgroup `P`. -/
def correctedAutomorphism
    (P : Sylow p G)
    (a : MulAut G) :
    MulAut G :=
  MulAut.conj (correctionConjugator P a) * a

/-- The inner-corrected automorphism stabilizes `P`. -/
theorem correctedAutomorphism_smul
    (P : Sylow p G)
    (a : MulAut G) :
    correctedAutomorphism P a • P = P := by
  rw [correctedAutomorphism, mul_smul]
  exact correctionConjugator_smul P a

/-- Package the inner-corrected automorphism as an element of
`SylowAutStabilizer P`. -/
def corrected
    (P : Sylow p G)
    (a : MulAut G) :
    SylowAutStabilizer P :=
  ⟨correctedAutomorphism P a, correctedAutomorphism_smul P a⟩

/-- The underlying automorphism of the corrected stabilizer element is
literally conjugation by the chosen correction followed by `a`. -/
@[simp]
theorem corrected_coe
    (P : Sylow p G)
    (a : MulAut G) :
    (corrected P a : MulAut G) =
      MulAut.conj (correctionConjugator P a) * a :=
  rfl

end SylowAutStabilizer

end InductiveMcKay
end McKayConjecture
