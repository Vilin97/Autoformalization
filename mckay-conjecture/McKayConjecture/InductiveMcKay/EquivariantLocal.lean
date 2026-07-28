/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AutomorphismStabilizer
import McKayConjecture.InductiveMcKay.NumericalReduction

/-!
# The equivariant local part of inductive McKay

This file strengthens `LocalCorrespondence` with the automorphism stability
and equivariance required in part (a) and the first clause of part (b) of the
inductive McKay condition.  Character-triple compatibility is intentionally
kept in the separate character-triple layer.
-/

noncomputable section

universe u

namespace McKayConjecture.InductiveMcKay

variable {G : Type u} [Group G] {p : ℕ}

/-- A local `p'`-character correspondence invariant and equivariant under
`Aut(G)_P`.

This is the equivariant numerical portion of the inductive McKay condition;
the full condition additionally requires a central-isomorphism witness for
each corresponding pair of characters.
-/
structure EquivariantLocalCorrespondence (P : Sylow p G)
    extends LocalCorrespondence P where
  /-- The intermediate subgroup is stable under `Aut(G)_P`. -/
  intermediate_invariant :
    AutomorphismInvariant (SylowAutStabilizer P)
      toLocalCorrespondence.intermediate
  /-- The character correspondence commutes with `Aut(G)_P`. -/
  map_smul' :
    letI :=
      SylowAutStabilizer.intermediatePPrimeCharacterMulAction
        P toLocalCorrespondence.intermediate intermediate_invariant p
    ∀ (a : SylowAutStabilizer P)
      (χ : PPrimeIrreducibleCharacter G p),
      toLocalCorrespondence.correspondence (a • χ) =
        a • toLocalCorrespondence.correspondence χ

namespace EquivariantLocalCorrespondence

variable {P : Sylow p G}

instance : Coe (EquivariantLocalCorrespondence P)
    (LocalCorrespondence P) :=
  ⟨EquivariantLocalCorrespondence.toLocalCorrespondence⟩

/-- Install the induced action on characters of the chosen intermediate
subgroup. -/
@[instance_reducible]
def intermediateCharacterMulAction
    (d : EquivariantLocalCorrespondence P) :
    MulAction (SylowAutStabilizer P)
      (PPrimeIrreducibleCharacter d.intermediate p) :=
  SylowAutStabilizer.intermediatePPrimeCharacterMulAction
    P d.intermediate d.intermediate_invariant p

/-- Pointwise equivariance, using the induced intermediate-subgroup action. -/
theorem map_smul (d : EquivariantLocalCorrespondence P) :
    letI := d.intermediateCharacterMulAction
    ∀ (a : SylowAutStabilizer P)
      (χ : PPrimeIrreducibleCharacter G p),
      d.correspondence (a • χ) = a • d.correspondence χ :=
  d.map_smul'

/-- Forget equivariance and retain the local correspondence used by
normalizer induction. -/
def forget (d : EquivariantLocalCorrespondence P) :
    LocalCorrespondence P :=
  d.toLocalCorrespondence

end EquivariantLocalCorrespondence

/-- Existence of an equivariant local correspondence for every finite group
in a universe. -/
def EquivariantNumericalInductiveMcKay (p : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (P : Sylow p G),
    Nonempty (EquivariantLocalCorrespondence P)

namespace EquivariantNumericalInductiveMcKay

/-- Forgetting equivariance yields the numerical inductive McKay condition. -/
theorem toNumerical
    (h : EquivariantNumericalInductiveMcKay.{u} p) :
    NumericalInductiveMcKay.{u} p := by
  intro G _ _ P
  obtain ⟨d⟩ := h G P
  exact ⟨d.forget⟩

/-- Hence equivariant local correspondences already imply explicit McKay
correspondences after forgetting their extra structure. -/
def correspondence
    (h : EquivariantNumericalInductiveMcKay.{u} p)
    (G : Type u) [Group G] [Finite G] (P : Sylow p G) :
    McKayCorrespondence G p P :=
  h.toNumerical.correspondence G P

/-- Cardinal-valued consequence of the equivariant numerical condition. -/
theorem statement [Fact p.Prime]
    (h : EquivariantNumericalInductiveMcKay.{u} p)
    (G : Type u) [Group G] [Finite G] (P : Sylow p G) :
    Statement G p P :=
  h.toNumerical.statement G P

end EquivariantNumericalInductiveMcKay

end McKayConjecture.InductiveMcKay
