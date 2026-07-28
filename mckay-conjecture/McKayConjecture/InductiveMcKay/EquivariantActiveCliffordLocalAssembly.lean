/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordActivePartitionEquivariance
import McKayConjecture.InductiveMcKay.ActiveCliffordLocalAssembly
import McKayConjecture.InductiveMcKay.EquivariantLocal

/-!
# Equivariant local assembly from active Clifford blocks

This file strengthens `ActiveCliffordLocalAssemblyData` by recording:

* invariance of its intermediate subgroup under `Aut(G)_P`; and
* equivariance of its active orbitwise equivalence in exact active
  Clifford sigma coordinates.

The sigma-coordinate certificate is converted by
`ActivePPrimeOrbitwiseCorrespondence.sigmaEquivariant_iff` into ordinary
equivariance of the assembled character bijection.  The result is a
genuine `EquivariantLocalCorrespondence P`.

No character-triple compatibility is asserted at this layer.

As in the active partition layer, the construction remains at the
Type-0 boundary.  Finite enumerations are installed locally wherever the
active Clifford sigma equivalences are evaluated.
-/

noncomputable section

namespace McKayConjecture.InductiveMcKay

open McKayConjecture.CliffordPartition

variable {G : Type} [Group G] [Finite G] {p : ℕ}

/-- Active Clifford local assembly data together with the exact
automorphism-invariance and sigma-equivariance needed for an equivariant
local correspondence. -/
structure EquivariantActiveCliffordLocalAssemblyData
    (P : Sylow p G)
    extends ActiveCliffordLocalAssemblyData P where
  /-- The chosen intermediate subgroup is invariant under
  `Aut(G)_P`. -/
  intermediate_invariant :
    AutomorphismInvariant (SylowAutStabilizer P)
      toActiveCliffordLocalAssemblyData.intermediate
  /-- The active orbitwise correspondence is equivariant in exact active
  Clifford sigma coordinates. -/
  sigma_equivariant :
    let d := toActiveCliffordLocalAssemblyData
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype d.intermediate :=
      Fintype.ofFinite d.intermediate
    letI : d.ambientNormal.Normal :=
      d.ambientNormal_normal
    letI : d.intermediateNormal.Normal :=
      d.intermediateNormal_normal
    letI :
        MulAction (SylowAutStabilizer P)
          (PPrimeIrreducibleCharacter d.intermediate p) :=
      SylowAutStabilizer.intermediatePPrimeCharacterMulAction
        P d.intermediate intermediate_invariant p
    d.orbitwise.SigmaEquivariant
      (A := SylowAutStabilizer P)

namespace EquivariantActiveCliffordLocalAssemblyData

variable {P : Sylow p G}

/-- The underlying active local assembly package. -/
abbrev activeLocalData
    (d : EquivariantActiveCliffordLocalAssemblyData P) :
    ActiveCliffordLocalAssemblyData P :=
  d.toActiveCliffordLocalAssemblyData

/-- Install the action of `Aut(G)_P` on prime-to-`p` characters of the
chosen invariant intermediate subgroup. -/
@[instance_reducible]
def intermediateCharacterMulAction
    (d : EquivariantActiveCliffordLocalAssemblyData P) :
    MulAction (SylowAutStabilizer P)
      (PPrimeIrreducibleCharacter d.intermediate p) :=
  SylowAutStabilizer.intermediatePPrimeCharacterMulAction
    P d.intermediate d.intermediate_invariant p

/-- The stored sigma-coordinate certificate is ordinary equivariance of
the assembled character correspondence. -/
theorem assembledCorrespondence_map_smul
    (d : EquivariantActiveCliffordLocalAssemblyData P) :
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype d.intermediate :=
      Fintype.ofFinite d.intermediate
    letI : d.ambientNormal.Normal :=
      d.ambientNormal_normal
    letI : d.intermediateNormal.Normal :=
      d.intermediateNormal_normal
    letI := d.intermediateCharacterMulAction
    ∀ (a : SylowAutStabilizer P)
      (χ : PPrimeIrreducibleCharacter G p),
      d.assembledCorrespondence (a • χ) =
        a • d.assembledCorrespondence χ := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype d.intermediate :=
    Fintype.ofFinite d.intermediate
  letI : d.ambientNormal.Normal :=
    d.ambientNormal_normal
  letI : d.intermediateNormal.Normal :=
    d.intermediateNormal_normal
  letI := d.intermediateCharacterMulAction
  exact
    d.orbitwise.sigmaEquivariant_iff.mp
      d.sigma_equivariant

/-- Assemble the active Clifford package into a genuine equivariant local
correspondence. -/
def toEquivariantLocalCorrespondence
    (d : EquivariantActiveCliffordLocalAssemblyData P) :
    EquivariantLocalCorrespondence P where
  toLocalCorrespondence :=
    d.toActiveCliffordLocalAssemblyData.toLocalCorrespondence
  intermediate_invariant :=
    d.intermediate_invariant
  map_smul' := by
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype d.intermediate :=
      Fintype.ofFinite d.intermediate
    letI : d.ambientNormal.Normal :=
      d.ambientNormal_normal
    letI : d.intermediateNormal.Normal :=
      d.intermediateNormal_normal
    exact d.assembledCorrespondence_map_smul

@[simp]
theorem toEquivariantLocalCorrespondence_toLocalCorrespondence
    (d : EquivariantActiveCliffordLocalAssemblyData P) :
    d.toEquivariantLocalCorrespondence.toLocalCorrespondence =
      d.toActiveCliffordLocalAssemblyData.toLocalCorrespondence :=
  rfl

@[simp]
theorem toEquivariantLocalCorrespondence_intermediate
    (d : EquivariantActiveCliffordLocalAssemblyData P) :
    d.toEquivariantLocalCorrespondence.intermediate =
      d.intermediate :=
  rfl

@[simp]
theorem toEquivariantLocalCorrespondence_correspondence_apply
    (d : EquivariantActiveCliffordLocalAssemblyData P)
    (χ : PPrimeIrreducibleCharacter G p) :
    d.toEquivariantLocalCorrespondence.correspondence χ =
      d.assembledCorrespondence χ :=
  rfl

/-- The invariant-subgroup witness of the assembled equivariant local
correspondence is exactly the stored witness. -/
theorem toEquivariantLocalCorrespondence_intermediate_invariant
    (d : EquivariantActiveCliffordLocalAssemblyData P) :
    d.toEquivariantLocalCorrespondence.intermediate_invariant =
      d.intermediate_invariant :=
  rfl

/-- The intermediate character action installed by the assembled
equivariant local correspondence is the action used by the active
sigma-equivariance certificate. -/
theorem toEquivariantLocalCorrespondence_intermediateCharacterMulAction
    (d : EquivariantActiveCliffordLocalAssemblyData P) :
    EquivariantLocalCorrespondence.intermediateCharacterMulAction
        d.toEquivariantLocalCorrespondence =
      d.intermediateCharacterMulAction :=
  rfl

/-- Pointwise action law for the assembled equivariant local
correspondence, using its canonical installed intermediate action. -/
@[simp]
theorem toEquivariantLocalCorrespondence_map_smul
    (d : EquivariantActiveCliffordLocalAssemblyData P) :
    letI :=
      d.toEquivariantLocalCorrespondence
        |>.intermediateCharacterMulAction
    ∀ (a : SylowAutStabilizer P)
      (χ : PPrimeIrreducibleCharacter G p),
      d.toEquivariantLocalCorrespondence.correspondence
          (a • χ) =
        a •
          d.toEquivariantLocalCorrespondence.correspondence
            χ :=
  d.toEquivariantLocalCorrespondence.map_smul

/-! ## Families -/

/-- An equivariant active Clifford assembly package for every finite
group and Sylow subgroup supplies the equivariant numerical inductive
McKay condition. -/
theorem equivariantNumericalInductiveMcKayOfActiveCliffordFamily
    (family :
      ∀ (Y : Type) [Group Y] [Finite Y]
        (Q : Sylow p Y),
        EquivariantActiveCliffordLocalAssemblyData Q) :
    EquivariantNumericalInductiveMcKay.{0} p := by
  intro Y _ _ Q
  exact
    ⟨(family Y Q).toEquivariantLocalCorrespondence⟩

end EquivariantActiveCliffordLocalAssemblyData

end McKayConjecture.InductiveMcKay
