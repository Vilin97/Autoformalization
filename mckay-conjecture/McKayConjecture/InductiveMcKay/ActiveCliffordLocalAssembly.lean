/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordActivePartition
import McKayConjecture.InductiveMcKay.NumericalReduction

/-!
# Local correspondences assembled from active Clifford blocks

This file is the direct bridge from the exact active Clifford partition
to numerical normalizer induction.  An
`ActiveCliffordLocalAssemblyData P` stores:

* an intermediate subgroup containing `N_G(P)`, together with the
  properness condition needed for subgroup induction;
* an explicitly normal subgroup of the ambient group;
* an explicitly normal subgroup of the intermediate group; and
* an `ActivePPrimeOrbitwiseCorrespondence` between their exact active
  Clifford partitions.

The active orbitwise datum assembles into the `correspondence` field of a
`LocalCorrespondence P`.  Its active-orbit and underlying-orbit transport
laws are inherited directly from `CliffordActivePartition`.

The family theorem has the existing Type-0 boundary: all public groups
are in `Type`, while finite enumerations used by character partitions are
installed locally at the noncomputable assembly and orbit-transport
boundaries.
-/

noncomputable section

namespace McKayConjecture.InductiveMcKay

open McKayConjecture.CliffordPartition

variable {G : Type} [Group G] [Finite G] {p : ℕ}

/-- The data needed to build one numerical local correspondence from
active Clifford-orbit block correspondences. -/
structure ActiveCliffordLocalAssemblyData (P : Sylow p G) where
  /-- The intermediate subgroup used by normalizer induction. -/
  intermediate : Subgroup G
  /-- The ambient Sylow normalizer is contained in the intermediate
  subgroup. -/
  normalizer_le :
    Subgroup.normalizer (P : Set G) ≤ intermediate
  /-- The intermediate subgroup is proper whenever the normalizer is not
  already the whole ambient group. -/
  proper_of_normalizer_ne_top :
    Subgroup.normalizer (P : Set G) ≠ ⊤ → intermediate < ⊤
  /-- The normal subgroup defining the ambient active Clifford
  partition. -/
  ambientNormal : Subgroup G
  /-- The exact normality witness for the ambient partition subgroup. -/
  ambientNormal_normal : ambientNormal.Normal
  /-- The normal subgroup defining the active Clifford partition inside
  the intermediate group. -/
  intermediateNormal : Subgroup intermediate
  /-- The exact normality witness for the intermediate partition
  subgroup. -/
  intermediateNormal_normal : intermediateNormal.Normal
  /-- The explicit matching of active orbit indices and their nonempty
  prime-to-`p` Clifford blocks. -/
  orbitwise :
    letI : ambientNormal.Normal := ambientNormal_normal
    letI : intermediateNormal.Normal :=
      intermediateNormal_normal
    ActivePPrimeOrbitwiseCorrespondence
      ambientNormal intermediateNormal p

namespace ActiveCliffordLocalAssemblyData

variable {P : Sylow p G}

/-- Assemble the stored active orbitwise data into the
ambient-to-intermediate prime-to-`p` character correspondence.

The finite enumerations are implementation details and do not occur in
the result type. -/
def assembledCorrespondence
    (d : ActiveCliffordLocalAssemblyData P) :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter d.intermediate p := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype d.intermediate :=
    Fintype.ofFinite d.intermediate
  letI : d.ambientNormal.Normal :=
    d.ambientNormal_normal
  letI : d.intermediateNormal.Normal :=
    d.intermediateNormal_normal
  exact d.orbitwise.assemble

/-- Convert active Clifford local data into the exact local datum
consumed by normalizer induction. -/
def toLocalCorrespondence
    (d : ActiveCliffordLocalAssemblyData P) :
    LocalCorrespondence P where
  intermediate := d.intermediate
  normalizer_le := d.normalizer_le
  proper_of_normalizer_ne_top :=
    d.proper_of_normalizer_ne_top
  correspondence := d.assembledCorrespondence

@[simp]
theorem toLocalCorrespondence_intermediate
    (d : ActiveCliffordLocalAssemblyData P) :
    d.toLocalCorrespondence.intermediate =
      d.intermediate :=
  rfl

/-- The correspondence field is definitionally the equivalence assembled
from the active orbit blocks. -/
@[simp]
theorem toLocalCorrespondence_correspondence_apply
    (d : ActiveCliffordLocalAssemblyData P)
    (χ : PPrimeIrreducibleCharacter G p) :
    d.toLocalCorrespondence.correspondence χ =
      d.assembledCorrespondence χ :=
  rfl

/-- The assembled correspondence transports the exact active orbit by
the stored active-orbit equivalence. -/
@[simp]
theorem activeOrbitIndex_assembledCorrespondence
    (d : ActiveCliffordLocalAssemblyData P)
    (χ : PPrimeIrreducibleCharacter G p) :
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype d.intermediate :=
      Fintype.ofFinite d.intermediate
    letI : d.ambientNormal.Normal :=
      d.ambientNormal_normal
    letI : d.intermediateNormal.Normal :=
      d.intermediateNormal_normal
    activeOrbitIndex d.intermediateNormal
        (d.assembledCorrespondence χ) =
      d.orbitwise.activeOrbitEquiv
        (activeOrbitIndex d.ambientNormal χ) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype d.intermediate :=
    Fintype.ofFinite d.intermediate
  letI : d.ambientNormal.Normal :=
    d.ambientNormal_normal
  letI : d.intermediateNormal.Normal :=
    d.intermediateNormal_normal
  exact d.orbitwise.activeOrbitIndex_assemble χ

/-- Inverse application transports the exact active orbit by the inverse
stored active-orbit equivalence. -/
@[simp]
theorem activeOrbitIndex_assembledCorrespondence_symm
    (d : ActiveCliffordLocalAssemblyData P)
    (ψ : PPrimeIrreducibleCharacter d.intermediate p) :
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype d.intermediate :=
      Fintype.ofFinite d.intermediate
    letI : d.ambientNormal.Normal :=
      d.ambientNormal_normal
    letI : d.intermediateNormal.Normal :=
      d.intermediateNormal_normal
    activeOrbitIndex d.ambientNormal
        (d.assembledCorrespondence.symm ψ) =
      d.orbitwise.activeOrbitEquiv.symm
        (activeOrbitIndex d.intermediateNormal ψ) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype d.intermediate :=
    Fintype.ofFinite d.intermediate
  letI : d.ambientNormal.Normal :=
    d.ambientNormal_normal
  letI : d.intermediateNormal.Normal :=
    d.intermediateNormal_normal
  exact d.orbitwise.activeOrbitIndex_assemble_symm ψ

/-- Forgetting activity, the assembled correspondence transports the
underlying Clifford orbit by the stored active-orbit equivalence. -/
@[simp]
theorem orbitOf_assembledCorrespondence
    (d : ActiveCliffordLocalAssemblyData P)
    (χ : PPrimeIrreducibleCharacter G p) :
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype d.intermediate :=
      Fintype.ofFinite d.intermediate
    letI : d.ambientNormal.Normal :=
      d.ambientNormal_normal
    letI : d.intermediateNormal.Normal :=
      d.intermediateNormal_normal
    orbitOf d.intermediateNormal
        (d.assembledCorrespondence χ).1 =
      (d.orbitwise.activeOrbitEquiv
        (activeOrbitIndex d.ambientNormal χ)).1 := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype d.intermediate :=
    Fintype.ofFinite d.intermediate
  letI : d.ambientNormal.Normal :=
    d.ambientNormal_normal
  letI : d.intermediateNormal.Normal :=
    d.intermediateNormal_normal
  exact d.orbitwise.orbitOf_assemble χ

/-- Forgetting activity, inverse application transports the underlying
Clifford orbit by the inverse stored active-orbit equivalence. -/
@[simp]
theorem orbitOf_assembledCorrespondence_symm
    (d : ActiveCliffordLocalAssemblyData P)
    (ψ : PPrimeIrreducibleCharacter d.intermediate p) :
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype d.intermediate :=
      Fintype.ofFinite d.intermediate
    letI : d.ambientNormal.Normal :=
      d.ambientNormal_normal
    letI : d.intermediateNormal.Normal :=
      d.intermediateNormal_normal
    orbitOf d.ambientNormal
        (d.assembledCorrespondence.symm ψ).1 =
      (d.orbitwise.activeOrbitEquiv.symm
        (activeOrbitIndex d.intermediateNormal ψ)).1 := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype d.intermediate :=
    Fintype.ofFinite d.intermediate
  letI : d.ambientNormal.Normal :=
    d.ambientNormal_normal
  letI : d.intermediateNormal.Normal :=
    d.intermediateNormal_normal
  exact d.orbitwise.orbitOf_assemble_symm ψ

end ActiveCliffordLocalAssemblyData

/-! ## Families and normalizer induction -/

/-- An active Clifford local assembly package for every finite group and
Sylow subgroup supplies the numerical inductive McKay condition. -/
theorem numericalInductiveMcKayOfActiveCliffordFamily
    (family :
      ∀ (Y : Type) [Group Y] [Finite Y]
        (Q : Sylow p Y),
        ActiveCliffordLocalAssemblyData Q) :
    NumericalInductiveMcKay.{0} p := by
  intro Y _ _ Q
  exact ⟨(family Y Q).toLocalCorrespondence⟩

/-- The explicit correspondence with the Sylow normalizer obtained by
feeding an active Clifford local family into normalizer induction. -/
def normalizerCorrespondenceOfActiveCliffordFamily
    (family :
      ∀ (Y : Type) [Group Y] [Finite Y]
        (Q : Sylow p Y),
        ActiveCliffordLocalAssemblyData Q)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    McKayCorrespondence G p P :=
  (numericalInductiveMcKayOfActiveCliffordFamily
    family).correspondence G P

/-- A family of active Clifford local packages proves the cardinal McKay
statement through the existing normalizer induction. -/
theorem statementOfActiveCliffordFamily
    [Fact p.Prime]
    (family :
      ∀ (Y : Type) [Group Y] [Finite Y]
        (Q : Sylow p Y),
        ActiveCliffordLocalAssemblyData Q)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (numericalInductiveMcKayOfActiveCliffordFamily
    family).statement G P

end McKayConjecture.InductiveMcKay
