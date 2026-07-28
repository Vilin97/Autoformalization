/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordPartitionCorrespondence
import McKayConjecture.InductiveMcKay.NumericalReduction

/-!
# Local correspondences assembled from Clifford blocks

This file connects the orbitwise Clifford bookkeeping layer to numerical
normalizer induction.  A `CliffordLocalAssemblyData P` records:

* an intermediate subgroup containing `N_G(P)`, with the properness
  condition required by subgroup induction;
* a normal subgroup of the ambient group;
* a normal subgroup of the intermediate group; and
* an orbitwise equivalence between the corresponding prime-to-`p`
  Clifford blocks.

The orbitwise equivalence assembles into the `correspondence` field of a
`LocalCorrespondence P`.  All public hypotheses use `Finite`; the
`Fintype` instances needed by the character partition are installed only
inside the noncomputable assembly definitions.
-/

noncomputable section

namespace McKayConjecture.InductiveMcKay

open McKayConjecture.CliffordPartition

variable {G : Type} [Group G] [Finite G] {p : ℕ}

/-- The data needed to build one numerical local correspondence from
orbitwise Clifford-block correspondences. -/
structure CliffordLocalAssemblyData (P : Sylow p G) where
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
  /-- The normal subgroup defining the ambient Clifford partition. -/
  ambientNormal : Subgroup G
  /-- Normality of the ambient partition subgroup. -/
  ambientNormal_normal : ambientNormal.Normal
  /-- The normal subgroup defining the Clifford partition inside the
  intermediate group. -/
  intermediateNormal : Subgroup intermediate
  /-- Normality of the intermediate partition subgroup. -/
  intermediateNormal_normal : intermediateNormal.Normal
  /-- The explicit matching of orbit indices and every prime-to-`p`
  Clifford block. -/
  orbitwise :
    letI : ambientNormal.Normal := ambientNormal_normal
    letI : intermediateNormal.Normal := intermediateNormal_normal
    PPrimeOrbitwiseCorrespondence ambientNormal intermediateNormal p

namespace CliffordLocalAssemblyData

variable {P : Sylow p G}

/-- Assemble the stored orbitwise data into the ambient-to-intermediate
prime-to-`p` character correspondence.

The finite enumerations are implementation details and do not occur in the
result type. -/
def assembledCorrespondence
    (d : CliffordLocalAssemblyData P) :
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

/-- Convert orbitwise Clifford data into the exact local datum consumed by
normalizer induction. -/
def toLocalCorrespondence
    (d : CliffordLocalAssemblyData P) :
    LocalCorrespondence P where
  intermediate := d.intermediate
  normalizer_le := d.normalizer_le
  proper_of_normalizer_ne_top :=
    d.proper_of_normalizer_ne_top
  correspondence := d.assembledCorrespondence

@[simp]
theorem toLocalCorrespondence_intermediate
    (d : CliffordLocalAssemblyData P) :
    d.toLocalCorrespondence.intermediate = d.intermediate :=
  rfl

/-- The correspondence field is definitionally the assembled orbitwise
Clifford equivalence. -/
@[simp]
theorem toLocalCorrespondence_correspondence_apply
    (d : CliffordLocalAssemblyData P)
    (χ : PPrimeIrreducibleCharacter G p) :
    d.toLocalCorrespondence.correspondence χ =
      d.assembledCorrespondence χ :=
  rfl

/-- The local correspondence transports the ambient Clifford orbit by the
stored orbit-index equivalence. -/
@[simp]
theorem orbitOf_assembledCorrespondence
    (d : CliffordLocalAssemblyData P)
    (χ : PPrimeIrreducibleCharacter G p) :
    letI : d.ambientNormal.Normal :=
      d.ambientNormal_normal
    letI : d.intermediateNormal.Normal :=
      d.intermediateNormal_normal
    orbitOf d.intermediateNormal
        (d.assembledCorrespondence χ).1 =
      d.orbitwise.orbitEquiv
        (orbitOf d.ambientNormal χ.1) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype d.intermediate :=
    Fintype.ofFinite d.intermediate
  letI : d.ambientNormal.Normal :=
    d.ambientNormal_normal
  letI : d.intermediateNormal.Normal :=
    d.intermediateNormal_normal
  exact d.orbitwise.orbitOf_assemble χ

/-- Inverse application transports the intermediate Clifford orbit by the
inverse stored orbit-index equivalence. -/
@[simp]
theorem orbitOf_assembledCorrespondence_symm
    (d : CliffordLocalAssemblyData P)
    (ψ : PPrimeIrreducibleCharacter d.intermediate p) :
    letI : d.ambientNormal.Normal :=
      d.ambientNormal_normal
    letI : d.intermediateNormal.Normal :=
      d.intermediateNormal_normal
    orbitOf d.ambientNormal
        (d.assembledCorrespondence.symm ψ).1 =
      d.orbitwise.orbitEquiv.symm
        (orbitOf d.intermediateNormal ψ.1) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype d.intermediate :=
    Fintype.ofFinite d.intermediate
  letI : d.ambientNormal.Normal :=
    d.ambientNormal_normal
  letI : d.intermediateNormal.Normal :=
    d.intermediateNormal_normal
  exact d.orbitwise.orbitOf_assemble_symm ψ

end CliffordLocalAssemblyData

/-! ## Families and normalizer induction -/

/-- A Clifford local assembly package for every finite group and Sylow
subgroup supplies the numerical inductive McKay condition. -/
theorem numericalInductiveMcKayOfCliffordFamily
    (family :
      ∀ (Y : Type) [Group Y] [Finite Y] (Q : Sylow p Y),
        CliffordLocalAssemblyData Q) :
    NumericalInductiveMcKay.{0} p := by
  intro Y _ _ Q
  exact ⟨(family Y Q).toLocalCorrespondence⟩

/-- The explicit correspondence with the Sylow normalizer obtained by
feeding a Clifford-local family into the existing normalizer induction. -/
def normalizerCorrespondenceOfCliffordFamily
    (family :
      ∀ (Y : Type) [Group Y] [Finite Y] (Q : Sylow p Y),
        CliffordLocalAssemblyData Q)
    (G : Type) [Group G] [Finite G] (P : Sylow p G) :
    McKayCorrespondence G p P :=
  (numericalInductiveMcKayOfCliffordFamily family).correspondence G P

/-- Therefore a family of orbitwise Clifford local packages proves the
cardinal McKay statement through the existing normalizer induction. -/
theorem statementOfCliffordFamily
    [Fact p.Prime]
    (family :
      ∀ (Y : Type) [Group Y] [Finite Y] (Q : Sylow p Y),
        CliffordLocalAssemblyData Q)
    (G : Type) [Group G] [Finite G] (P : Sylow p G) :
    Statement G p P :=
  (numericalInductiveMcKayOfCliffordFamily family).statement G P

end McKayConjecture.InductiveMcKay
