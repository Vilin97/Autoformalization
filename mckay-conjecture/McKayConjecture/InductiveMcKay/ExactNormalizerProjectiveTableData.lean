/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.ExactNormalizerData
import McKayConjecture.InductiveMcKay.SemidirectStructure

/-!
# Concrete projective-table data at the exact Sylow normalizer

For a fixed finite group `G` and a fixed Sylow subgroup `P`, a direct
character-table verification of the inductive McKay condition has two
representation-theoretic ingredients:

* an `Aut(G)_P`-equivariant bijection between the `p'`-degree irreducible
  characters of `G` and `N_G(P)`; and
* for every paired character, associated projective representations whose
  factor sets and central scalars agree along
  `N_G(P) ⋊ Γ_χ ↪ G ⋊ Γ_χ`.

`ExactNormalizerProjectiveTableData` bundles exactly these ingredients.
It does not ask for any of the ordinary subgroup clauses of a central
character-triple isomorphism.  Those clauses are automatic for the exact
normalizer and are supplied by `SemidirectStructure`.

This is useful for finite character-table computations: after the character
and projective matrices have been written down, this file turns their checked
identities directly into `LocalInductiveMcKayData`.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {G : Type u} [Group G] {p : ℕ}

namespace EquivariantMcKayEquiv

variable {P : Sylow p G}

/-- Regard an exact-normalizer character equivalence as an equivariant local
correspondence whose intermediate subgroup is literally `N_G(P)`. -/
def toExactNormalizerLocalCorrespondence
    (e : EquivariantMcKayEquiv P) :
    EquivariantLocalCorrespondence P where
  toLocalCorrespondence :=
    { intermediate := Subgroup.normalizer (P : Set G)
      normalizer_le := le_rfl
      proper_of_normalizer_ne_top := fun h ↦
        lt_top_iff_ne_top.mpr h
      correspondence := e.toEquiv }
  intermediate_invariant :=
    SylowAutStabilizer.normalizer_invariant P
  map_smul' := by
    intro a χ
    exact e.map_smul a χ

@[simp]
theorem toExactNormalizerLocalCorrespondence_intermediate
    (e : EquivariantMcKayEquiv P) :
    e.toExactNormalizerLocalCorrespondence.intermediate =
      Subgroup.normalizer (P : Set G) :=
  rfl

end EquivariantMcKayEquiv

/-- The projective data attached to one row of an exact-normalizer character
table correspondence.  Bundling the representation spaces here avoids any
universe restriction on the finite group whose table is being checked. -/
structure ExactNormalizerProjectiveRowData
    [Finite G] {P : Sylow p G}
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p) where
  /-- Representation space for the ambient semidirect product. -/
  leftSpace : Type
  /-- Representation space for the normalizer semidirect product. -/
  rightSpace : Type
  [leftAddCommGroup : AddCommGroup leftSpace]
  [leftModule : Module ℂ leftSpace]
  [leftModuleFinite : Module.Finite ℂ leftSpace]
  [leftNontrivial : Nontrivial leftSpace]
  [rightAddCommGroup : AddCommGroup rightSpace]
  [rightModule : Module ℂ rightSpace]
  [rightModuleFinite : Module.Finite ℂ rightSpace]
  [rightNontrivial : Nontrivial rightSpace]
  /-- The two associated projective representations and the checked factor
  and scalar identities. -/
  witness :
    EquivariantLocalCorrespondence.ProjectiveCompatibilityWitness
      e.toExactNormalizerLocalCorrespondence χ leftSpace rightSpace

/-- The concrete character-table and projective-representation input for one
finite group and one chosen Sylow subgroup.

The second field is intentionally stated using independent representation
spaces: corresponding characters need not have equal degrees. -/
structure ExactNormalizerProjectiveTableData
    [Finite G] (P : Sylow p G) where
  /-- The checked equivariant bijection of the two `p'`-character tables. -/
  characterTableEquiv : EquivariantMcKayEquiv P
  /-- The checked projective factor-set and central-scalar identities for
  every row paired by `characterTableEquiv`. -/
  projectiveComparison :
    ∀ χ : PPrimeIrreducibleCharacter G p,
      ExactNormalizerProjectiveRowData characterTableEquiv χ

namespace ExactNormalizerProjectiveTableData

variable [Finite G] {P : Sylow p G}

/-- The exact-normalizer local correspondence underlying the table datum. -/
def toEquivariantLocalCorrespondence
    (d : ExactNormalizerProjectiveTableData P) :
    EquivariantLocalCorrespondence P :=
  d.characterTableEquiv.toExactNormalizerLocalCorrespondence

/-- A checked projective-table datum supplies the full local inductive McKay
datum.  Injectivity, the centralizer inclusion, the ambient product, and the
intersection identity are derived automatically from the canonical
normalizer embedding. -/
def toLocalInductiveMcKayData
    (d : ExactNormalizerProjectiveTableData P) :
    LocalInductiveMcKayData P where
  toEquivariantLocalCorrespondence :=
    d.toEquivariantLocalCorrespondence
  triple_compatible := by
    intro χ
    let C := d.projectiveComparison χ
    letI := C.leftAddCommGroup
    letI := C.leftModule
    letI := C.leftModuleFinite
    letI := C.leftNontrivial
    letI := C.rightAddCommGroup
    letI := C.rightModule
    letI := C.rightModuleFinite
    letI := C.rightNontrivial
    exact C.witness.tripleCompatible

/-- The same concrete data can be viewed in the exact-normalizer interface
used by recursive normalizer composition. -/
def toExactNormalizerInductiveMcKayData
    (d : ExactNormalizerProjectiveTableData P) :
    ExactNormalizerInductiveMcKayData P where
  toEquivariantMcKayEquiv := d.characterTableEquiv
  triple_compatible := by
    intro χ
    let C := d.projectiveComparison χ
    letI := C.leftAddCommGroup
    letI := C.leftModule
    letI := C.leftModuleFinite
    letI := C.leftNontrivial
    letI := C.rightAddCommGroup
    letI := C.rightModule
    letI := C.rightModuleFinite
    letI := C.rightNontrivial
    exact
      ⟨C.leftSpace, C.rightSpace, inferInstance, inferInstance,
        inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, inferInstance,
        C.witness.toCentralIsomorphismWitness, rfl⟩

end ExactNormalizerProjectiveTableData

end InductiveMcKay
end McKayConjecture
