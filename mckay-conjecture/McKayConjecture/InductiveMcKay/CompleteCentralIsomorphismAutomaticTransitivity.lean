/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralIsomorphismAutomaticTransitivity
import McKayConjecture.InductiveMcKay.CentralTripleCliffordAssembly

/-!
# Automatic transitivity for bundled central-isomorphism witnesses

This file lifts the gauge-adjusted composition theorem for
`CentralIsomorphismWitness` to the existentially bundled representation
spaces used by the inductive-McKay assembly layer.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace CompleteCentralIsomorphismWitness

open CharacterTriple

variable {A B D : Type}
  [Group A] [Finite A] [Group B] [Finite B] [Group D] [Finite D]
variable {T : CharacterTriple A} {U : CharacterTriple B}
  {Z : CharacterTriple D}

/-- Compose two complete central-isomorphism witnesses.  The potentially
unrelated projective realizations of the middle triple are aligned
canonically by associated-lift uniqueness. -/
def composeAutomatic
    (C₁ : CompleteCentralIsomorphismWitness T U)
    (C₂ : CompleteCentralIsomorphismWitness U Z) :
    CompleteCentralIsomorphismWitness T Z := by
  letI := C₁.leftAddCommGroup
  letI := C₁.leftModule
  letI := C₁.leftModuleFinite
  letI := C₁.leftNontrivial
  letI := C₁.rightAddCommGroup
  letI := C₁.rightModule
  letI := C₁.rightModuleFinite
  letI := C₁.rightNontrivial
  letI := C₂.leftAddCommGroup
  letI := C₂.leftModule
  letI := C₂.leftModuleFinite
  letI := C₂.leftNontrivial
  letI := C₂.rightAddCommGroup
  letI := C₂.rightModule
  letI := C₂.rightModuleFinite
  letI := C₂.rightNontrivial
  exact
    { leftSpace := C₁.leftSpace
      rightSpace := C₂.rightSpace
      witness := C₁.witness.composeAutomatic C₂.witness }

/-- The embedding of the bundled composite is the composite of the two
stored embeddings. -/
theorem composeAutomatic_embedding
    (C₁ : CompleteCentralIsomorphismWitness T U)
    (C₂ : CompleteCentralIsomorphismWitness U Z) :
    (C₁.composeAutomatic C₂).embedding =
      C₁.embedding.comp C₂.embedding := by
  letI := C₁.leftAddCommGroup
  letI := C₁.leftModule
  letI := C₁.leftModuleFinite
  letI := C₁.leftNontrivial
  letI := C₁.rightAddCommGroup
  letI := C₁.rightModule
  letI := C₁.rightModuleFinite
  letI := C₁.rightNontrivial
  letI := C₂.leftAddCommGroup
  letI := C₂.leftModule
  letI := C₂.leftModuleFinite
  letI := C₂.leftNontrivial
  letI := C₂.rightAddCommGroup
  letI := C₂.rightModule
  letI := C₂.rightModuleFinite
  letI := C₂.rightNontrivial
  exact
    CharacterTriple.CentralIsomorphismWitness.composeAutomatic_embedding
      C₁.witness C₂.witness

/-- Compose complete witnesses after transporting the second witness's
left projective realization onto the first witness's right representation
space.  This stricter form is convenient for character-functoriality
lemmas whose middle representation must agree definitionally. -/
def composeAutomaticStrict
    (C₁ : CompleteCentralIsomorphismWitness T U)
    (C₂ : CompleteCentralIsomorphismWitness U Z) :
    CompleteCentralIsomorphismWitness T Z := by
  letI := C₁.leftAddCommGroup
  letI := C₁.leftModule
  letI := C₁.leftModuleFinite
  letI := C₁.leftNontrivial
  letI := C₁.rightAddCommGroup
  letI := C₁.rightModule
  letI := C₁.rightModuleFinite
  letI := C₁.rightNontrivial
  letI := C₂.leftAddCommGroup
  letI := C₂.leftModule
  letI := C₂.leftModuleFinite
  letI := C₂.leftNontrivial
  letI := C₂.rightAddCommGroup
  letI := C₂.rightModule
  letI := C₂.rightModuleFinite
  letI := C₂.rightNontrivial
  exact
    { leftSpace := C₁.leftSpace
      rightSpace := C₂.rightSpace
      witness := C₁.witness.composeAutomaticStrict C₂.witness }

/-- The strict bundled composite has the expected composite embedding. -/
theorem composeAutomaticStrict_embedding
    (C₁ : CompleteCentralIsomorphismWitness T U)
    (C₂ : CompleteCentralIsomorphismWitness U Z) :
    (C₁.composeAutomaticStrict C₂).embedding =
      C₁.embedding.comp C₂.embedding := by
  letI := C₁.leftAddCommGroup
  letI := C₁.leftModule
  letI := C₁.leftModuleFinite
  letI := C₁.leftNontrivial
  letI := C₁.rightAddCommGroup
  letI := C₁.rightModule
  letI := C₁.rightModuleFinite
  letI := C₁.rightNontrivial
  letI := C₂.leftAddCommGroup
  letI := C₂.leftModule
  letI := C₂.leftModuleFinite
  letI := C₂.leftNontrivial
  letI := C₂.rightAddCommGroup
  letI := C₂.rightModule
  letI := C₂.rightModuleFinite
  letI := C₂.rightNontrivial
  exact
    CharacterTriple.CentralIsomorphismWitness.composeAutomaticStrict_embedding
      C₁.witness C₂.witness

end CompleteCentralIsomorphismWitness
end InductiveMcKay
end McKayConjecture
