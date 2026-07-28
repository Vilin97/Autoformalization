/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralCharacterExtension
import McKayConjecture.InductiveMcKay.CentralTripleCliffordAssembly

/-!
# Extension transport for bundled central-isomorphism witnesses

This file exposes the extension-preservation theorem through the bundled
`CompleteCentralIsomorphismWitness` API.  It avoids making callers unpack
the existential representation spaces supplied by an inductive-McKay
triple-compatibility field.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace CompleteCentralIsomorphismWitness

open CharacterTriple

variable {A B : Type}
  [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}

/-- The target irreducible character obtained from an exact source
extension through a bundled complete central-isomorphism witness. -/
def extensionImage
    (C : CompleteCentralIsomorphismWitness T U)
    (χ : IrreducibleCharacter A)
    (hχ :
      IrreducibleCharacter.IsExtensionAlong
        T.normalSubgroup.subtype T.character χ) :
    IrreducibleCharacter B := by
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  exact
    C.witness.rightMultiplicityCharacter χ hχ.liesOver

/-- A bundled complete central-isomorphism witness sends an exact extension
to an exact extension of the target normal character. -/
theorem extensionImage_isExtension
    (C : CompleteCentralIsomorphismWitness T U)
    (χ : IrreducibleCharacter A)
    (hχ :
      IrreducibleCharacter.IsExtensionAlong
        T.normalSubgroup.subtype T.character χ) :
    IrreducibleCharacter.IsExtensionAlong
      U.normalSubgroup.subtype U.character
      (C.extensionImage χ hχ) := by
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  exact
    C.witness.rightMultiplicityCharacter_isExtension_of_isExtension
      χ hχ

end CompleteCentralIsomorphismWitness
end InductiveMcKay
end McKayConjecture
