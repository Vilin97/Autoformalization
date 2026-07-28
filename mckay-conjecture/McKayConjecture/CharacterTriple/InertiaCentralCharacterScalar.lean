/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralCharacterScalar
import McKayConjecture.CharacterTriple.Inertia

/-!
# Central scalars in the inertia character correspondence

This file specializes the central-scalar identity for a central
character-triple correspondence to the canonical inertia triples used in
Clifford theory.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace CentralIsomorphismWitness

open CliffordCorrespondence
open CliffordEquivalence

variable {G H : Type}
variable [Group G] [Finite G] [Group H] [Finite H]
variable (N : Subgroup G) [N.Normal]
variable (M : Subgroup H) [M.Normal]
variable (θ : IrreducibleCharacter N)
variable (φ : IrreducibleCharacter M)
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]

/-- The prime-to-`p` correspondence between matched inertia triples
preserves normalized values at every matched centralizer element. -/
theorem pPrimeInertiaEquiv_matchedCentral_cross
    {p : ℕ} (hp : p.Prime)
    (C :
      CentralIsomorphismWitness
        (ofInertia N θ) (ofInertia M φ) V W)
    (hθ : θ.IsPPrimeDegree p)
    (hφ : φ.IsPPrimeDegree p)
    (χ : PPrimeIrreducibleCharactersOverInertia N θ p)
    (b : IrreducibleCharacter.inertia M φ)
    (hb :
      C.embedding b ∈
        Subgroup.centralizer
          ((ofInertia N θ).normalSubgroup :
            Set (IrreducibleCharacter.inertia N θ))) :
    χ.1.1.values (C.embedding b) *
        ((C.pPrimeInertiaEquiv
          N θ M φ hp hθ hφ χ).1.1.degree : ℂ) =
      (C.pPrimeInertiaEquiv
          N θ M φ hp hθ hφ χ).1.1.values b *
        (χ.1.1.degree : ℂ) := by
  let χTriple :=
    pPrimeIrreducibleCharactersOverInertiaEquivTriple
      N θ p χ
  have hcross :=
    C.rightCharacterMap_matchedCentral_cross
      χTriple.1 b hb
  simpa only [χTriple,
    pPrimeInertiaEquiv_apply_coe,
    centralPPrimeCharacterEquiv_apply,
    rightPPrimeCharacterMap_apply_value,
    rightCharacterMap_apply_value,
    pPrimeIrreducibleCharactersOverInertiaEquivTriple_apply_coe
  ] using hcross

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
