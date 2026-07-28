/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralCharacterBijection

/-!
# Character bijections from factor-matched projective lifts

The ordinary character correspondence attached to a character-triple
comparison only uses:

* injectivity of the right ambient embedding;
* the product and intersection conditions;
* associated projective lifts whose factor sets agree literally.

It does not use containment of the left centralizer or scalar agreement on
that centralizer.  The underlying construction is implemented for
`FactorMatchedIsomorphismWitness` in the central-character modules.  This
file exposes the two final equivalences under names that do not suggest the
stronger central-isomorphism hypotheses.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FactorMatchedIsomorphismWitness

variable {A B : Type}
variable [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]

/-- Irreducible characters on the two ambient groups lying over the
distinguished normal characters. -/
def irreducibleCharactersOverEquiv
    (C : FactorMatchedIsomorphismWitness T U V W) :
    CliffordCorrespondence.IrreducibleCharactersOverAlong
        T.normalSubgroup.subtype T.character ≃
      CliffordCorrespondence.IrreducibleCharactersOverAlong
        U.normalSubgroup.subtype U.character :=
  C.centralCharacterEquiv

@[simp]
theorem irreducibleCharactersOverEquiv_apply
    (C : FactorMatchedIsomorphismWitness T U V W)
    (χ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      T.normalSubgroup.subtype T.character) :
    C.irreducibleCharactersOverEquiv χ = C.rightCharacterMap χ :=
  rfl

/-- The factor-matched character equivalence restricted to characters of
degree prime to `p`. -/
def pPrimeIrreducibleCharactersOverEquiv
    {p : ℕ} (hp : p.Prime)
    (C : FactorMatchedIsomorphismWitness T U V W)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character ≃
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p U.normalSubgroup.subtype U.character :=
  C.centralPPrimeCharacterEquiv hp hT hU

@[simp]
theorem pPrimeIrreducibleCharactersOverEquiv_apply
    {p : ℕ} (hp : p.Prime)
    (C : FactorMatchedIsomorphismWitness T U V W)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p)
    (χ :
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character) :
    C.pPrimeIrreducibleCharactersOverEquiv hp hT hU χ =
      C.rightPPrimeCharacterMap hp hT hU χ :=
  rfl

end FactorMatchedIsomorphismWitness
end CharacterTriple
end McKayConjecture
