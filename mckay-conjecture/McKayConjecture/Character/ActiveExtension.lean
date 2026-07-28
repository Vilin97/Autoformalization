/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ActiveOrbitTransport
import McKayConjecture.Character.CliffordEquivalence
import McKayConjecture.Character.ExtensionConstituent

/-!
# Prime-to-`p` extensions activate Clifford orbits

An explicit prime-to-`p` ambient character lying over a prime-to-`p`
normal-subgroup character is a witness that the corresponding Clifford
orbit is active.  In particular, any prime-to-`p` extension supplies such
a witness.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordPartition

open CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal]
variable {p : ℕ}

/-- A prime-to-`p` ambient constituent activates the Clifford orbit of the
normal-subgroup character below it. -/
theorem isActivePPrimeCharacter_of_liesOver
    (θ : PPrimeIrreducibleCharacter N p)
    (χ : PPrimeIrreducibleCharacter G p)
    (hχ : LiesOverAlong N.subtype θ.1 χ.1) :
    IsActivePPrimeCharacter N θ := by
  let q : OrbitSpace N :=
    Quotient.mk'' θ.1
  have hq :
      (Quotient.mk'' q.out : OrbitSpace N) =
        Quotient.mk'' θ.1 :=
    Quotient.out_eq' q
  let χθ :
      PPrimeIrreducibleCharactersOverOrbit N θ.1 p :=
    ⟨⟨χ.1, liesOverOrbit_of_liesOver N θ.1 hχ⟩, χ.2⟩
  exact
    ⟨(pPrimeOrbitBlockEquivOfQuotientMkEq
        N hq p).symm χθ⟩

/-- Activity is equivalent to the existence of a prime-to-`p` ambient
character lying over the character itself.  Clifford theory lets one
replace the conjugate constituent appearing in the orbit-block definition
by the selected representative. -/
theorem isActivePPrimeCharacter_iff_exists_liesOver
    (θ : PPrimeIrreducibleCharacter N p) :
    IsActivePPrimeCharacter N θ ↔
      ∃ χ : PPrimeIrreducibleCharacter G p,
        LiesOverAlong N.subtype θ.1 χ.1 := by
  letI : Fintype G := Fintype.ofFinite G
  constructor
  · rintro ⟨χ⟩
    let q : OrbitSpace N :=
      Quotient.mk'' θ.1
    have hq :
        (Quotient.mk'' q.out : OrbitSpace N) =
          Quotient.mk'' θ.1 :=
      Quotient.out_eq' q
    let χθ :
        PPrimeIrreducibleCharactersOverOrbit N θ.1 p :=
      pPrimeOrbitBlockEquivOfQuotientMkEq
        N hq p χ
    exact
      ⟨⟨χθ.1.1, χθ.2⟩,
        CliffordEquivalence.liesOver_of_liesOverOrbit
          N θ.1 χθ.1.1 χθ.1.2⟩
  · rintro ⟨χ, hχ⟩
    exact
      isActivePPrimeCharacter_of_liesOver
        N θ χ hχ

/-- A prime-to-`p` extension activates the Clifford orbit of the character
being extended. -/
theorem isActivePPrimeCharacter_of_isExtension
    (θ : PPrimeIrreducibleCharacter N p)
    (χ : PPrimeIrreducibleCharacter G p)
    (hχ :
      IrreducibleCharacter.IsExtensionAlong
        N.subtype θ.1 χ.1) :
    IsActivePPrimeCharacter N θ :=
  isActivePPrimeCharacter_of_liesOver
    N θ χ hχ.liesOver

end CliffordPartition
end McKayConjecture
