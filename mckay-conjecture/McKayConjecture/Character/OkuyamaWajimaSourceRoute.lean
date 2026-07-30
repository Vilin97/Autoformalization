/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaNavarroInput
import McKayConjecture.Character.OkuyamaWajimaPrimeAwayOriginal

/-!
# Source-level assembly of the Okuyama--Wajima comparison

This file composes the proved abelian-quotient Navarro input with the exact
prime-away adapter for the printed Okuyama--Wajima theorem.

All formal group and character-triple coordinates are discharged.  The two
remaining premises are precisely the source theorems which have not yet been
formalized: the printed ordinary extension clause and Navarro's deletion of
the adjoined Sylow subgroup `Q`.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open GroupTheory

variable {A : Type} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable (K Q V : Subgroup A) [K.Normal]

/-- The source-faithful single-subgroup route to the ordinary
Okuyama--Wajima extension comparison. -/
theorem okuyamaWajimaExtensionConclusion_of_printed_of_qDeletion
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hKQ : (K ⊔ Q).Normal)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hcomm :
      _root_.commutator V ≤
        (coprimeFixedPoints K Q).subgroupOf V)
    (hprinted :
      InvariantOkuyamaWajimaPrintedExtensionTheoremInput
        K Q hQ hK d theta hinvariant)
    (hdelete :
      InvariantOkuyamaWajimaPrimeAwayQDeletionInput
        K Q V hQ hK hV hCV d theta hinvariant) :
    okuyamaWajimaExtensionConclusion
      K Q V hCV d theta := by
  obtain ⟨hNavarroSource, hNavarroTarget⟩ :=
    invariantOkuyamaWajimaNavarroInput_of_commutator_le
      K Q V hQ hK hV hCV d theta hinvariant hcomm
  exact
    okuyamaWajimaExtensionConclusion_of_navarro_of_primeAway
      K Q V hQ hK hV hCV d theta hinvariant
      hNavarroSource hNavarroTarget
      ((invariantOkuyamaWajimaPrimeAwayOriginalConclusion_of_printed
        K Q V hQ hK hV hCV d theta hinvariant
        hprinted hdelete) hKQ hcomm)

section Uniform

variable (U : Subgroup A)

/-- Uniform source-level route consumed by the good-element count.

The abelian Navarro premise is proved internally; only the printed OW
extension theorem and the uniform Navarro `Q`-deletion theorem remain as
premises. -/
theorem uniformOkuyamaWajimaExtensionComparison_of_printed_of_qDeletion
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hKQ : (K ⊔ Q).Normal)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hprinted :
      InvariantOkuyamaWajimaPrintedExtensionTheoremInput
        K Q hQ hK d theta hinvariant)
    (hdelete :
      UniformInvariantOkuyamaWajimaPrimeAwayQDeletionInput
        K Q U hQ hK hU d theta hinvariant) :
    UniformOkuyamaWajimaExtensionComparison
      K Q U d theta := by
  exact
    uniformOkuyamaWajimaExtensionComparison_of_primeLocal
      K Q U hQ hK hKQ hU d theta hinvariant
      (uniformInvariantOkuyamaWajimaNavarroInput
        K Q U hQ hK hU d theta hinvariant)
      (uniformInvariantOkuyamaWajimaPrimeAwayOriginalInput_of_printed
        K Q U hQ hK hU d theta hinvariant hprinted hdelete)

end Uniform

end McKayConjecture
