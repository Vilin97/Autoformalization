/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaSourceRoute
import McKayConjecture.Character.NavarroGeneralLocalGlobalExtension

/-!
# Automatic source-level assembly of the Okuyama--Wajima comparison

The general Navarro local--global extension theorem proves that adjoining
the normal Sylow subgroup `Q` does not affect extension existence on the
prime-away local pieces.  This file inserts that result into the
source-level Okuyama--Wajima route.

Consequently the only remaining mathematical input to the theorems below
is the ordinary extension clause of the printed Okuyama--Wajima theorem.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open GroupTheory

variable {A : Type} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable (K Q V : Subgroup A) [K.Normal]

/-- The source-faithful single-subgroup Okuyama--Wajima extension
comparison, with Navarro `Q`-deletion discharged automatically. -/
theorem okuyamaWajimaExtensionConclusion_of_printed
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
        K Q hQ hK d theta hinvariant) :
    okuyamaWajimaExtensionConclusion
      K Q V hCV d theta := by
  exact
    okuyamaWajimaExtensionConclusion_of_printed_of_qDeletion
      K Q V hQ hK hKQ hV hCV d theta hinvariant hcomm hprinted
      (invariantOkuyamaWajimaPrimeAwayQDeletionInput_of_normalProduct
        K Q V hQ hK hKQ hV hCV d theta hinvariant)

section Uniform

variable (U : Subgroup A)

/-- The uniform source-level Okuyama--Wajima extension comparison, with
Navarro `Q`-deletion discharged automatically at every intermediate
subgroup. -/
theorem uniformOkuyamaWajimaExtensionComparison_of_printed
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hKQ : (K ⊔ Q).Normal)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hprinted :
      InvariantOkuyamaWajimaPrintedExtensionTheoremInput
        K Q hQ hK d theta hinvariant) :
    UniformOkuyamaWajimaExtensionComparison
      K Q U d theta := by
  apply
    uniformOkuyamaWajimaExtensionComparison_of_printed_of_qDeletion
      K Q U hQ hK hKQ hU d theta hinvariant hprinted
  intro V hCV hVU
  exact
    invariantOkuyamaWajimaPrimeAwayQDeletionInput_of_normalProduct
      K Q V hQ hK hKQ (hVU.trans hU) hCV d theta hinvariant

end Uniform

end McKayConjecture
