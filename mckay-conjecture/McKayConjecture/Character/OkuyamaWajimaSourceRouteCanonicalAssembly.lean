/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaPrintedCanonicalAssembly
import McKayConjecture.Character.OkuyamaWajimaPrintedStatementSourceRoute
import McKayConjecture.Character.OkuyamaWajimaSourceRouteAutomatic

/-!
# Canonical assembly of the source-level Okuyama--Wajima route

The completed canonical strong induction proves the universal printed
Okuyama--Wajima extension statement.  Specializing that theorem to the
finite local groups used by the source route supplies its printed-theorem
input without any additional hypothesis.

The final two theorems insert this automatic input into the existing
single-subgroup and uniform source-level comparison APIs.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open GroupTheory
open OkuyamaWajimaPrintedStatementSourceRoute

variable {A : Type} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable (K Q : Subgroup A) [K.Normal]

/-- The source-route form of the printed Okuyama--Wajima theorem,
discharged by the complete canonical strong induction. -/
theorem invariantOkuyamaWajimaPrintedExtensionTheoremInput_automatic
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    InvariantOkuyamaWajimaPrintedExtensionTheoremInput
      K Q hQ hK d theta hinvariant := by
  apply
    invariantOkuyamaWajimaPrintedExtensionTheoremInput_of_universal
      K Q hQ hK d theta hinvariant
  intro G _ _
  exact okuyamaWajimaPrintedExtensionStatement G

section SingleSubgroup

variable (V : Subgroup A)

/-- The source-faithful single-subgroup Okuyama--Wajima extension
comparison, with both the printed theorem and Navarro deletion
discharged automatically. -/
theorem okuyamaWajimaExtensionConclusion_automatic
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
        (coprimeFixedPoints K Q).subgroupOf V) :
    okuyamaWajimaExtensionConclusion
      K Q V hCV d theta := by
  exact
    okuyamaWajimaExtensionConclusion_of_printed
      K Q V hQ hK hKQ hV hCV d theta hinvariant hcomm
      (invariantOkuyamaWajimaPrintedExtensionTheoremInput_automatic
        K Q hQ hK d theta hinvariant)

end SingleSubgroup

section Uniform

variable (U : Subgroup A)

/-- The uniform source-level Okuyama--Wajima extension comparison, with
the printed theorem and every Navarro deletion instance discharged
automatically. -/
theorem uniformOkuyamaWajimaExtensionComparison_automatic
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hKQ : (K ⊔ Q).Normal)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    UniformOkuyamaWajimaExtensionComparison
      K Q U d theta := by
  exact
    uniformOkuyamaWajimaExtensionComparison_of_printed
      K Q U hQ hK hKQ hU d theta hinvariant
      (invariantOkuyamaWajimaPrintedExtensionTheoremInput_automatic
        K Q hQ hK d theta hinvariant)

end Uniform

end McKayConjecture
