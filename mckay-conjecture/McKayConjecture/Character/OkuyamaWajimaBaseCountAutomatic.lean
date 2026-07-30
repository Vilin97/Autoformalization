/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaCanonicalBaseExtension

/-!
# The automatic Okuyama--Wajima base-extension count

Ambient invariance of the kernel character produces the determinant-normalized
source and target base extensions.  Consequently, the base-count theorem no
longer needs a separate canonical-extension existence hypothesis: its only
remaining character-theoretic input is the semantic uniform ordinary
Okuyama--Wajima comparison.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open CliffordCorrespondence
open GroupTheory

variable {Γ : Type} [Group Γ] [Finite Γ]
variable {p : ℕ} [Fact p.Prime]

/-- The canonical source and target base extensions supplied automatically by
ambient invariance.  This definition exposes the chosen extension data for
later constructions that need the actual characters rather than just their
fibre cardinalities. -/
def okuyamaWajimaInvariantCanonicalBaseExtensionData
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (hinvariant : ∀ g : Γ, g • θ.1.1 = θ.1.1) :
    OkuyamaWajimaBaseExtensionData S K hKS d θ :=
  okuyamaWajimaCanonicalBaseExtensionData
    S K hKS d θ
    (okuyamaWajimaCanonicalBaseExtensionHypothesis_of_invariant
      S K hK hKS d θ hinvariant)

/-- Automatic canonical-base form of the Okuyama--Wajima base count.

The invariant determinant-normalized base extensions are constructed from the
displayed group and character hypotheses.  Thus the semantic uniform ordinary
Okuyama--Wajima comparison is the only remaining input beyond the hypotheses
already intrinsic to the setup. -/
theorem natCard_over_invariantCanonicalExtension_eq_normalizer
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (hinvariant : ∀ g : Γ, g • θ.1.1 = θ.1.1)
    (how :
      OkuyamaWajimaComplementUniformOrdinaryInput
        S K hK hKS d θ) :
    let c :=
      okuyamaWajimaInvariantCanonicalBaseExtensionData
        S K hK hKS d θ hinvariant
    Nat.card
        (IrreducibleCharactersOverAlong
          (K ⊔ (S : Subgroup Γ) : Subgroup Γ).subtype
          c.sourceExtension) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)).subtype
          c.targetExtension) :=
  natCard_over_okuyamaWajimaBaseExtensions_eq_normalizer
    S K hK hKS d θ hinvariant
    (okuyamaWajimaInvariantCanonicalBaseExtensionData
      S K hK hKS d θ hinvariant)
    how

/-- Existential form of the automatic canonical-base count.  This endpoint is
convenient when downstream code only needs a pair of compatible base
extensions and the resulting cardinality equality. -/
theorem exists_okuyamaWajimaBaseExtensionData_natCard_eq_normalizer
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (hinvariant : ∀ g : Γ, g • θ.1.1 = θ.1.1)
    (how :
      OkuyamaWajimaComplementUniformOrdinaryInput
        S K hK hKS d θ) :
    ∃ c : OkuyamaWajimaBaseExtensionData S K hKS d θ,
      Nat.card
          (IrreducibleCharactersOverAlong
            (K ⊔ (S : Subgroup Γ) : Subgroup Γ).subtype
            c.sourceExtension) =
        Nat.card
          (IrreducibleCharactersOverAlong
            (okuyamaWajimaInternalNormalProduct
              K (S : Subgroup Γ)).subtype
            c.targetExtension) := by
  let c :=
    okuyamaWajimaInvariantCanonicalBaseExtensionData
      S K hK hKS d θ hinvariant
  refine ⟨c, ?_⟩
  exact
    natCard_over_okuyamaWajimaBaseExtensions_eq_normalizer
      S K hK hKS d θ hinvariant c how

end McKayConjecture
