/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.NormalProductParameterTwist
import McKayConjecture.Character.OkuyamaWajimaBaseCountAutomatic

/-!
# The ordinary Okuyama--Wajima count for each linear parameter

The automatic canonical-base theorem gives the ordinary fibre count for
the determinant-normalized source and target extensions.  An invariant
linear character of either quotient Sylow subgroup extends independently
to the corresponding ambient group.  Twisting by those two unrelated
extensions therefore transports the base equality to every pair of linear
parameters.

The target base extension is defined on the internal normal product inside
the Sylow normalizer.  The first part of this file supplies the exact
projection from that subgroup to its quotient Sylow image.  This avoids
transporting the final theorem across the propositionally equal subgroup
`D ⊔ S`.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open CliffordCorrespondence
open GroupTheory

variable {Γ : Type} [Group Γ] [Finite Γ]
variable {p : ℕ} [Fact p.Prime]

/-! ### The target normal-product quotient projection -/

/-- The quotient projection from the internal target normal product to
the Sylow image modulo the internal fixed-point kernel. -/
def okuyamaWajimaTargetQuotientProjection
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K) :
    letI :
        (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ)).Normal :=
      internalFixedPoints_normal K (S : Subgroup Γ)
    okuyamaWajimaInternalNormalProduct K (S : Subgroup Γ) →*
      (normalProductQuotientSylow
        (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
        (okuyamaWajimaSylowInNormalizer S) :
          Subgroup
            (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
              okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ))) := by
  letI :
      (okuyamaWajimaInternalFixedPoints
        K (S : Subgroup Γ)).Normal :=
    internalFixedPoints_normal K (S : Subgroup Γ)
  let D :=
    okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ)
  let L :=
    okuyamaWajimaInternalNormalProduct K (S : Subgroup Γ)
  let P :=
    normalProductQuotientSylow
      D (okuyamaWajimaSylowInNormalizer S)
  exact
    { toFun := fun x =>
        ⟨QuotientGroup.mk' D (x :
            Subgroup.normalizer ((S : Subgroup Γ) : Set Γ)), by
          rw [← map_internalNormalProduct_eq_quotientSylow
            S K hK]
          exact ⟨x, x.property, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        rfl }

@[simp]
theorem okuyamaWajimaTargetQuotientProjection_apply
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (x :
      okuyamaWajimaInternalNormalProduct K (S : Subgroup Γ)) :
    letI :
        (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ)).Normal :=
      internalFixedPoints_normal K (S : Subgroup Γ)
    ((okuyamaWajimaTargetQuotientProjection S K hK x :
        normalProductQuotientSylow
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
          (okuyamaWajimaSylowInNormalizer S)) :
      Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
        okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ)) =
      QuotientGroup.mk'
        (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
        (x : Subgroup.normalizer ((S : Subgroup Γ) : Set Γ)) :=
  rfl

/-- The chosen inflated extension of a target quotient-Sylow parameter
restricts to its pullback along the internal target projection. -/
theorem inflatedOkuyamaWajimaTargetLinearExtension_spec
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (mu :
      letI :
          (okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ)).Normal :=
        internalFixedPoints_normal K (S : Subgroup Γ)
      (normalProductQuotientSylow
        (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
        (okuyamaWajimaSylowInNormalizer S) :
          Subgroup
            (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
              okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ))) →* ℂˣ)
    (hmu :
      letI :
          (okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ)).Normal :=
        internalFixedPoints_normal K (S : Subgroup Γ)
      letI :
          (normalProductQuotientSylow
            (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
            (okuyamaWajimaSylowInNormalizer S) :
              Subgroup
                (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
                  okuyamaWajimaInternalFixedPoints
                    K (S : Subgroup Γ))).Normal :=
        okuyamaWajimaQuotientSylow_normal S K hK hKS
      MonoidHom.IsConjugationInvariant
        (normalProductQuotientSylow
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
          (okuyamaWajimaSylowInNormalizer S) :
            Subgroup
              (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
                okuyamaWajimaInternalFixedPoints
                  K (S : Subgroup Γ)))
        mu) :
    letI :
        (okuyamaWajimaInternalFixedPoints
          K (S : Subgroup Γ)).Normal :=
      internalFixedPoints_normal K (S : Subgroup Γ)
    letI :
        (normalProductQuotientSylow
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
          (okuyamaWajimaSylowInNormalizer S) :
            Subgroup
              (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
                okuyamaWajimaInternalFixedPoints
                  K (S : Subgroup Γ))).Normal :=
      okuyamaWajimaQuotientSylow_normal S K hK hKS
    (inflatedNormalQuotientSylowLinearExtension
        (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
        (normalProductQuotientSylow
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
          (okuyamaWajimaSylowInNormalizer S))
        mu hmu).comp
          (okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)).subtype =
      mu.comp
        (okuyamaWajimaTargetQuotientProjection S K hK) := by
  letI :
      (okuyamaWajimaInternalFixedPoints
        K (S : Subgroup Γ)).Normal :=
    internalFixedPoints_normal K (S : Subgroup Γ)
  letI :
      (normalProductQuotientSylow
        (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
        (okuyamaWajimaSylowInNormalizer S) :
          Subgroup
            (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
              okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ))).Normal :=
    okuyamaWajimaQuotientSylow_normal S K hK hKS
  apply MonoidHom.ext
  intro x
  let x' :
      (normalProductQuotientSylow
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
          (okuyamaWajimaSylowInNormalizer S) :
        Subgroup
          (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
            okuyamaWajimaInternalFixedPoints
              K (S : Subgroup Γ))).comap
        (QuotientGroup.mk'
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))) :=
    ⟨(x : Subgroup.normalizer ((S : Subgroup Γ) : Set Γ)), by
      rw [comap_normalProductQuotientSylow]
      rw [coe_okuyamaWajimaSylowInNormalizer,
        ← internalNormalProduct_eq_fixedPoints_sup_sylow S K hK]
      exact x.property⟩
  have hx :=
    DFunLike.congr_fun
      (inflatedNormalQuotientSylowLinearExtension_spec
        (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
        (normalProductQuotientSylow
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
          (okuyamaWajimaSylowInNormalizer S))
        mu hmu)
      x'
  exact hx

/-- An invariant target quotient-Sylow parameter twists the fibre over the
internal normal product in its native subgroup coordinates. -/
def okuyamaWajimaTargetTwistOverEquiv
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (mu :
      letI :
          (okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ)).Normal :=
        internalFixedPoints_normal K (S : Subgroup Γ)
      (normalProductQuotientSylow
        (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
        (okuyamaWajimaSylowInNormalizer S) :
          Subgroup
            (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
              okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ))) →* ℂˣ)
    (hmu :
      letI :
          (okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ)).Normal :=
        internalFixedPoints_normal K (S : Subgroup Γ)
      letI :
          (normalProductQuotientSylow
            (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
            (okuyamaWajimaSylowInNormalizer S) :
              Subgroup
                (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
                  okuyamaWajimaInternalFixedPoints
                    K (S : Subgroup Γ))).Normal :=
        okuyamaWajimaQuotientSylow_normal S K hK hKS
      MonoidHom.IsConjugationInvariant
        (normalProductQuotientSylow
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
          (okuyamaWajimaSylowInNormalizer S) :
            Subgroup
              (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
                okuyamaWajimaInternalFixedPoints
                  K (S : Subgroup Γ)))
        mu)
    (alpha :
      IrreducibleCharacter
        (okuyamaWajimaInternalNormalProduct K (S : Subgroup Γ))) :
    IrreducibleCharactersOverAlong
        (okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ)).subtype alpha ≃
      IrreducibleCharactersOverAlong
        (okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ)).subtype
        (IrreducibleCharacter.twist
          (mu.comp
            (okuyamaWajimaTargetQuotientProjection S K hK))
          alpha) := by
  letI :
      (okuyamaWajimaInternalFixedPoints
        K (S : Subgroup Γ)).Normal :=
    internalFixedPoints_normal K (S : Subgroup Γ)
  letI :
      (normalProductQuotientSylow
        (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
        (okuyamaWajimaSylowInNormalizer S) :
          Subgroup
            (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
              okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ))).Normal :=
    okuyamaWajimaQuotientSylow_normal S K hK hKS
  exact
    twistOverEquiv_of_linearExtension
      (okuyamaWajimaInternalNormalProduct
        K (S : Subgroup Γ)).subtype
      alpha
      (mu.comp
        (okuyamaWajimaTargetQuotientProjection S K hK))
      (inflatedNormalQuotientSylowLinearExtension
        (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
        (normalProductQuotientSylow
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
          (okuyamaWajimaSylowInNormalizer S))
        mu hmu)
      (inflatedOkuyamaWajimaTargetLinearExtension_spec
        S K hK hKS mu hmu)

/-! ### Independent parameters and the per-parameter count -/

/-- The ordinary Okuyama--Wajima count for two independently chosen
invariant linear parameters.

There is no identification between `muSource` and `muTarget` in either the
statement or the proof.  Each parameter separately transports its fibre to
the automatically constructed determinant-normalized base extension, and
the semantic ordinary OW comparison identifies those two base fibre
cardinalities. -/
theorem okuyamaWajima_perInvariantLinearParameter
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
        S K hK hKS d θ)
    (muSource :
      (normalProductQuotientSylow K S :
        Subgroup (Γ ⧸ K)) →* ℂˣ)
    (hmuSource :
      letI :
          (normalProductQuotientSylow K S :
            Subgroup (Γ ⧸ K)).Normal :=
        normalProductQuotientSylow_normal K S hKS
      MonoidHom.IsConjugationInvariant
        (normalProductQuotientSylow K S :
          Subgroup (Γ ⧸ K))
        muSource)
    (muTarget :
      letI :
          (okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ)).Normal :=
        internalFixedPoints_normal K (S : Subgroup Γ)
      (normalProductQuotientSylow
        (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
        (okuyamaWajimaSylowInNormalizer S) :
          Subgroup
            (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
              okuyamaWajimaInternalFixedPoints
                K (S : Subgroup Γ))) →* ℂˣ)
    (hmuTarget :
      letI :
          (okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ)).Normal :=
        internalFixedPoints_normal K (S : Subgroup Γ)
      letI :
          (normalProductQuotientSylow
            (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
            (okuyamaWajimaSylowInNormalizer S) :
              Subgroup
                (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
                  okuyamaWajimaInternalFixedPoints
                    K (S : Subgroup Γ))).Normal :=
        okuyamaWajimaQuotientSylow_normal S K hK hKS
      MonoidHom.IsConjugationInvariant
        (normalProductQuotientSylow
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
          (okuyamaWajimaSylowInNormalizer S) :
            Subgroup
              (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
                okuyamaWajimaInternalFixedPoints
                  K (S : Subgroup Γ)))
        muTarget) :
    let c :=
      okuyamaWajimaInvariantCanonicalBaseExtensionData
        S K hK hKS d θ hinvariant
    Nat.card
        (IrreducibleCharactersOverAlong
          (K ⊔ (S : Subgroup Γ) : Subgroup Γ).subtype
          (IrreducibleCharacter.twist
            (muSource.comp
              (normalProductQuotientProjection K S))
            c.sourceExtension)) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)).subtype
          (IrreducibleCharacter.twist
            (muTarget.comp
              (okuyamaWajimaTargetQuotientProjection S K hK))
            c.targetExtension)) := by
  let c :=
    okuyamaWajimaInvariantCanonicalBaseExtensionData
      S K hK hKS d θ hinvariant
  have hbase :
      Nat.card
          (IrreducibleCharactersOverAlong
            (K ⊔ (S : Subgroup Γ) : Subgroup Γ).subtype
            c.sourceExtension) =
        Nat.card
          (IrreducibleCharactersOverAlong
            (okuyamaWajimaInternalNormalProduct
              K (S : Subgroup Γ)).subtype
            c.targetExtension) :=
    by
      simpa only [c] using
        (natCard_over_invariantCanonicalExtension_eq_normalizer
          S K hK hKS d θ hinvariant how)
  dsimp only
  calc
    Nat.card
        (IrreducibleCharactersOverAlong
          (K ⊔ (S : Subgroup Γ) : Subgroup Γ).subtype
          (IrreducibleCharacter.twist
            (muSource.comp
              (normalProductQuotientProjection K S))
            c.sourceExtension)) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (K ⊔ (S : Subgroup Γ) : Subgroup Γ).subtype
          c.sourceExtension) :=
      (Nat.card_congr
        (twistOverEquiv_of_normalProductQuotientSylowParameter
          K S hKS muSource hmuSource c.sourceExtension)).symm
    _ =
      Nat.card
        (IrreducibleCharactersOverAlong
          (okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)).subtype
          c.targetExtension) :=
      hbase
    _ =
      Nat.card
        (IrreducibleCharactersOverAlong
          (okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)).subtype
          (IrreducibleCharacter.twist
            (muTarget.comp
              (okuyamaWajimaTargetQuotientProjection S K hK))
            c.targetExtension)) :=
      Nat.card_congr
        (okuyamaWajimaTargetTwistOverEquiv
          S K hK hKS muTarget hmuTarget c.targetExtension)

/-! ### The exact remaining Gallagher-coordinate seam -/

/-- Two explicit source and target characters have independent invariant
Gallagher coordinates when each is a linear quotient-Sylow twist of its
own automatic canonical base extension.

This proposition deliberately asks for no comparison between the two
parameters.  In a concrete inertia-group application, proving this
proposition is the narrow remaining extraction step from the two
Gallagher decompositions. -/
def OkuyamaWajimaIndependentGallagherParameterCoordinates
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (hinvariant : ∀ g : Γ, g • θ.1.1 = θ.1.1)
    (alpha :
      IrreducibleCharacter
        (K ⊔ (S : Subgroup Γ) : Subgroup Γ))
    (beta :
      IrreducibleCharacter
        (okuyamaWajimaInternalNormalProduct K (S : Subgroup Γ))) :
    Prop :=
  let c :=
    okuyamaWajimaInvariantCanonicalBaseExtensionData
      S K hK hKS d θ hinvariant
  ∃ (muSource :
      (normalProductQuotientSylow K S :
        Subgroup (Γ ⧸ K)) →* ℂˣ),
    (letI :
        (normalProductQuotientSylow K S :
          Subgroup (Γ ⧸ K)).Normal :=
      normalProductQuotientSylow_normal K S hKS
    MonoidHom.IsConjugationInvariant
      (normalProductQuotientSylow K S :
        Subgroup (Γ ⧸ K))
      muSource) ∧
    alpha =
      IrreducibleCharacter.twist
        (muSource.comp
          (normalProductQuotientProjection K S))
        c.sourceExtension ∧
    ∃ (muTarget :
        letI :
            (okuyamaWajimaInternalFixedPoints
              K (S : Subgroup Γ)).Normal :=
          internalFixedPoints_normal K (S : Subgroup Γ)
        (normalProductQuotientSylow
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
          (okuyamaWajimaSylowInNormalizer S) :
            Subgroup
              (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
                okuyamaWajimaInternalFixedPoints
                  K (S : Subgroup Γ))) →* ℂˣ),
      (letI :
          (okuyamaWajimaInternalFixedPoints
            K (S : Subgroup Γ)).Normal :=
        internalFixedPoints_normal K (S : Subgroup Γ)
      letI :
          (normalProductQuotientSylow
            (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
            (okuyamaWajimaSylowInNormalizer S) :
              Subgroup
                (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
                  okuyamaWajimaInternalFixedPoints
                    K (S : Subgroup Γ))).Normal :=
        okuyamaWajimaQuotientSylow_normal S K hK hKS
      MonoidHom.IsConjugationInvariant
        (normalProductQuotientSylow
          (okuyamaWajimaInternalFixedPoints K (S : Subgroup Γ))
          (okuyamaWajimaSylowInNormalizer S) :
            Subgroup
              (Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⧸
                okuyamaWajimaInternalFixedPoints
                  K (S : Subgroup Γ)))
        muTarget) ∧
      beta =
        IrreducibleCharacter.twist
          (muTarget.comp
            (okuyamaWajimaTargetQuotientProjection S K hK))
          c.targetExtension

/-- Explicit-character adapter for the per-parameter theorem.  Once the
two independent Gallagher coordinates are extracted, the ordinary
lying-over fibre cardinalities are equal. -/
theorem natCard_over_eq_of_independentGallagherParameterCoordinates
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
        S K hK hKS d θ)
    (alpha :
      IrreducibleCharacter
        (K ⊔ (S : Subgroup Γ) : Subgroup Γ))
    (beta :
      IrreducibleCharacter
        (okuyamaWajimaInternalNormalProduct K (S : Subgroup Γ)))
    (hparameters :
      OkuyamaWajimaIndependentGallagherParameterCoordinates
        S K hK hKS d θ hinvariant alpha beta) :
    Nat.card
        (IrreducibleCharactersOverAlong
          (K ⊔ (S : Subgroup Γ) : Subgroup Γ).subtype alpha) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (okuyamaWajimaInternalNormalProduct
            K (S : Subgroup Γ)).subtype beta) := by
  rcases hparameters with
    ⟨muSource, hmuSource, halpha,
      muTarget, hmuTarget, hbeta⟩
  rw [halpha, hbeta]
  exact
    okuyamaWajima_perInvariantLinearParameter
      S K hK hKS d θ hinvariant how
      muSource hmuSource muTarget hmuTarget

end McKayConjecture
