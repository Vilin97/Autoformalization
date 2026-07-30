/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InvariantLinearTwistOver
import McKayConjecture.GroupTheory.NormalProductSylowQuotient

/-!
# Linear twists on a normal product

Let `K` be normal in a finite group `G`, let `S` be a Sylow `p`-subgroup,
and suppose that `K ⊔ S` is normal.  Then the image of `S` in `G ⧸ K` is
a normal Sylow subgroup and the full preimage of that image is exactly
`K ⊔ S`.

This file specializes the invariant normal-quotient-Sylow twist construction
to those normal-product coordinates.  In particular, an invariant linear
parameter on the quotient Sylow pulls back along the canonical projection

`K ⊔ S → (KS) / K`,

and twisting by that parameter gives an explicit equivalence of ordinary
lying-over fibres on `K ⊔ S`.
-/

noncomputable section

namespace McKayConjecture

namespace GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- The chosen inflated extension of a quotient-Sylow parameter restricts
to its pullback along the normal-product quotient projection. -/
theorem inflatedNormalProductQuotientSylowLinearExtension_spec
    (K : Subgroup G) [K.Normal]
    (S : Sylow p G)
    (hKS : (K ⊔ (S : Subgroup G)).Normal)
    (mu :
      (normalProductQuotientSylow K S :
        Subgroup (G ⧸ K)) →* ℂˣ)
    (hmu :
      letI :
          (normalProductQuotientSylow K S :
            Subgroup (G ⧸ K)).Normal :=
        normalProductQuotientSylow_normal K S hKS
      MonoidHom.IsConjugationInvariant
        (normalProductQuotientSylow K S :
          Subgroup (G ⧸ K)) mu) :
    letI :
        (normalProductQuotientSylow K S :
          Subgroup (G ⧸ K)).Normal :=
      normalProductQuotientSylow_normal K S hKS
    (inflatedNormalQuotientSylowLinearExtension
        K (normalProductQuotientSylow K S) mu hmu).comp
          (K ⊔ (S : Subgroup G)).subtype =
      mu.comp (normalProductQuotientProjection K S) := by
  letI :
      (normalProductQuotientSylow K S :
        Subgroup (G ⧸ K)).Normal :=
    normalProductQuotientSylow_normal K S hKS
  apply MonoidHom.ext
  intro x
  let x' :
      (normalProductQuotientSylow K S :
          Subgroup (G ⧸ K)).comap
        (QuotientGroup.mk' K) :=
    ⟨(x : G), by
      rw [comap_normalProductQuotientSylow K S]
      exact x.property⟩
  have hx :=
    DFunLike.congr_fun
      (inflatedNormalQuotientSylowLinearExtension_spec
        K (normalProductQuotientSylow K S) mu hmu)
      x'
  change
    inflatedNormalQuotientSylowLinearExtension
        K (normalProductQuotientSylow K S) mu hmu (x : G) =
      mu (normalProductQuotientProjection K S x)
  change
    inflatedNormalQuotientSylowLinearExtension
        K (normalProductQuotientSylow K S) mu hmu (x : G) =
      mu
        (quotientSubgroupProjection
          K
          (normalProductQuotientSylow K S :
            Subgroup (G ⧸ K))
          x') at hx
  rw [hx]
  congr 1

end GroupTheory

namespace CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- An invariant linear parameter on the normal quotient Sylow gives the
normal-product fibre twist in the exact `K ⊔ S` coordinates. -/
def twistOverEquiv_of_normalProductQuotientSylowParameter
    (K : Subgroup G) [K.Normal]
    (S : Sylow p G)
    (hKS : (K ⊔ (S : Subgroup G)).Normal)
    (mu :
      (GroupTheory.normalProductQuotientSylow K S :
        Subgroup (G ⧸ K)) →* ℂˣ)
    (hmu :
      letI :
          (GroupTheory.normalProductQuotientSylow K S :
            Subgroup (G ⧸ K)).Normal :=
        GroupTheory.normalProductQuotientSylow_normal K S hKS
      MonoidHom.IsConjugationInvariant
        (GroupTheory.normalProductQuotientSylow K S :
          Subgroup (G ⧸ K)) mu)
    (alpha :
      IrreducibleCharacter
        (K ⊔ (S : Subgroup G) : Subgroup G)) :
    IrreducibleCharactersOverAlong
        (K ⊔ (S : Subgroup G)).subtype alpha ≃
      IrreducibleCharactersOverAlong
        (K ⊔ (S : Subgroup G)).subtype
        (IrreducibleCharacter.twist
          (mu.comp
            (GroupTheory.normalProductQuotientProjection K S))
          alpha) := by
  letI :
      (GroupTheory.normalProductQuotientSylow K S :
        Subgroup (G ⧸ K)).Normal :=
    GroupTheory.normalProductQuotientSylow_normal K S hKS
  exact
    twistOverEquiv_of_linearExtension
      (K ⊔ (S : Subgroup G)).subtype
      alpha
      (mu.comp
        (GroupTheory.normalProductQuotientProjection K S))
      (GroupTheory.inflatedNormalQuotientSylowLinearExtension
        K (GroupTheory.normalProductQuotientSylow K S) mu hmu)
      (GroupTheory.inflatedNormalProductQuotientSylowLinearExtension_spec
        K S hKS mu hmu)

end CliffordCorrespondence

end McKayConjecture
