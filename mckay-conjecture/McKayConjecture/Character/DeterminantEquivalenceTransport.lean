/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DirectProductLinearExtension
import McKayConjecture.Character.OverAlongTransport
import McKayConjecture.Character.PPrimeDeterminantRoot
import McKayConjecture.GroupTheory.InvariantSubgroupAutomorphism

/-!
# Transport of determinant parameters along group equivalences

The determinant of an irreducible character is independent of the chosen
realization and is natural under pullback along a group equivalence.  The
same is true of the coprime determinant-root normalization when the source
homomorphisms form a commuting equivalence square.

The final statements specialize this square to subgroup inclusions and to an
automorphism preserving a subgroup.  This is the form used to transport the
Sylow-factor parameter in determinant-normalized local extensions.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace IrreducibleCharacter

universe u₁ u₂ u₃ u₄

variable {G : Type u₁} {G' : Type u₂}
variable [Group G] [Group G'] [Finite G']

/-- The determinant character commutes with pullback along a group
equivalence. -/
theorem determinantParameter_comap
    (e : G' ≃* G) (χ : IrreducibleCharacter G) :
    determinantParameter (χ.comap e) =
      (determinantParameter χ).comp e.toMonoidHom := by
  apply MonoidHom.ext
  intro g
  let i := comapRealizationIso e χ
  have hdet :
      LinearMap.det
          ((χ.comap e).realization.ρ g :
            (χ.comap e).realization →ₗ[ℂ]
              (χ.comap e).realization) =
        LinearMap.det
          ((FDRep.res e.toMonoidHom χ.realization).ρ g :
            FDRep.res e.toMonoidHom χ.realization →ₗ[ℂ]
              FDRep.res e.toMonoidHom χ.realization) := by
    rw [FDRep.Iso.conj_ρ i g, LinearEquiv.conj_apply,
      LinearMap.comp_assoc, LinearMap.det_conj]
  apply Units.ext
  rw [determinantParameter_eq_det,
    MonoidHom.comp_apply, determinantParameter_eq_det]
  change
    LinearMap.det
        ((χ.comap e).realization.ρ g :
          (χ.comap e).realization →ₗ[ℂ]
            (χ.comap e).realization) =
      LinearMap.det
        (χ.realization.ρ (e g) :
          χ.realization →ₗ[ℂ] χ.realization)
  change
    LinearMap.det
        ((χ.comap e).realization.ρ g :
          (χ.comap e).realization →ₗ[ℂ]
            (χ.comap e).realization) =
      LinearMap.det
        (χ.realization.ρ (e g) :
          χ.realization →ₗ[ℂ] χ.realization) at hdet
  exact hdet

/-- Prime-to-`p` packaging does not change determinant transport. -/
theorem determinantParameter_pPrimeComapEquiv
    (p : ℕ) (e : G' ≃* G)
    (χ : PPrimeIrreducibleCharacter G p) :
    determinantParameter
        (pPrimeComapEquiv p e χ).1 =
      (determinantParameter χ.1).comp e.toMonoidHom :=
  determinantParameter_comap e χ.1

variable {H : Type u₃} {H' : Type u₄}
variable [Group H] [Group H']

/-- Naturality of the determinant-root parameter in a commuting square.

The equivalences point from the new groups to the old groups, in the same
direction as `IrreducibleCharacter.comap`. -/
theorem determinantRootParameter_comap_equiv
    (eG : G' ≃* G) (eH : H' ≃* H)
    (f : H →* G) (f' : H' →* G')
    (hcomm :
      eG.toMonoidHom.comp f' =
        f.comp eH.toMonoidHom)
    (χ : IrreducibleCharacter G)
    (hcoprime : (Nat.card H).Coprime χ.degree) :
    determinantRootParameter (χ.comap eG) f'
        (by
          simpa only [comap_degree,
            Nat.card_congr eH.toEquiv] using hcoprime) =
      (determinantRootParameter χ f hcoprime).comp
        eH.toMonoidHom := by
  apply MonoidHom.ext
  intro h
  have hcard :
      Nat.card H' = Nat.card H :=
    Nat.card_congr eH.toEquiv
  have hdet :=
    DFunLike.congr_fun
      (determinantParameter_comap eG χ) (f' h)
  have hpoint :=
    DFunLike.congr_fun hcomm h
  change
    (determinantParameter (χ.comap eG) (f' h)) ^
        (Nat.card H').gcdB (χ.comap eG).degree =
      (determinantParameter χ (f (eH h))) ^
        (Nat.card H).gcdB χ.degree
  rw [comap_degree, hcard, hdet]
  exact congrArg
    (fun x : G ↦
      (determinantParameter χ x) ^
        (Nat.card H).gcdB χ.degree)
    hpoint

/-- Determinant-root transport for prime-to-`p` characters. -/
theorem determinantRootParameter_pPrimeComapEquiv
    (p : ℕ)
    (eG : G' ≃* G) (eH : H' ≃* H)
    (f : H →* G) (f' : H' →* G')
    (hcomm :
      eG.toMonoidHom.comp f' =
        f.comp eH.toMonoidHom)
    (χ : PPrimeIrreducibleCharacter G p)
    (hcoprime : (Nat.card H).Coprime χ.1.degree) :
    determinantRootParameter
        (pPrimeComapEquiv p eG χ).1 f'
        (by
          simpa only [pPrimeComapEquiv_degree,
            Nat.card_congr eH.toEquiv] using hcoprime) =
      (determinantRootParameter χ.1 f hcoprime).comp
        eH.toMonoidHom :=
  determinantRootParameter_comap_equiv
    eG eH f f' hcomm χ.1 hcoprime

section Subgroup

variable (K : Subgroup G) (K' : Subgroup G')

/-- Restriction-square form of determinant-root transport. -/
theorem determinantRootParameter_comap_subgroupEquiv
    (eG : G' ≃* G) (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom)
    (χ : IrreducibleCharacter G)
    (hcoprime : (Nat.card K).Coprime χ.degree) :
    determinantRootParameter (χ.comap eG) K'.subtype
        (by
          simpa only [comap_degree,
            Nat.card_congr eK.toEquiv] using hcoprime) =
      (determinantRootParameter χ K.subtype hcoprime).comp
        eK.toMonoidHom :=
  determinantRootParameter_comap_equiv
    eG eK K.subtype K'.subtype hcomm χ hcoprime

/-- Prime-to-`p` restriction-square form of determinant-root transport. -/
theorem determinantRootParameter_pPrimeComap_subgroupEquiv
    (p : ℕ)
    (eG : G' ≃* G) (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom)
    (χ : PPrimeIrreducibleCharacter G p)
    (hcoprime : (Nat.card K).Coprime χ.1.degree) :
    determinantRootParameter
        (pPrimeComapEquiv p eG χ).1 K'.subtype
        (by
          simpa only [pPrimeComapEquiv_degree,
            Nat.card_congr eK.toEquiv] using hcoprime) =
      (determinantRootParameter χ.1 K.subtype hcoprime).comp
        eK.toMonoidHom :=
  determinantRootParameter_pPrimeComapEquiv
    p eG eK K.subtype K'.subtype hcomm χ hcoprime

end Subgroup

section InvariantSubgroup

variable {A : Type u₁} [Group A] [Finite A]

/-- If an automorphism preserves a subgroup, its pullback transports the
restricted determinant-root parameter along the restricted automorphism. -/
theorem determinantRootParameter_comap_invariantSubgroupAutomorphism
    (e : MulAut A) (K : Subgroup A)
    (hK : K.map e.toMonoidHom = K)
    (χ : IrreducibleCharacter A)
    (hcoprime : (Nat.card K).Coprime χ.degree) :
    determinantRootParameter (χ.comap e) K.subtype
        (by simpa only [comap_degree] using hcoprime) =
      (determinantRootParameter χ K.subtype hcoprime).comp
        (GroupTheory.invariantSubgroupAutomorphism
          e K hK).toMonoidHom :=
  determinantRootParameter_comap_subgroupEquiv K K
    e
    (GroupTheory.invariantSubgroupAutomorphism e K hK)
    (GroupTheory.invariantSubgroupAutomorphism_subtype_commutes
      e K hK)
    χ hcoprime

/-- Prime-to-`p` version for an automorphism preserving the restricted
subgroup. -/
theorem determinantRootParameter_pPrimeComap_invariantSubgroupAutomorphism
    (p : ℕ)
    (e : MulAut A) (K : Subgroup A)
    (hK : K.map e.toMonoidHom = K)
    (χ : PPrimeIrreducibleCharacter A p)
    (hcoprime : (Nat.card K).Coprime χ.1.degree) :
    determinantRootParameter
        (pPrimeComapEquiv p e χ).1 K.subtype
        (by
          simpa only [pPrimeComapEquiv_degree] using hcoprime) =
      (determinantRootParameter χ.1 K.subtype hcoprime).comp
        (GroupTheory.invariantSubgroupAutomorphism
          e K hK).toMonoidHom :=
  determinantRootParameter_pPrimeComap_subgroupEquiv K K
    p e
    (GroupTheory.invariantSubgroupAutomorphism e K hK)
    (GroupTheory.invariantSubgroupAutomorphism_subtype_commutes
      e K hK)
    χ hcoprime

end InvariantSubgroup

section DirectProduct

variable {A A' B B' : Type}
variable [Group A] [Group A'] [Group B] [Group B']

/-- Transport a character of the first direct factor by transporting its
canonical character on the first coordinate. -/
def directProductFirstFactorCharacterComap
    (eA : A' ≃* A)
    (χ :
      IrreducibleCharacter
        (directProductFirstFactor (G := A) (H := B))) :
    IrreducibleCharacter
      (directProductFirstFactor (G := A') (H := B')) :=
  ((χ.comap
      (directProductFirstFactorEquiv
        (G := A) (H := B)).symm).comap eA).comap
    (directProductFirstFactorEquiv
      (G := A') (H := B'))

/-- A direct-product linear extension commutes with simultaneous transport
of both factors. -/
theorem directProductFirstFactorLinearExtension_comap_prodCongr
    (eA : A' ≃* A) (eB : B' ≃* B)
    (χ :
      IrreducibleCharacter
        (directProductFirstFactor (G := A) (H := B)))
    (lam : B →* ℂˣ) :
    (directProductFirstFactorLinearExtension χ lam).comap
        (MulEquiv.prodCongr eA eB) =
      directProductFirstFactorLinearExtension
        (directProductFirstFactorCharacterComap
          (B' := B') eA χ)
        (lam.comp eB.toMonoidHom) := by
  apply IrreducibleCharacter.ext
  funext x
  rw [comap_values,
    directProductFirstFactorLinearExtension,
    directProductFirstFactorLinearExtension,
    externalTensor_values, comap_values, linear_values,
    externalTensor_values, comap_values, linear_values]
  simp [directProductFirstFactorCharacterComap,
    MulEquiv.prodCongr]

/-- A determinant-normalized direct-product extension is covariant when its
first-factor character, ambient character, and Sylow factor are transported
through commuting equivalence squares. -/
theorem determinantNormalizedDirectProductExtension_comap_prodCongr
    (eA : A' ≃* A) (eB : B' ≃* B)
    (eG : G' ≃* G)
    (f : B →* G) (f' : B' →* G')
    (hcomm :
      eG.toMonoidHom.comp f' =
        f.comp eB.toMonoidHom)
    (χ :
      IrreducibleCharacter
        (directProductFirstFactor (G := A) (H := B)))
    (ψ : IrreducibleCharacter G)
    (hcoprime : (Nat.card B).Coprime ψ.degree) :
    (directProductFirstFactorLinearExtension χ
        (determinantRootParameter ψ f hcoprime)).comap
          (MulEquiv.prodCongr eA eB) =
      directProductFirstFactorLinearExtension
        (directProductFirstFactorCharacterComap
          (B' := B') eA χ)
        (determinantRootParameter (ψ.comap eG) f'
          (by
            simpa only [comap_degree,
              Nat.card_congr eB.toEquiv] using hcoprime)) := by
  rw [directProductFirstFactorLinearExtension_comap_prodCongr,
    determinantRootParameter_comap_equiv
      eG eB f f' hcomm ψ hcoprime]

end DirectProduct

end IrreducibleCharacter
end McKayConjecture
