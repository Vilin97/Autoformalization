/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionConjugation
import McKayConjecture.Character.InnerAutomorphism
import McKayConjecture.Character.OkuyamaWajimaFullFixedCoordinates

/-!
# Source-character transport in the full-fixed Okuyama--Wajima branch

The normal subgroup used by Isaacs 13.29 is the internal copy of `K` in
`U K`.  This file identifies it with the ambient `K`, transports the
invariant source character, and records that restriction of an ambient
character is automatically invariant under conjugation by `P`.
-/

noncomputable section

namespace McKayConjecture
namespace OkuyamaWajimaFullFixedSourceTransport

variable {A : Type} [Group A] [Finite A]
variable (P K U : Subgroup A) [K.Normal]

/-- The internal copy of `K` in `U K` is canonically the ambient `K`. -/
def sourceNormalEquivKernel :
    OkuyamaWajimaFullFixedCoordinates.sourceNormal K U ≃* K :=
  Subgroup.subgroupOfEquivOfLe le_sup_right

@[simp]
theorem sourceNormalEquivKernel_apply_coe
    (x : OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) :
    ((sourceNormalEquivKernel K U x : K) : A) =
      (((x :
        OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) :
          (U ⊔ K : Subgroup A)) : A) :=
  rfl

/-- Extension from the internal copy of `K` is exactly extension from the
ambient `K` along its inclusion in `U K`. -/
theorem isExtensionAlong_sourceNormalEquiv_iff
    (theta : IrreducibleCharacter K)
    (chi : IrreducibleCharacter (U ⊔ K : Subgroup A)) :
    IrreducibleCharacter.IsExtensionAlong
        (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U).subtype
        (theta.comap (sourceNormalEquivKernel K U))
        chi ↔
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion
          (show K ≤ U ⊔ K from le_sup_right))
        theta chi := by
  constructor
  · intro h k
    let k' := (sourceNormalEquivKernel K U).symm k
    calc
      chi.values
          (Subgroup.inclusion
            (show K ≤ U ⊔ K from le_sup_right) k) =
          chi.values
            ((OkuyamaWajimaFullFixedCoordinates.sourceNormal K U).subtype
              k') := by
            congr 1
      _ = (theta.comap
            (sourceNormalEquivKernel K U)).values k' :=
        h k'
      _ = theta.values k := by
        simp only [IrreducibleCharacter.comap_values,
          MulEquiv.apply_symm_apply, k']
  · intro h k
    calc
      chi.values
          ((OkuyamaWajimaFullFixedCoordinates.sourceNormal K U).subtype
            k) =
          chi.values
            (Subgroup.inclusion
              (show K ≤ U ⊔ K from le_sup_right)
              (sourceNormalEquivKernel K U k)) := by
            congr 1
      _ = theta.values (sourceNormalEquivKernel K U k) :=
        h (sourceNormalEquivKernel K U k)
      _ = (theta.comap
            (sourceNormalEquivKernel K U)).values k := by
        rfl

/-- The original `P`-invariant character of `K`, transported to the
internal normal subgroup used by Isaacs 13.29. -/
def internalInvariantSourceCharacter
    {p : ℕ} [Fact p.Prime]
    (theta :
      PInvariantPPrimeIrreducibleCharacter K P p) :
    letI :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        P K U
    ActionInvariantPPrimeIrreducibleCharacter
      P
      (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)
      p := by
  letI :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      P K U
  letI : MulDistribMulAction P K :=
    subgroupConjugationMulDistribMulAction K P
  let e := sourceNormalEquivKernel K U
  refine
    ⟨IrreducibleCharacter.pPrimeComapEquiv p e theta.1, ?_⟩
  intro s k
  change
    theta.1.1.values (e (s • k)) =
      theta.1.1.values (e k)
  have htheta :=
    (pInvariantCharacterEquivActionInvariant K P theta).2
      s (e k)
  exact htheta

@[simp]
theorem internalInvariantSourceCharacter_coe
    {p : ℕ} [Fact p.Prime]
    (theta :
      PInvariantPPrimeIrreducibleCharacter K P p) :
    letI :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        P K U
    (internalInvariantSourceCharacter
      P K U theta).1.1 =
      theta.1.1.comap (sourceNormalEquivKernel K U) := by
  letI :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      P K U
  rfl

/-- A character of `U K` obtained by restricting an ambient character is
fixed by the conjugation action of `P`. -/
theorem sourceExtension_values_invariant_of_ambientExtension
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A))
    (sourceExtension :
      IrreducibleCharacter (U ⊔ K : Subgroup A))
    (ambientExtension : IrreducibleCharacter A)
    (hambient :
      IrreducibleCharacter.IsExtensionAlong
        (U ⊔ K : Subgroup A).subtype
        sourceExtension ambientExtension)
    (s : P) (g : (U ⊔ K : Subgroup A)) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        P (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            P K U hcentral)
    sourceExtension.values (s • g) =
      sourceExtension.values g := by
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      P (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          P K U hcentral)
  calc
    sourceExtension.values (s • g) =
        ambientExtension.values
          (((s • g : (U ⊔ K : Subgroup A))) : A) :=
      (hambient (s • g)).symm
    _ = ambientExtension.values (g : A) := by
      have hconj :
          IsConj (g : A)
            (((s • g : (U ⊔ K : Subgroup A))) : A) := by
        rw [isConj_iff]
        exact ⟨(s : A), rfl⟩
      exact
        (ambientExtension.values_eq_of_isConj hconj).symm
    _ = sourceExtension.values g :=
      hambient g

end OkuyamaWajimaFullFixedSourceTransport
end McKayConjecture
