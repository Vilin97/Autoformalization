/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerComponentCorrespondenceEquivariance

/-!
# Pointwise values under layer-coordinate transport

The existing coordinate equivariance theorems identify whole dependent
families of prime-to-`p` characters.  This file records their pointwise
value consequences for both the component characters and their matched
intermediate-subgroup characters.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}
variable {D : LayerSylowCoordinateData G p Q}

namespace LayerComponentLocalData

/-- A layer-coordinate character evaluates on a transported component
element as the original coordinate character evaluates before transport. -/
theorem layerCoordinatePPrimeFamily_values_componentConjugation
    (g : G)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (hgθ : g • θ = θ)
    (K : ComponentIndex G)
    (x : K.1) :
    (layerCoordinatePPrimeFamily θ
      (componentConjugationPermutation G g⁻¹ K)).1.values
        (componentConjugationEquiv G g⁻¹ K x) =
      (layerCoordinatePPrimeFamily θ K).1.values x := by
  have hfamily :=
    congrFun
      (layerPPrimeCoordinateFamily_ambient_smul
        (G := G) (p := p) g θ)
      K
  rw [hgθ,
    IrreducibleCharacter.dependentProductPPrimeEquiv_apply]
    at hfamily
  have hvalues :=
    congrArg
      (fun χ : PPrimeIrreducibleCharacter K.1 p ↦
        χ.1.values x)
      hfamily
  change
    (layerCoordinatePPrimeFamily θ K).1.values x =
      (layerCoordinatePPrimeFamily θ
        (componentConjugationPermutation G g⁻¹ K)).1.values
          (componentConjugationEquiv G g⁻¹ K x)
    at hvalues
  exact hvalues.symm

/-- Index-equality form of
`layerCoordinatePPrimeFamily_values_componentConjugation`, convenient when
the transported coordinate has a separately chosen name. -/
theorem layerCoordinatePPrimeFamily_values_of_index_eq
    (g : G)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (hgθ : g • θ = θ)
    (K L : ComponentIndex G)
    (hKL :
      componentConjugationPermutation G g⁻¹ K = L)
    (x : K.1)
    (y : L.1)
    (hy :
      (y : G) = g⁻¹ * (x : G) * g) :
    (layerCoordinatePPrimeFamily θ L).1.values y =
      (layerCoordinatePPrimeFamily θ K).1.values x := by
  subst L
  have hvalue :=
    layerCoordinatePPrimeFamily_values_componentConjugation
      g θ hgθ K x
  have htransported :
      componentConjugationEquiv G g⁻¹ K x = y := by
    apply Subtype.ext
    change g⁻¹ * (x : G) * (g⁻¹)⁻¹ = (y : G)
    simpa using hy.symm
  rw [htransported] at hvalue
  exact hvalue

/-- A matched intermediate-coordinate character evaluates on a restricted
transported element as the original matched character evaluates before
transport. -/
theorem localCoordinatePPrimeFamily_values_relativeConjugation
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (hcoordinate :
      d.IsCoordinateCorrespondenceEquivariant hM)
    (a : LayerSylowAmbientNormalizer G Q)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (haθ :
      letI := ambientNormalizerLayerPPrimeCharacterMulAction
        (G := G) (p := p) (Q := Q)
      a • θ = θ)
    (K : ComponentIndex G)
    (x : d.intermediate K) :
    (d.localCoordinatePPrimeFamily θ
      (componentConjugationPermutation G ((a⁻¹ : _) : G) K)).1.values
        (d.relativeIntermediateConjugationEquiv hM a⁻¹ K x) =
      (d.localCoordinatePPrimeFamily θ K).1.values x := by
  letI := ambientNormalizerLayerPPrimeCharacterMulAction
    (G := G) (p := p) (Q := Q)
  have hfamily :=
    congrFun
      (d.coordinateCorrespondenceFamily_smul
        hM hcoordinate a θ)
      K
  rw [haθ,
    IrreducibleCharacter.dependentProductPPrimeEquiv_apply]
    at hfamily
  have hvalues :=
    congrArg
      (fun χ : PPrimeIrreducibleCharacter
          (d.intermediate K) p ↦
        χ.1.values x)
      hfamily
  change
    (d.localCoordinatePPrimeFamily θ K).1.values x =
      (d.localCoordinatePPrimeFamily θ
        (componentConjugationPermutation G
          ((a⁻¹ : LayerSylowAmbientNormalizer G Q) : G) K)).1.values
          (d.relativeIntermediateConjugationEquiv hM a⁻¹ K x)
    at hvalues
  exact hvalues.symm

/-- Index-equality form of
`localCoordinatePPrimeFamily_values_relativeConjugation`, with the
transported intermediate element characterized by its ambient value. -/
theorem localCoordinatePPrimeFamily_values_of_index_eq
    (d : LayerComponentLocalData D)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) d.intermediate)
    (hcoordinate :
      d.IsCoordinateCorrespondenceEquivariant hM)
    (a : LayerSylowAmbientNormalizer G Q)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (haθ :
      letI := ambientNormalizerLayerPPrimeCharacterMulAction
        (G := G) (p := p) (Q := Q)
      a • θ = θ)
    (K L : ComponentIndex G)
    (hKL :
      componentConjugationPermutation G ((a⁻¹ : _) : G) K = L)
    (x : d.intermediate K)
    (y : d.intermediate L)
    (hy :
      (((y : d.intermediate L) : L.1) : G) =
        ((a⁻¹ : LayerSylowAmbientNormalizer G Q) : G) *
          (((x : d.intermediate K) : K.1) : G) *
        (a : G)) :
    (d.localCoordinatePPrimeFamily θ L).1.values y =
      (d.localCoordinatePPrimeFamily θ K).1.values x := by
  subst L
  have hvalue :=
    d.localCoordinatePPrimeFamily_values_relativeConjugation
      hM hcoordinate a θ haθ K x
  have htransported :
      d.relativeIntermediateConjugationEquiv hM a⁻¹ K x = y := by
    apply Subtype.ext
    apply Subtype.ext
    change
      ((a⁻¹ : LayerSylowAmbientNormalizer G Q) : G) *
          (((x : d.intermediate K) : K.1) : G) *
        ((a⁻¹ : LayerSylowAmbientNormalizer G Q) : G)⁻¹ =
      (((y : d.intermediate
        (componentConjugationPermutation G
          ((a⁻¹ : LayerSylowAmbientNormalizer G Q) : G) K)) :
        (componentConjugationPermutation G
          ((a⁻¹ : LayerSylowAmbientNormalizer G Q) : G) K).1) : G)
    simpa using hy.symm
  rw [htransported] at hvalue
  exact hvalue

end LayerComponentLocalData
end InductiveMcKay
end McKayConjecture
