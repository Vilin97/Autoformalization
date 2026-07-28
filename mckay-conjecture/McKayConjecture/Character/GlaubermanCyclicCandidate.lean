/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanTwistedTrace

/-!
# The canonical cyclic Glauberman trace

Let `H ◁ E`, let `gH` generate `E/H`, and let `χ ∈ Irr(H)` be fixed by
conjugation by `g`.  Schur normalization constructs an actual
intertwining unit `P`, not merely a projective one.  This file packages
that proved construction and the resulting class function

`c ↦ trace(P ρ(c))` on `C_H(g)`.

The same data gives an irreducible extension `χ̃ ∈ Irr(E)`, and the
twisted trace is exactly `c ↦ χ̃(gc)`.  This normalization still has a
root-of-unity scalar ambiguity (already visible when `H` is trivial).
`CyclicDeterminantNormalization.lean` removes that ambiguity before the
signed-irreducibility theorem is applied.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace RepresentationTheory

universe u

variable {E : Type u} [Group E] [Finite E]
variable (H : Subgroup E) [H.Normal]
variable (χ : IrreducibleCharacter H) (g : E)

/-- The normalized conjugation unit and both of its defining
identities, constructed from invariance of `χ`. -/
structure NormalizedCyclicIntertwinerData
    (hχ : IrreducibleCharacter.IsInvariantUnder H χ g) where
  /-- The normalized intertwining unit. -/
  unit : (Module.End ℂ χ.realization)ˣ
  /-- It intertwines the conjugation action of `g`. -/
  intertwines :
    ∀ h : H,
      unit *
          (Representation.asGroupHom
            χ.realization.ρ) h =
        (Representation.asGroupHom
          χ.realization.ρ)
          (ClassFunction.conjByMulEquiv
            (K := E) (H := H) g h) * unit
  /-- Integral powers agree with the representation whenever the
  corresponding power of `g` lies in `H`. -/
  normalized :
    ∀ (t : ℤ) (ht : g ^ t ∈ H),
      unit ^ t =
        (Representation.asGroupHom
          χ.realization.ρ)
          ⟨g ^ t, ht⟩

/-- Schur normalization supplies the cyclic intertwiner data for every
invariant irreducible character. -/
def normalizedCyclicIntertwinerData
    (hχ : IrreducibleCharacter.IsInvariantUnder H χ g) :
    NormalizedCyclicIntertwinerData H χ g hχ := by
  letI : Representation.IsIrreducible χ.realization.ρ :=
    CliffordRestriction.isIrreducible_of_simple
      χ.realization
  have hexists :=
    exists_normalized_conjugation_unit_of_nonempty_equiv
      χ.realization.ρ g
      (IrreducibleCharacter.realization_nonempty_equiv_conjRep
        H χ g hχ)
  exact
    ⟨Classical.choose hexists,
      (Classical.choose_spec hexists).1,
      (Classical.choose_spec hexists).2⟩

/-- The normalized cyclic extension representation attached to the
chosen Schur-normalized intertwiner. -/
def normalizedCyclicExtension
    (hgen : ∀ k : E, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    (hχ : IrreducibleCharacter.IsInvariantUnder H χ g) :
    Representation ℂ E χ.realization :=
  let d := normalizedCyclicIntertwinerData H χ g hχ
  cyclicExtension χ.realization.ρ g d.unit
    d.intertwines d.normalized hgen

/-- The normalized cyclic extension restricts literally to the chosen
realization of `χ`. -/
theorem normalizedCyclicExtension_comp_subtype
    (hgen : ∀ k : E, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    (hχ : IrreducibleCharacter.IsInvariantUnder H χ g) :
    (normalizedCyclicExtension H χ g hgen hχ).comp
        H.subtype =
      χ.realization.ρ := by
  exact cyclicExtension_comp_subtype
    (normalizedCyclicIntertwinerData H χ g hχ).intertwines
    (normalizedCyclicIntertwinerData H χ g hχ).normalized
    hgen

/-- The normalized cyclic extension remains irreducible. -/
theorem normalizedCyclicExtension_isIrreducible
    (hgen : ∀ k : E, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    (hχ : IrreducibleCharacter.IsInvariantUnder H χ g) :
    Representation.IsIrreducible
      (normalizedCyclicExtension H χ g hgen hχ) := by
  letI : Representation.IsIrreducible χ.realization.ρ :=
    CliffordRestriction.isIrreducible_of_simple
      χ.realization
  exact isIrreducible_cyclicExtension
    (normalizedCyclicIntertwinerData H χ g hχ).intertwines
    (normalizedCyclicIntertwinerData H χ g hχ).normalized
    hgen

/-- The irreducible character afforded by the normalized cyclic
extension. -/
def normalizedCyclicExtensionCharacter
    (hgen : ∀ k : E, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    (hχ : IrreducibleCharacter.IsInvariantUnder H χ g) :
    IrreducibleCharacter E := by
  letI : Representation.IsIrreducible
      (normalizedCyclicExtension H χ g hgen hχ) :=
    normalizedCyclicExtension_isIrreducible
      H χ g hgen hχ
  letI : Simple
      (FDRep.of
        (normalizedCyclicExtension H χ g hgen hχ)) :=
    simple_fdRep_of_isIrreducible
      (normalizedCyclicExtension H χ g hgen hχ)
  exact
    IrreducibleCharacter.ofSimple
      (FDRep.of
        (normalizedCyclicExtension H χ g hgen hχ))

/-- The normalized cyclic character really extends `χ`. -/
theorem normalizedCyclicExtensionCharacter_isExtension
    (hgen : ∀ k : E, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    (hχ : IrreducibleCharacter.IsInvariantUnder H χ g) :
    IrreducibleCharacter.IsExtensionAlong H.subtype χ
      (normalizedCyclicExtensionCharacter
        H χ g hgen hχ) := by
  intro h
  change
    LinearMap.trace ℂ χ.realization
        (normalizedCyclicExtension H χ g hgen hχ
          (H.subtype h)) =
      χ.values h
  rw [show
    normalizedCyclicExtension H χ g hgen hχ
        (H.subtype h) =
      χ.realization.ρ h by
        exact DFunLike.congr_fun
          (normalizedCyclicExtension_comp_subtype
            H χ g hgen hχ) h]
  exact congrFun χ.realization_character h

/-- The concrete twisted trace attached to the normalized cyclic
extension. -/
def cyclicGlaubermanTrace
    (hgen : ∀ k : E, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    (hχ : IrreducibleCharacter.IsInvariantUnder H χ g) :
    McKayConjecture.ClassFunction
      (cyclicFixedPoints H g) :=
  let d := normalizedCyclicIntertwinerData H χ g hχ
  cyclicTwistedTraceClassFunction
    d.intertwines d.normalized hgen

/-- The canonical cyclic trace is the normalized twisted trace
`trace(Pρ(c))`. -/
@[simp]
theorem cyclicGlaubermanTrace_apply
    (hgen : ∀ k : E, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    (hχ : IrreducibleCharacter.IsInvariantUnder H χ g)
    (c : cyclicFixedPoints H g) :
    cyclicGlaubermanTrace H χ g hgen hχ c =
      LinearMap.trace ℂ χ.realization
        (((normalizedCyclicIntertwinerData
            H χ g hχ).unit :
              Module.End ℂ χ.realization) *
          χ.realization.ρ
            (cyclicFixedPointsInclusion H g c)) :=
  by
    simpa only [cyclicGlaubermanTrace] using
      cyclicTwistedTraceClassFunction_apply
        (normalizedCyclicIntertwinerData
          H χ g hχ).intertwines
        (normalizedCyclicIntertwinerData
          H χ g hχ).normalized
        hgen c

/-- Equivalently, the canonical cyclic trace is the value of the
normalized irreducible extension on the coset `g C_H(g)`. -/
@[simp]
theorem cyclicGlaubermanTrace_eq_extensionCharacter
    (hgen : ∀ k : E, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    (hχ : IrreducibleCharacter.IsInvariantUnder H χ g)
    (c : cyclicFixedPoints H g) :
    cyclicGlaubermanTrace H χ g hgen hχ c =
      (normalizedCyclicExtensionCharacter
        H χ g hgen hχ).values
          (g * (c : E)) :=
  by
    simp [
      cyclicGlaubermanTrace,
      cyclicTwistedTraceClassFunction,
      normalizedCyclicExtensionCharacter,
      normalizedCyclicExtension]

end RepresentationTheory
end McKayConjecture
