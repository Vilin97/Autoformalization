/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Burnside
import McKayConjecture.Character.Construction
import McKayConjecture.Character.Restriction
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionRepresentation
import McKayConjecture.CharacterTriple.ProjectiveIrreducible

/-!
# Irreducible characters of factor-set central extensions

Stable submodules for a projective representation are exactly the invariant
submodules for its honest factor-set extension representation.  Consequently,
projective irreducibility gives an ordinary irreducible representation of the
extension.

For the finite root-of-unity factor set, this file packages that
representation as an `IrreducibleCharacter` and computes its restriction to
the canonical coefficient copy.
-/

noncomputable section

open CategoryTheory

universe u v w z

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K : Type u} {V : Type v} {G : Type w} {A : Type z}
variable [Field K] [AddCommGroup V] [Module K V]
variable [Group G] [CommGroup A]

/-- Rescaling chosen projective lifts does not change which submodules are
stable. -/
theorem rescale_isStable_iff
    (P : ProjectiveRepresentation K G V) (c : G → Kˣ)
    (S : Submodule K V) :
    (P.rescale c).IsStable S ↔ P.IsStable S := by
  constructor
  · intro hS g v hv
    have hscaled := hS g hv
    have hunscaled :=
      S.smul_mem (((c g)⁻¹ : Kˣ) : K) hscaled
    simpa only [rescale_operator, LinearEquiv.mul_apply,
      scalarLinearEquiv_apply, smul_smul, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ (c g).ne_zero, one_smul] using hunscaled
  · intro hS g v hv
    change (c g : K) • P.operator g v ∈ S
    exact S.smul_mem (c g : K) (hS g hv)

/-- Projective irreducibility is invariant under rescaling of the chosen
lifts. -/
theorem rescale_isIrreducible_iff
    (P : ProjectiveRepresentation K G V) (c : G → Kˣ) :
    (P.rescale c).IsIrreducible ↔ P.IsIrreducible := by
  constructor
  · intro hP
    refine ⟨hP.1, ?_⟩
    intro S hS
    exact hP.2 S ((P.rescale_isStable_iff c S).mpr hS)
  · intro hP
    refine ⟨hP.1, ?_⟩
    intro S hS
    exact hP.2 S ((P.rescale_isStable_iff c S).mp hS)

/-- A submodule is invariant under the honest central-extension
representation exactly when it is stable under the original projective
representation. -/
theorem centralExtensionRepresentation_invariant_iff_isStable
    (P : ProjectiveRepresentation K G V)
    (α : FactorSet G A) (hα : α.IsNormalized)
    (ι : A →* Kˣ)
    (hfactor : ∀ g h : G, ι (α g h) = P.factor g h)
    (S : Submodule K V) :
    (∀ (x : FactorSet.CentralExtensionGroup α hα) ⦃v : V⦄,
      v ∈ S →
        P.centralExtensionRepresentation α hα ι hfactor x v ∈ S) ↔
      P.IsStable S := by
  constructor
  · intro hS g v hv
    have hbase :=
      hS (FactorSet.CentralExtensionGroup.mk α hα g 1) hv
    simpa only [centralExtensionRepresentation_apply_vector,
      FactorSet.CentralExtensionGroup.coefficient_mk,
      FactorSet.CentralExtensionGroup.base_mk, map_one, Units.val_one,
      one_smul] using hbase
  · intro hS x v hv
    rw [centralExtensionRepresentation_apply_vector]
    exact
      S.smul_mem
        ((ι (FactorSet.CentralExtensionGroup.coefficient α hα x) : K))
        (hS (FactorSet.CentralExtensionGroup.base α hα x) hv)

/-- Projective irreducibility implies lattice irreducibility of the honest
central-extension representation. -/
theorem centralExtensionRepresentation_isIrreducible
    (P : ProjectiveRepresentation K G V)
    (α : FactorSet G A) (hα : α.IsNormalized)
    (ι : A →* Kˣ)
    (hfactor : ∀ g h : G, ι (α g h) = P.factor g h)
    (hP : P.IsIrreducible) :
    Representation.IsIrreducible
      (P.centralExtensionRepresentation α hα ι hfactor) := by
  let ρ :=
    P.centralExtensionRepresentation α hα ι hfactor
  letI : Nontrivial V := hP.nontrivial
  letI : Nontrivial (Subrepresentation ρ) :=
    ⟨⟨⊥, ⊤, fun h =>
      bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩⟩
  refine ⟨fun W ↦ ?_⟩
  have hstable : P.IsStable W.toSubmodule :=
    (P.centralExtensionRepresentation_invariant_iff_isStable
      α hα ι hfactor W.toSubmodule).mp
      (fun x v hv ↦ W.apply_mem_toSubmodule x hv)
  rcases hP.eq_bot_or_eq_top W.toSubmodule hstable with hbot | htop
  · left
    apply Subrepresentation.ext
    change W.toSubmodule = (⊥ : Submodule K V)
    exact hbot
  · right
    apply Subrepresentation.ext
    change W.toSubmodule = (⊤ : Submodule K V)
    exact htop

section FiniteFactorIrreducibility

variable [IsAlgClosed K] [Module.Finite K V] [Nontrivial V]

/-- Determinant normalization and identity normalization preserve
projective irreducibility. -/
theorem finiteFactorNormalize_isIrreducible_iff
    (P : ProjectiveRepresentation K G V) :
    P.finiteFactorNormalize.IsIrreducible ↔ P.IsIrreducible := by
  simp only [finiteFactorNormalize, determinantNormalize, normalize,
    rescale_isIrreducible_iff]

/-- Projective irreducibility gives irreducibility of the honest
root-of-unity central-extension representation. -/
theorem finiteFactorCentralExtensionRepresentation_isIrreducible
    (P : ProjectiveRepresentation K G V)
    (hP : P.IsIrreducible) :
    Representation.IsIrreducible
      P.finiteFactorCentralExtensionRepresentation :=
  P.finiteFactorNormalize.centralExtensionRepresentation_isIrreducible
    P.finiteFactorSet P.finiteFactorSet_isNormalized
    (rootsOfUnity (Module.finrank K V) K).subtype
    P.finiteFactorSet_coe
    (P.finiteFactorNormalize_isIrreducible_iff.mpr hP)

end FiniteFactorIrreducibility

section ComplexCharacter

variable {G : Type u} {V : Type}
variable [Group G]
variable [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]

/-- The finite-dimensional honest representation of the root-of-unity
central extension. -/
abbrev finiteFactorCentralExtensionFDRep
    (P : ProjectiveRepresentation ℂ G V) :
    FDRep ℂ P.FiniteFactorCentralExtensionGroup :=
  FDRep.of P.finiteFactorCentralExtensionRepresentation

/-- The honest finite-factor extension representation is categorically
simple when the original projective representation is irreducible. -/
theorem finiteFactorCentralExtensionFDRep_simple
    (P : ProjectiveRepresentation ℂ G V)
    (hP : P.IsIrreducible) :
    Simple P.finiteFactorCentralExtensionFDRep := by
  letI :
      Representation.IsIrreducible
        P.finiteFactorCentralExtensionRepresentation :=
    P.finiteFactorCentralExtensionRepresentation_isIrreducible hP
  exact FDRep.simple_of_representation_isIrreducible
    P.finiteFactorCentralExtensionRepresentation

/-- Restricting the finite-factor extension representation to its canonical
coefficient copy gives scalar matrices.  This is the corresponding character
formula. -/
theorem finiteFactorCentralExtensionFDRep_restrictCoefficient_character
    (P : ProjectiveRepresentation ℂ G V) :
    (FDRep.res
      (FactorSet.CentralExtensionGroup.coefficientEmbedding
        P.finiteFactorSet P.finiteFactorSet_isNormalized)
      P.finiteFactorCentralExtensionFDRep).character =
        fun a : rootsOfUnity (Module.finrank ℂ V) ℂ ↦
          ((a : ℂˣ) : ℂ) * (Module.finrank ℂ V : ℂ) := by
  funext a
  change
    LinearMap.trace ℂ V
        (P.finiteFactorCentralExtensionRepresentation
          (FactorSet.CentralExtensionGroup.coefficientEmbedding
            P.finiteFactorSet P.finiteFactorSet_isNormalized a)) =
      ((a : ℂˣ) : ℂ) * (Module.finrank ℂ V : ℂ)
  rw [finiteFactorCentralExtensionRepresentation,
    P.finiteFactorNormalize.centralExtensionRepresentation_apply_coefficientEmbedding
      P.finiteFactorSet P.finiteFactorSet_isNormalized
      (rootsOfUnity (Module.finrank ℂ V) ℂ).subtype
      P.finiteFactorSet_coe]
  have hscalar :
      ((scalarLinearEquiv ℂ V
          ((rootsOfUnity (Module.finrank ℂ V) ℂ).subtype a) :
            V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) =
        (((rootsOfUnity (Module.finrank ℂ V) ℂ).subtype a : ℂˣ) : ℂ) •
          (LinearMap.id : Module.End ℂ V) := by
    ext v
    simp
  rw [hscalar, map_smul, LinearMap.trace_id]
  rfl

/-- The irreducible character afforded by the finite factor-set central
extension representation. -/
def finiteFactorCentralExtensionCharacter
    (P : ProjectiveRepresentation ℂ G V)
    (hP : P.IsIrreducible) :
    IrreducibleCharacter P.FiniteFactorCentralExtensionGroup := by
  letI : Simple P.finiteFactorCentralExtensionFDRep :=
    P.finiteFactorCentralExtensionFDRep_simple hP
  exact IrreducibleCharacter.ofSimple
    P.finiteFactorCentralExtensionFDRep

@[simp]
theorem finiteFactorCentralExtensionCharacter_degree
    (P : ProjectiveRepresentation ℂ G V)
    (hP : P.IsIrreducible) :
    (P.finiteFactorCentralExtensionCharacter hP).degree =
      Module.finrank ℂ V := by
  letI : Simple P.finiteFactorCentralExtensionFDRep :=
    P.finiteFactorCentralExtensionFDRep_simple hP
  rfl

/-- On the coefficient copy, the extension character is the defining scalar
times its degree. -/
@[simp]
theorem finiteFactorCentralExtensionCharacter_values_coefficientEmbedding
    (P : ProjectiveRepresentation ℂ G V)
    (hP : P.IsIrreducible)
    (a : rootsOfUnity (Module.finrank ℂ V) ℂ) :
    (P.finiteFactorCentralExtensionCharacter hP).values
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          P.finiteFactorSet P.finiteFactorSet_isNormalized a) =
      ((a : ℂˣ) : ℂ) *
        (P.finiteFactorCentralExtensionCharacter hP).degree := by
  letI : Simple P.finiteFactorCentralExtensionFDRep :=
    P.finiteFactorCentralExtensionFDRep_simple hP
  change
    P.finiteFactorCentralExtensionFDRep.character
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          P.finiteFactorSet P.finiteFactorSet_isNormalized a) =
      ((a : ℂˣ) : ℂ) * Module.finrank ℂ V
  have hrestriction :=
    congrFun
      (P.finiteFactorCentralExtensionFDRep_restrictCoefficient_character)
      a
  exact hrestriction

end ComplexCharacter

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
