/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Burnside
import McKayConjecture.Character.Construction
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Submodule

/-!
# External tensor products of finite-dimensional representations

The external tensor product of a representation of `G` and a representation
of `H` is the representation of `G × H` on the tensor product of their
carriers.  This file proves the exact action, character, and dimension
formulas and proves that the external tensor product of two simple complex
representations is simple.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra MonoidalCategory TensorProduct

namespace McKayConjecture
namespace FDRep

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- The external tensor product of finite-dimensional representations. -/
abbrev externalTensor (V : FDRep ℂ G) (W : FDRep ℂ H) :
    FDRep ℂ (G × H) :=
  FDRep.of
    (Representation.tprod
      ((show Representation ℂ G V from V.ρ).comp
        (MonoidHom.fst G H))
      ((show Representation ℂ H W from W.ρ).comp
        (MonoidHom.snd G H)))

@[simp]
theorem externalTensor_ρ_apply
    (V : FDRep ℂ G) (W : FDRep ℂ H) (g : G) (h : H) :
    (externalTensor V W).ρ (g, h) =
      TensorProduct.map (V.ρ g) (W.ρ h) :=
  rfl

@[simp]
theorem externalTensor_character
    (V : FDRep ℂ G) (W : FDRep ℂ H) (g : G) (h : H) :
    (externalTensor V W).character (g, h) =
      V.character g * W.character h := by
  change
    (Representation.tprod
      ((show Representation ℂ G V from V.ρ).comp
        (MonoidHom.fst G H))
      ((show Representation ℂ H W from W.ρ).comp
        (MonoidHom.snd G H))).character (g, h) =
      V.character g * W.character h
  rw [Representation.char_tensor]
  rfl

@[simp]
theorem externalTensor_finrank
    (V : FDRep ℂ G) (W : FDRep ℂ H) :
    Module.finrank ℂ (externalTensor V W) =
      Module.finrank ℂ V * Module.finrank ℂ W :=
  Module.finrank_tensorProduct

/-- A subrepresentation of an external tensor product is stable under every
endomorphism acting on the first tensor factor. -/
theorem externalTensor_firstEnd_mem
    (V : FDRep ℂ G) (W : FDRep ℂ H)
    [Simple V]
    (L : Subrepresentation (externalTensor V W).ρ)
    (f : Module.End ℂ V)
    ⦃t : V ⊗[ℂ] W⦄ (ht : t ∈ L.toSubmodule) :
    TensorProduct.map f LinearMap.id t ∈ L.toSubmodule := by
  let repV : Representation ℂ G V := V.ρ
  letI : Representation.IsIrreducible repV :=
    CliffordRestriction.isIrreducible_of_simple V
  obtain ⟨r, hr⟩ :=
    Representation.asAlgebraHom_surjective_of_isIrreducible
      repV f
  let ρG : Representation ℂ G (V ⊗[ℂ] W) :=
    repV.tprod 1
  have hstable :
      ∀ (g : G) ⦃x : V ⊗[ℂ] W⦄,
        x ∈ L.toSubmodule → ρG g x ∈ L.toSubmodule := by
    intro g x hx
    have hL :=
      L.apply_mem_toSubmodule (g, 1) hx
    rw [externalTensor_ρ_apply] at hL
    simpa [ρG, repV] using hL
  have hrmem :
      ρG.asAlgebraHom r t ∈ L.toSubmodule :=
    Representation.asAlgebraHom_mem_of_forall_mem ρG
      L.toSubmodule hstable t ht r
  have haction :
      ρG.asAlgebraHom r =
        TensorProduct.map (repV.asAlgebraHom r) LinearMap.id := by
    apply LinearMap.ext
    intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro v w
      exact Representation.smul_tprod_one_asModule
        repV r v w
    · intro x y hx hy
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  rw [haction, hr] at hrmem
  exact hrmem

/-- A subrepresentation of an external tensor product is stable under every
endomorphism acting on the second tensor factor. -/
theorem externalTensor_secondEnd_mem
    (V : FDRep ℂ G) (W : FDRep ℂ H)
    [Simple W]
    (L : Subrepresentation (externalTensor V W).ρ)
    (f : Module.End ℂ W)
    ⦃t : V ⊗[ℂ] W⦄ (ht : t ∈ L.toSubmodule) :
    TensorProduct.map LinearMap.id f t ∈ L.toSubmodule := by
  let repW : Representation ℂ H W := W.ρ
  letI : Representation.IsIrreducible repW :=
    CliffordRestriction.isIrreducible_of_simple W
  obtain ⟨r, hr⟩ :=
    Representation.asAlgebraHom_surjective_of_isIrreducible
      repW f
  let ρH : Representation ℂ H (V ⊗[ℂ] W) :=
    (1 : Representation ℂ H V).tprod repW
  have hstable :
      ∀ (h : H) ⦃x : V ⊗[ℂ] W⦄,
        x ∈ L.toSubmodule → ρH h x ∈ L.toSubmodule := by
    intro h x hx
    have hL :=
      L.apply_mem_toSubmodule (1, h) hx
    rw [externalTensor_ρ_apply] at hL
    simpa [ρH, repW] using hL
  have hrmem :
      ρH.asAlgebraHom r t ∈ L.toSubmodule :=
    Representation.asAlgebraHom_mem_of_forall_mem ρH
      L.toSubmodule hstable t ht r
  have haction :
      ρH.asAlgebraHom r =
        TensorProduct.map LinearMap.id (repW.asAlgebraHom r) := by
    apply LinearMap.ext
    intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro v w
      exact Representation.smul_one_tprod_asModule
        repW r v w
    · intro x y hx hy
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  rw [haction, hr] at hrmem
  exact hrmem

/-- A subrepresentation of an external tensor product of simple factors is
stable under every linear endomorphism of the tensor-product carrier. -/
theorem externalTensor_allEnd_mem
    (V : FDRep ℂ G) (W : FDRep ℂ H)
    [Simple V] [Simple W]
    (L : Subrepresentation (externalTensor V W).ρ)
    (F : Module.End ℂ (V ⊗[ℂ] W))
    ⦃t : V ⊗[ℂ] W⦄ (ht : t ∈ L.toSubmodule) :
    F t ∈ L.toSubmodule := by
  have hpure
      (f : Module.End ℂ V) (g : Module.End ℂ W)
      ⦃x : V ⊗[ℂ] W⦄ (hx : x ∈ L.toSubmodule) :
      TensorProduct.map f g x ∈ L.toSubmodule := by
    have hfirst :=
      externalTensor_firstEnd_mem V W L f hx
    have hsecond :=
      externalTensor_secondEnd_mem V W L g hfirst
    have heq :
        TensorProduct.map LinearMap.id g
            (TensorProduct.map f LinearMap.id x) =
          TensorProduct.map f g x := by
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      simp
    rwa [heq] at hsecond
  obtain ⟨x, hx⟩ :=
    (homTensorHomEquiv
      ℂ V W V W).surjective F
  rw [← hx, homTensorHomEquiv_apply]
  clear hx F
  induction x using TensorProduct.induction_on with
  | zero =>
      exact L.toSubmodule.zero_mem
  | tmul f g =>
      simpa only [TensorProduct.homTensorHomMap_apply] using
        hpure f g ht
  | add x y hx hy =>
      rw [map_add, LinearMap.add_apply]
      exact L.toSubmodule.add_mem hx hy

/-- The external tensor product of two simple finite-dimensional complex
representations is irreducible in the subrepresentation-lattice sense. -/
theorem externalTensor_isIrreducible
    (V : FDRep ℂ G) (W : FDRep ℂ H)
    [Simple V] [Simple W] :
    Representation.IsIrreducible (externalTensor V W).ρ := by
  letI : Nontrivial V :=
    CliffordRestriction.nontrivial_of_simple V
  letI : Nontrivial W :=
    CliffordRestriction.nontrivial_of_simple W
  have htensorPos :
      0 < Module.finrank ℂ (V ⊗[ℂ] W) := by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  letI : Nontrivial (V ⊗[ℂ] W) :=
    Module.nontrivial_of_finrank_pos htensorPos
  letI : Nontrivial (externalTensor V W) :=
    Module.nontrivial_of_finrank_pos (by
      rw [externalTensor_finrank]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)
  letI :
      Nontrivial
        (Subrepresentation (externalTensor V W).ρ) :=
    ⟨⟨⊥, ⊤, fun h ↦
      bot_ne_top
        (congrArg Subrepresentation.toSubmodule h)⟩⟩
  refine ⟨fun L ↦ ?_⟩
  by_cases hL : L = ⊥
  · exact Or.inl hL
  · right
    apply Subrepresentation.ext
    apply Submodule.eq_top_iff'.mpr
    obtain ⟨t, ht, ht0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot
        (fun hbot ↦ hL <| by
          apply Subrepresentation.ext
          exact hbot)
    obtain ⟨φ, hφ⟩ :=
      Module.Projective.exists_dual_eq_one ℂ ht0
    intro y
    let F : Module.End ℂ (V ⊗[ℂ] W) :=
      LinearMap.smulRight φ y
    have hFy :=
      externalTensor_allEnd_mem V W L F ht
    change (φ t) • y ∈ L.toSubmodule at hFy
    rw [hφ, one_smul] at hFy
    exact hFy

/-- The external tensor product of simple factors is categorically simple. -/
theorem externalTensor_simple
    (V : FDRep ℂ G) (W : FDRep ℂ H)
    [Simple V] [Simple W] :
    Simple (externalTensor V W) := by
  letI :
      Representation.IsIrreducible (externalTensor V W).ρ :=
    externalTensor_isIrreducible V W
  exact
    FDRep.simple_of_representation_isIrreducible
      (externalTensor V W).ρ

end FDRep
end McKayConjecture
