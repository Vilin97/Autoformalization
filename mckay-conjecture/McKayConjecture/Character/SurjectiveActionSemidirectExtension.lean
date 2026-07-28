/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.KernelQuotient
import McKayConjecture.Character.Construction
import McKayConjecture.Character.CyclicExtensionIntertwiner
import McKayConjecture.CharacterTriple.Semidirect

/-!
# Semidirect extensions from a surjective implementer cover

Suppose an action group `A` is covered by a group `L`, and the action of the
image of `l : L` on `G` is conjugation by a specified element of `G`.  If a
representation of `G` kills the kernel of the covering map, its operators
descend from `L` to `A`.  The descended operators and the original
representation combine to an honest representation of `G ⋊ A`.

This is the reusable central-product construction needed for inner
automorphism stabilizers.
-/

noncomputable section

open CategoryTheory

universe u v w

namespace McKayConjecture

/-- Descend a homomorphism through the kernel of a surjective covering
homomorphism. -/
def implementationOfSurjectiveCover
    {L : Type u} {A : Type v} {H : Type w}
    [Group L] [Group A] [Group H]
    (c : L →* A) (hc : Function.Surjective c)
    (r : L →* H) (hker : c.ker ≤ r.ker) :
    A →* H :=
  (QuotientGroup.lift c.ker r hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective c hc).symm.toMonoidHom

@[simp]
theorem implementationOfSurjectiveCover_apply_cover
    {L : Type u} {A : Type v} {H : Type w}
    [Group L] [Group A] [Group H]
    (c : L →* A) (hc : Function.Surjective c)
    (r : L →* H) (hker : c.ker ≤ r.ker)
    (l : L) :
    implementationOfSurjectiveCover c hc r hker (c l) = r l := by
  have hsymm :
      (QuotientGroup.quotientKerEquivOfSurjective c hc).symm (c l) =
        QuotientGroup.mk' c.ker l := by
    apply
      (QuotientGroup.quotientKerEquivOfSurjective c hc).injective
    simp only [MulEquiv.apply_symm_apply]
    rfl
  rw [implementationOfSurjectiveCover, MonoidHom.comp_apply,
    show
      (QuotientGroup.quotientKerEquivOfSurjective c hc).symm.toMonoidHom
          (c l) =
        QuotientGroup.mk' c.ker l from hsymm,
    show
      QuotientGroup.mk' c.ker l =
        (l : L ⧸ c.ker) from rfl,
    QuotientGroup.lift_mk]

namespace IrreducibleCharacter

variable {G : Type u} {A : Type v} {L : Type w}
variable [Group G] [Group A] [Group L]

/-- The honest action on `G ⋊ A` obtained by descending conjugating
implementers from a surjective cover of `A`. -/
def surjectiveCoverSemidirectLinearAction
    (φ : A →* MulAut G)
    (χ : IrreducibleCharacter G)
    (c : L →* A) (hc : Function.Surjective c)
    (f : L →* G)
    (haction : ∀ l : L, φ (c l) = MulAut.conj (f l))
    (hker :
      c.ker ≤
        (χ.realizationLinearEquivHom.comp f).ker) :
    G ⋊[φ] A →*
      (χ.realization ≃ₗ[ℂ] χ.realization) := by
  let implementer :
      A →* (χ.realization ≃ₗ[ℂ] χ.realization) :=
    implementationOfSurjectiveCover c hc
      (χ.realizationLinearEquivHom.comp f) hker
  apply
    SemidirectProduct.lift
      χ.realizationLinearEquivHom implementer
  intro a
  obtain ⟨l, rfl⟩ := hc a
  apply MonoidHom.ext
  intro g
  change
    χ.realizationLinearEquivHom (φ (c l) g) =
      MulAut.conj (implementer (c l))
        (χ.realizationLinearEquivHom g)
  rw [haction l]
  change
    χ.realizationLinearEquivHom
        (f l * g * (f l)⁻¹) =
      MulAut.conj (implementer (c l))
        (χ.realizationLinearEquivHom g)
  rw [implementationOfSurjectiveCover_apply_cover]
  simp only [MonoidHom.comp_apply, map_mul, map_inv, MulAut.conj_apply]

@[simp]
theorem surjectiveCoverSemidirectLinearAction_inl
    (φ : A →* MulAut G)
    (χ : IrreducibleCharacter G)
    (c : L →* A) (hc : Function.Surjective c)
    (f : L →* G)
    (haction : ∀ l : L, φ (c l) = MulAut.conj (f l))
    (hker :
      c.ker ≤
        (χ.realizationLinearEquivHom.comp f).ker)
    (g : G) :
    surjectiveCoverSemidirectLinearAction
        φ χ c hc f haction hker
        (SemidirectProduct.inl g) =
      χ.realizationLinearEquivHom g := by
  unfold surjectiveCoverSemidirectLinearAction
  rw [SemidirectProduct.lift_inl]

/-- The finite-dimensional representation extending `χ` across the
semidirect product. -/
def surjectiveCoverSemidirectFDRep
    (φ : A →* MulAut G)
    (χ : IrreducibleCharacter G)
    (c : L →* A) (hc : Function.Surjective c)
    (f : L →* G)
    (haction : ∀ l : L, φ (c l) = MulAut.conj (f l))
    (hker :
      c.ker ≤
        (χ.realizationLinearEquivHom.comp f).ker) :
    FDRep ℂ (G ⋊[φ] A) :=
  FDRep.of
    (CharacterTriple.linearRepresentationOfAction
      (surjectiveCoverSemidirectLinearAction
        φ χ c hc f haction hker))

theorem surjectiveCoverSemidirectFDRep_simple
    [Finite G] [Finite A]
    (φ : A →* MulAut G)
    (χ : IrreducibleCharacter G)
    (c : L →* A) (hc : Function.Surjective c)
    (f : L →* G)
    (haction : ∀ l : L, φ (c l) = MulAut.conj (f l))
    (hker :
      c.ker ≤
        (χ.realizationLinearEquivHom.comp f).ker) :
    Simple
      (surjectiveCoverSemidirectFDRep
        φ χ c hc f haction hker) := by
  let σ :=
    CharacterTriple.linearRepresentationOfAction
      (surjectiveCoverSemidirectLinearAction
        φ χ c hc f haction hker)
  let inl :
      G →* G ⋊[φ] A :=
    SemidirectProduct.inl
  have hcomp :
      σ.comp inl = χ.realization.ρ := by
    apply MonoidHom.ext
    intro g
    change
      (surjectiveCoverSemidirectLinearAction
        φ χ c hc f haction hker
        (SemidirectProduct.inl g)).toLinearMap =
        χ.realization.ρ g
    rw [surjectiveCoverSemidirectLinearAction_inl]
    exact χ.realizationLinearEquivHom_toLinearMap g
  letI : Representation.IsIrreducible χ.realization.ρ :=
    CliffordRestriction.isIrreducible_of_simple χ.realization
  have hcompIrreducible :
      Representation.IsIrreducible (σ.comp inl) := by
    rw [hcomp]
    infer_instance
  letI : Representation.IsIrreducible σ :=
    RepresentationTheory.Representation.isIrreducible_of_isIrreducible_comp
      σ hcompIrreducible
  exact FDRep.simple_of_representation_isIrreducible σ

/-- The resulting honest irreducible extension character. -/
def surjectiveCoverSemidirectExtension
    [Finite G] [Finite A]
    (φ : A →* MulAut G)
    (χ : IrreducibleCharacter G)
    (c : L →* A) (hc : Function.Surjective c)
    (f : L →* G)
    (haction : ∀ l : L, φ (c l) = MulAut.conj (f l))
    (hker :
      c.ker ≤
        (χ.realizationLinearEquivHom.comp f).ker) :
    IrreducibleCharacter (G ⋊[φ] A) := by
  letI :
      Simple
        (surjectiveCoverSemidirectFDRep
          φ χ c hc f haction hker) :=
    surjectiveCoverSemidirectFDRep_simple
      φ χ c hc f haction hker
  exact
    IrreducibleCharacter.ofSimple
      (surjectiveCoverSemidirectFDRep
        φ χ c hc f haction hker)

/-- The constructed character really restricts to `χ` on the canonical
normal copy of `G`. -/
theorem surjectiveCoverSemidirectExtension_isExtension
    [Finite G] [Finite A]
    (φ : A →* MulAut G)
    (χ : IrreducibleCharacter G)
    (c : L →* A) (hc : Function.Surjective c)
    (f : L →* G)
    (haction : ∀ l : L, φ (c l) = MulAut.conj (f l))
    (hker :
      c.ker ≤
        (χ.realizationLinearEquivHom.comp f).ker) :
    IsExtensionAlong
      (CharacterTriple.ofSemidirect φ χ
        (fun a g ↦ by
          obtain ⟨l, rfl⟩ := hc a
          rw [haction l, MulAut.conj_apply]
          exact
            ClassFunction.conj_apply χ.toClassFunction
              g (f l))).normalSubgroup.subtype
      (CharacterTriple.ofSemidirect φ χ
        (fun a g ↦ by
          obtain ⟨l, rfl⟩ := hc a
          rw [haction l, MulAut.conj_apply]
          exact
            ClassFunction.conj_apply χ.toClassFunction
              g (f l))).character
      (surjectiveCoverSemidirectExtension
        φ χ c hc f haction hker) := by
  intro x
  change
    LinearMap.trace ℂ χ.realization
        ((surjectiveCoverSemidirectLinearAction
          φ χ c hc f haction hker x.1).toLinearMap) =
      χ.values x.1.left
  obtain ⟨g, hg⟩ := x.2
  rw [← hg, surjectiveCoverSemidirectLinearAction_inl,
    realizationLinearEquivHom_toLinearMap]
  exact congrFun χ.realization_character g

end IrreducibleCharacter
end McKayConjecture
