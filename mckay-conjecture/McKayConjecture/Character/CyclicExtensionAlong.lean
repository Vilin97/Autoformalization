/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CyclicExtensionConstruction
import McKayConjecture.Character.ExtensionEquivalenceTransport

/-!
# Character extensions along injective homomorphisms with cyclic quotient

The cyclic extension theorem is naturally stated for a normal subgroup.
This file gives its invariant formulation for an injective homomorphism:
if the range is normal with cyclic quotient and conjugation through the
embedding is a specified character-invariant action, then the character
extends along the original homomorphism.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace IrreducibleCharacter

variable {H : Type u} {K : Type v}
variable [Group H] [Finite H] [Group K] [Finite K]

/-- An invariant irreducible character extends along an injective normal
embedding whose quotient is cyclic. -/
theorem exists_extensionAlong_of_injective_cyclic_range
    (f : H →* K)
    (hf : Function.Injective f)
    (range_normal : f.range.Normal)
    (hcyclic : IsCyclic (K ⧸ f.range))
    (action : K →* MulAut H)
    (conjugates :
      ∀ (k : K) (h : H),
        f (action k h) = k * f h * k⁻¹)
    (χ : IrreducibleCharacter H)
    (invariant :
      ∀ (k : K) (h : H),
        χ.values (action k h) = χ.values h) :
    ∃ ψ : IrreducibleCharacter K,
      IsExtensionAlong f χ ψ := by
  letI : f.range.Normal := range_normal
  let e : H ≃* f.range := MonoidHom.ofInjective hf
  let θ : IrreducibleCharacter f.range :=
    χ.comap e.symm
  obtain ⟨q, hq⟩ := hcyclic.exists_generator
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective f.range q
  have htop :
      Subgroup.zpowers (QuotientGroup.mk' f.range g) = ⊤ := by
    apply top_unique
    intro x _
    exact hq x
  have hθ :
      IsInvariantUnder f.range θ g := by
    intro x
    rw [comap_values, comap_values]
    have heq :
        e.symm
            (RepresentationTheory.ClassFunction.conjByMulEquiv
              (K := K) (H := f.range) g x) =
          action g (e.symm x) := by
      apply hf
      calc
        f
            (e.symm
              (RepresentationTheory.ClassFunction.conjByMulEquiv
                (K := K) (H := f.range) g x)) =
            (RepresentationTheory.ClassFunction.conjByMulEquiv
              (K := K) (H := f.range) g x : K) := by
                exact MonoidHom.apply_ofInjective_symm hf _
        _ = g * (x : K) * g⁻¹ := rfl
        _ = g * f (e.symm x) * g⁻¹ := by
          rw [MonoidHom.apply_ofInjective_symm]
        _ = f (action g (e.symm x)) :=
          (conjugates g (e.symm x)).symm
    rw [heq]
    exact invariant g (e.symm x)
  obtain ⟨ψ, hψ⟩ :=
    exists_extension_of_cyclic_quotient
      f.range θ htop hθ
  refine ⟨ψ, fun h ↦ ?_⟩
  have hh := hψ (e h)
  change ψ.values (f h) = χ.values h
  rw [show f h = (e h : K) by rfl]
  simpa [θ] using hh

end IrreducibleCharacter
end McKayConjecture
