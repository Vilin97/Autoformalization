/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveIrreducible
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Intertwiners of projective representations

An intertwiner of projective representations is a linear map commuting with
their chosen lifts.  The scalar factors do not enter this definition.  This
file proves the projective forms of the elementary irreducibility lemmas:

* a nonzero intertwiner out of an irreducible projective representation is
  injective;
* a nonzero intertwiner into an irreducible projective representation is
  surjective;
* a nonzero intertwiner between two irreducibles is a linear equivalence;
* over an algebraically closed field, every endomorphism of a finite
  dimensional irreducible projective representation is scalar.

The last result is the projective version of Schur's lemma.  Its proof uses
an eigenspace of the endomorphism, so it needs no linearization of the
projective action.
-/

noncomputable section

universe u v w x

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K : Type u} {G : Type v} {V : Type w} {W : Type x}
variable [Field K] [Group G]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- A linear map commuting with the chosen lifts of two projective
representations. -/
structure IntertwiningMap
    (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W) where
  /-- The underlying linear map. -/
  toLinearMap : V →ₗ[K] W
  /-- Equivariance with respect to every chosen projective operator. -/
  intertwines : ∀ g : G,
    toLinearMap.comp (P.operator g : V →ₗ[K] V) =
      (Q.operator g : W →ₗ[K] W).comp toLinearMap

namespace IntertwiningMap

variable {P : ProjectiveRepresentation K G V}
variable {Q : ProjectiveRepresentation K G W}

instance : CoeFun (IntertwiningMap P Q) (fun _ ↦ V → W) :=
  ⟨fun f ↦ f.toLinearMap⟩

@[ext]
theorem ext {f g : IntertwiningMap P Q}
    (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f
  cases g
  simp_all

@[simp]
theorem intertwines_apply (f : IntertwiningMap P Q)
    (g : G) (v : V) :
    f (P.operator g v) = Q.operator g (f v) := by
  exact LinearMap.congr_fun (f.intertwines g) v

/-- The kernel of a projective intertwiner is stable under the source
projective representation. -/
theorem isStable_ker (f : IntertwiningMap P Q) :
    P.IsStable (LinearMap.ker f.toLinearMap) := by
  intro g v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [f.intertwines_apply, hv, map_zero]

/-- The range of a projective intertwiner is stable under the target
projective representation. -/
theorem isStable_range (f : IntertwiningMap P Q) :
    Q.IsStable (LinearMap.range f.toLinearMap) := by
  intro g w hw
  obtain ⟨v, rfl⟩ := hw
  refine ⟨P.operator g v, ?_⟩
  exact f.intertwines_apply g v

/-- A projective intertwiner out of an irreducible source is either
injective or zero. -/
theorem injective_or_eq_zero (f : IntertwiningMap P Q)
    (hP : P.IsIrreducible) :
    Function.Injective f ∨ f.toLinearMap = 0 := by
  rcases hP.eq_bot_or_eq_top _ f.isStable_ker with hker | hker
  · exact Or.inl (LinearMap.ker_eq_bot.mp hker)
  · exact Or.inr (LinearMap.ker_eq_top.mp hker)

/-- A projective intertwiner into an irreducible target is either
surjective or zero. -/
theorem surjective_or_eq_zero (f : IntertwiningMap P Q)
    (hQ : Q.IsIrreducible) :
    Function.Surjective f ∨ f.toLinearMap = 0 := by
  rcases hQ.eq_bot_or_eq_top _ f.isStable_range with hrange | hrange
  · exact Or.inr (LinearMap.range_eq_bot.mp hrange)
  · exact Or.inl (LinearMap.range_eq_top.mp hrange)

/-- A nonzero projective intertwiner between irreducible projective
representations is bijective. -/
theorem bijective_of_ne_zero (f : IntertwiningMap P Q)
    (hP : P.IsIrreducible) (hQ : Q.IsIrreducible)
    (hf : f.toLinearMap ≠ 0) :
    Function.Bijective f :=
  ⟨(f.injective_or_eq_zero hP).resolve_right hf,
    (f.surjective_or_eq_zero hQ).resolve_right hf⟩

/-- A nonzero projective intertwiner between irreducibles, bundled as a
linear equivalence. -/
def linearEquivOfNeZero (f : IntertwiningMap P Q)
    (hP : P.IsIrreducible) (hQ : Q.IsIrreducible)
    (hf : f.toLinearMap ≠ 0) :
    V ≃ₗ[K] W :=
  LinearEquiv.ofBijective f.toLinearMap
    (f.bijective_of_ne_zero hP hQ hf)

section Schur

/-- The eigenspace of a projective endomorphism is stable under the
projective action. -/
theorem isStable_eigenspace
    (f : IntertwiningMap P P) (c : K) :
    P.IsStable (Module.End.eigenspace f.toLinearMap c) := by
  intro g v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  rw [f.intertwines_apply, hv, map_smul]

variable [IsAlgClosed K] [FiniteDimensional K V]

/-- Projective Schur lemma: every endomorphism of a finite-dimensional
irreducible projective representation over an algebraically closed field is
a scalar multiple of the identity. -/
theorem eq_smul_id
    (f : IntertwiningMap P P) (hP : P.IsIrreducible) :
    ∃ c : K, f.toLinearMap = c • LinearMap.id := by
  letI : Nontrivial V := hP.nontrivial
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f.toLinearMap
  have heigen :
      Module.End.eigenspace f.toLinearMap c = ⊤ := by
    rcases hP.eq_bot_or_eq_top _
      (f.isStable_eigenspace c) with hbot | htop
    · exact False.elim (hc hbot)
    · exact htop
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro v
  have hv : v ∈ Module.End.eigenspace f.toLinearMap c := by
    rw [heigen]
    exact Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hv
  simpa using hv

end Schur

end IntertwiningMap
end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
