/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FiniteDimensionalIndecomposable
import Mathlib.LinearAlgebra.Projection

/-!
# The local exchange step in Krull--Schmidt

This file isolates the part of the Krull--Schmidt argument which uses
local endomorphism rings.  If the identity of an indecomposable object
is a finite sum of maps factoring through a family of indecomposable
objects, then one of those objects is isomorphic to it.

The statements are phrased for intertwining maps, which is the
generality needed for finite-dimensional representations.
-/

noncomputable section

namespace Representation
namespace IntertwiningMap

universe uι uk uG uA uB

variable {k : Type uk} {G : Type uG}
variable [Field k] [Monoid G]

/-- An idempotent endomorphism of a directly indecomposable
representation is either zero or the identity. -/
theorem idempotent_eq_zero_or_eq_id
    {A : Type uA} [AddCommGroup A] [Module k A]
    {ρ : Representation k G A}
    (hρ : ρ.IsDirectSumIndecomposable)
    (e : IntertwiningMap ρ ρ)
    (he : IsIdempotentElem e) :
    e = 0 ∨ e = id ρ := by
  have heLinear : IsIdempotentElem e.toLinearMap := by
    exact congrArg toLinearMap he
  rcases hρ.2 e.range e.ker
      (LinearMap.IsIdempotentElem.isCompl heLinear) with hrange | hker
  · left
    apply IntertwiningMap.ext
    have hrange' : LinearMap.range e.toLinearMap = ⊥ :=
      congrArg Subrepresentation.toSubmodule hrange
    exact LinearMap.range_eq_bot.mp hrange'
  · right
    have hker' : LinearMap.ker e.toLinearMap = ⊥ :=
      congrArg Subrepresentation.toSubmodule hker
    have hinjective : Function.Injective e :=
      LinearMap.ker_eq_bot.mp hker'
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    apply hinjective
    simpa only [mul_apply, id_apply, toLinearMap_apply] using
      congrArg (fun f : IntertwiningMap ρ ρ => f a) he

/-- In a local endomorphism ring, if the identity is a finite sum of
endomorphisms, at least one summand is invertible.  The summands here
are displayed as factorizations through a finite family of
representations. -/
theorem exists_isUnit_comp_of_sum_comp_eq_id
    {ι : Type uι} [Fintype ι]
    {A : Type uA} [AddCommGroup A] [Module k A]
    {B : ι → Type uB}
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)]
    {ρ : Representation k G A}
    (σ : ∀ i, Representation k G (B i))
    [IsLocalRing (IntertwiningMap ρ ρ)]
    (f : ∀ i, IntertwiningMap ρ (σ i))
    (g : ∀ i, IntertwiningMap (σ i) ρ)
    (h : (∑ i, (g i).comp (f i)) = id ρ) :
    ∃ i, IsUnit ((g i).comp (f i)) := by
  have hunit : IsUnit (∑ i, (g i).comp (f i)) := by
    rw [h]
    exact isUnit_one
  obtain ⟨i, _, hi⟩ :=
    IsLocalRing.exists_of_isUnit_sum
      (s := Finset.univ)
      (f := fun i => (g i).comp (f i))
      (by simpa using hunit)
  exact ⟨i, hi⟩

/-- If `g ∘ f` is invertible and the target is directly
indecomposable, then the source and target representations are
equivalent.  This is the exchange step which turns a unit matrix
coefficient into an isomorphic summand. -/
noncomputable def equivOfIsUnitComp
    {A : Type uA} {B : Type uB}
    [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B]
    {ρ : Representation k G A}
    {σ : Representation k G B}
    [Nontrivial A]
    (hσ : σ.IsDirectSumIndecomposable)
    (f : IntertwiningMap ρ σ)
    (g : IntertwiningMap σ ρ)
    (hgf : IsUnit (g.comp f)) :
    ρ.Equiv σ := by
  let q : IntertwiningMap ρ ρ := g.comp f
  have hq : Function.Bijective q :=
    q.isUnit_iff_bijective.mp hgf
  let qEquiv : ρ.Equiv ρ := q.ofBijective hq
  let f' : IntertwiningMap ρ σ :=
    f.comp qEquiv.symm.toIntertwiningMap
  have hleft : Function.LeftInverse g f' := by
    intro a
    exact qEquiv.apply_symm_apply a
  let e : IntertwiningMap σ σ := f'.comp g
  have he : IsIdempotentElem e := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro b
    change f' (g (f' (g b))) = f' (g b)
    rw [hleft (g b)]
  have hf'bijective : Function.Bijective f' := by
    rcases idempotent_eq_zero_or_eq_id hσ e he with hezero | heone
    · exfalso
      obtain ⟨a, ha⟩ := exists_ne (0 : A)
      apply ha
      have heval :=
        congrArg (fun t : IntertwiningMap σ σ => t (f' a)) hezero
      have hfzero : f' a = 0 := by
        simp only [e, comp_apply, coe_zero, Pi.zero_apply] at heval
        rw [hleft a] at heval
        exact heval
      have hlefta := hleft a
      rw [hfzero, map_zero] at hlefta
      exact hlefta.symm
    · have hright : Function.RightInverse g f' := by
        intro b
        have heval :=
          congrArg (fun t : IntertwiningMap σ σ => t b) heone
        simpa only [e, comp_apply, id_apply] using heval
      exact ⟨hleft.injective, hright.surjective⟩
  exact f'.ofBijective hf'bijective

/-- The one-summand Krull--Schmidt exchange theorem.  If the identity
of a representation with local endomorphism ring is a finite sum of
factorizations through directly indecomposable representations, then
one member of the family is equivalent to it. -/
theorem exists_equiv_of_sum_comp_eq_id
    {ι : Type uι} [Fintype ι]
    {A : Type uA} [AddCommGroup A] [Module k A]
    {B : ι → Type uB}
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)]
    {ρ : Representation k G A}
    (σ : ∀ i, Representation k G (B i))
    [Nontrivial A]
    [IsLocalRing (IntertwiningMap ρ ρ)]
    (hσ : ∀ i, (σ i).IsDirectSumIndecomposable)
    (f : ∀ i, IntertwiningMap ρ (σ i))
    (g : ∀ i, IntertwiningMap (σ i) ρ)
    (h : (∑ i, (g i).comp (f i)) = id ρ) :
    ∃ i, Nonempty (ρ.Equiv (σ i)) := by
  obtain ⟨i, hi⟩ :=
    exists_isUnit_comp_of_sum_comp_eq_id σ f g h
  exact ⟨i, ⟨equivOfIsUnitComp (hσ i) (f i) (g i) hi⟩⟩

/-- A split retract of a finite direct sum of indecomposable
representations is isomorphic to one of the summands as soon as the
retract itself is indecomposable.  The direct sum is presented by
inclusion and projection maps resolving its identity. -/
theorem exists_equiv_of_split_retract
    {ι : Type uι} [Fintype ι]
    {A : Type uA} [AddCommGroup A] [Module k A]
    {V : Type*} [AddCommGroup V] [Module k V]
    {B : ι → Type uB}
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)]
    {ρA : Representation k G A}
    {ρV : Representation k G V}
    (ρB : ∀ i, Representation k G (B i))
    [Nontrivial A]
    [IsLocalRing (IntertwiningMap ρA ρA)]
    (hρB : ∀ i, (ρB i).IsDirectSumIndecomposable)
    (includeA : IntertwiningMap ρA ρV)
    (retractA : IntertwiningMap ρV ρA)
    (hretract : retractA.comp includeA = id ρA)
    (includeB : ∀ i, IntertwiningMap (ρB i) ρV)
    (projectB : ∀ i, IntertwiningMap ρV (ρB i))
    (hresolution :
      (∑ i, (includeB i).comp (projectB i)) = id ρV) :
    ∃ i, Nonempty (ρA.Equiv (ρB i)) := by
  apply exists_equiv_of_sum_comp_eq_id ρB hρB
      (fun i => (projectB i).comp includeA)
      (fun i => retractA.comp (includeB i))
  apply IntertwiningMap.ext
  simp only [IntertwiningMap.toLinearMap_sum]
  apply LinearMap.ext
  intro a
  simp only [LinearMap.sum_apply, comp_toLinearMap,
    LinearMap.comp_apply, toLinearMap_apply, toLinearMap_id,
    LinearMap.id_apply]
  have hresolutionAt :=
    congrArg
      (fun t : IntertwiningMap ρV ρV => t (includeA a))
      hresolution
  have hretractAt :=
    congrArg
      (fun t : IntertwiningMap ρA ρA => t a)
      hretract
  simpa only [sum_apply, comp_apply, id_apply, map_sum] using
    congrArg retractA hresolutionAt |>.trans hretractAt

end IntertwiningMap
end Representation
