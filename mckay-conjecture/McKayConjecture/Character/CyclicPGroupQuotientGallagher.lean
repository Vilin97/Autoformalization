/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CyclicQuotientMaximalExtendibility
import McKayConjecture.Character.GallagherPPrime
import McKayConjecture.Character.PGroupQuotientClifford

/-!
# Active characters over cyclic `p`-group quotients

Suppose `N ◁ G`, the quotient `G/N` is both cyclic and a `p`-group, and
`θ ∈ Irr_{p'}(N)` is active.  The `p`-group quotient forces `θ` to be
`G`-invariant, while cyclicity lets us extend `θ` to `G`.  Gallagher's
correspondence then parametrizes all prime-to-`p` characters of `G` over
`θ` by the prime-to-`p` characters of `G/N`.

This is the portion of the cyclic-factor case that follows from the
ordinary character theory already available in the project.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

open CliffordPartition

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (N : Subgroup G) [N.Normal]

/-- An active prime-to-`p` kernel character extends across a cyclic
`p`-group quotient. -/
theorem exists_pPrime_extension_of_active_of_cyclicPGroupQuotient
    [IsCyclic (G ⧸ N)]
    (hquotient : IsPGroup p (G ⧸ N))
    (θ : PPrimeIrreducibleCharacter N p)
    (hactive : IsActivePPrimeCharacter N θ) :
    ∃ ψ : PPrimeIrreducibleCharacter G p,
      IsExtensionAlong N.subtype θ.1 ψ.1 := by
  have hinertia :
      inertia N θ.1 = ⊤ :=
    inertia_eq_top_of_isActivePPrimeCharacter
      N hquotient θ hactive
  obtain ⟨q, hq⟩ :=
    isCyclic_iff_exists_zpowers_eq_top.mp
      (inferInstance : IsCyclic (G ⧸ N))
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective N q
  have hinvariant :
      IsInvariantUnder N θ.1 g := by
    intro n
    have hg :
        g⁻¹ ∈ inertia N θ.1 := by
      rw [hinertia]
      exact Subgroup.mem_top _
    have hfix :
        conjBy N g⁻¹ θ.1 = θ.1 :=
      (mem_inertia_iff N θ.1 g⁻¹).mp hg
    have hv :=
      congrArg
        (fun χ : IrreducibleCharacter N ↦
          χ.values n) hfix
    rw [conjBy_values] at hv
    have heq :
        RepresentationTheory.ClassFunction.conjByMulEquiv
            (K := G) (H := N) g n =
          (MulAut.conjNormal (H := N) g⁻¹).symm n := by
      apply Subtype.ext
      simp only [
        RepresentationTheory.ClassFunction.conjByMulEquiv_apply,
        MulAut.conjNormal_symm_apply, inv_inv]
    rw [heq]
    exact hv
  obtain ⟨ψ, hψ⟩ :=
    exists_extension_of_cyclic_quotient
      N θ.1 hq hinvariant
  exact
    ⟨⟨ψ, (hψ.isPPrimeDegree_iff p).2 θ.2⟩,
      hψ⟩

/-- A chosen prime-to-`p` extension in the cyclic `p`-group quotient
case. -/
def activeCyclicPGroupExtension
    [IsCyclic (G ⧸ N)]
    (hquotient : IsPGroup p (G ⧸ N))
    (θ : PPrimeIrreducibleCharacter N p)
    (hactive : IsActivePPrimeCharacter N θ) :
    PPrimeIrreducibleCharacter G p :=
  Classical.choose
    (exists_pPrime_extension_of_active_of_cyclicPGroupQuotient
      N hquotient θ hactive)

/-- The chosen character really extends the active kernel character. -/
theorem activeCyclicPGroupExtension_isExtension
    [IsCyclic (G ⧸ N)]
    (hquotient : IsPGroup p (G ⧸ N))
    (θ : PPrimeIrreducibleCharacter N p)
    (hactive : IsActivePPrimeCharacter N θ) :
    IsExtensionAlong N.subtype θ.1
      (activeCyclicPGroupExtension
        N hquotient θ hactive).1 :=
  Classical.choose_spec
    (exists_pPrime_extension_of_active_of_cyclicPGroupQuotient
      N hquotient θ hactive)

/-- Gallagher parametrization of the prime-to-`p` characters over an
active kernel character when the quotient is a cyclic `p`-group. -/
def activeGallagherPPrimeCorrespondenceOfCyclicPGroupQuotient
    [IsCyclic (G ⧸ N)]
    (hquotient : IsPGroup p (G ⧸ N))
    (θ : PPrimeIrreducibleCharacter N p)
    (hactive : IsActivePPrimeCharacter N θ) :
    PPrimeIrreducibleCharacter (G ⧸ N) p ≃
      CliffordCorrespondence.PPrimeIrreducibleCharactersOverAlong
        N.subtype θ.1 p :=
  gallagherPPrimeCorrespondenceOfSource
    (Fact.out : p.Prime)
    (activeCyclicPGroupExtension_isExtension
      N hquotient θ hactive)
    θ.2

end IrreducibleCharacter
end McKayConjecture
