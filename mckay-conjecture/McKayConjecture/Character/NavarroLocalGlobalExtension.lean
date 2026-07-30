/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CharacterDegreeDivisibility
import McKayConjecture.CharacterTriple.NormalHallPPrimeExtension
import McKayConjecture.CharacterTriple.SubgroupRestriction
import McKayConjecture.GroupTheory.QuotientSubgroupPreimage

/-!
# The Sylow-preimage local--global extension seam

For a character triple `(G, N, θ)` and a Sylow subgroup `R` of `G / N`,
let `G_R` be the full preimage of `R`.  Navarro's local--global extension
criterion says that `θ` extends to `G` exactly when its canonical copy
extends to every `G_R`.

The general local--global implication is intentionally recorded as the
proposition `NavarroSylowPreimageExtensionConclusion`; it is the precise
remaining theorem corresponding to Navarro, Theorem 5.10.

The coprime local input needed at the distinguished prime is already
available: an invariant character of a normal `p'`-subgroup extends over
a `p`-group quotient.  The theorem
`extendsToQuotientSylowPreimage_of_pPrimeKernel` packages that result in
the same coordinates as the local--global statement.

Finally, `hasExtension_iff_of_navarro_of_primeAwayComparison` shows that,
for two triples with isomorphic quotients and `p'` kernels, it is enough
to compare local extension existence away from `p`.  This is the abstract
prime-local reduction used by the Okuyama--Wajima argument.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace CharacterTriple

open GroupTheory

variable {G : Type u} [Group G] [Finite G]

/-- A character triple has an ordinary extension when its distinguished
normal-subgroup character extends to the ambient group. -/
def HasExtension (T : CharacterTriple G) : Prop :=
  ∃ psi : IrreducibleCharacter G,
    IrreducibleCharacter.IsExtensionAlong
      T.normalSubgroup.subtype T.character psi

/-- Extension existence on the full preimage of a quotient Sylow
subgroup.  The restricted triple supplies the canonical internal copy of
the original normal subgroup. -/
def ExtendsToQuotientSylowPreimage
    (T : CharacterTriple G)
    {r : ℕ} [Fact r.Prime]
    (R : Sylow r (G ⧸ T.normalSubgroup)) : Prop :=
  let H :=
    quotientSubgroupPreimage T.normalSubgroup
      (R : Subgroup (G ⧸ T.normalSubgroup))
  let hNH :
      T.normalSubgroup ≤ H :=
    normal_le_quotientSubgroupPreimage
      T.normalSubgroup
      (R : Subgroup (G ⧸ T.normalSubgroup))
  let TR := T.restrictTo H hNH
  ∃ psi : IrreducibleCharacter H,
    IrreducibleCharacter.IsExtensionAlong
      TR.normalSubgroup.subtype TR.character psi

/-- Exact formalization-friendly statement of Navarro's Sylow-preimage
local--global extension criterion (Theorem 5.10).

This definition names the theorem statement; it does not assert a proof. -/
def NavarroSylowPreimageExtensionConclusion
    (T : CharacterTriple G) : Prop :=
  T.HasExtension ↔
    ∀ (r : ℕ) (hr : r.Prime),
      letI : Fact r.Prime := ⟨hr⟩
      ∀ R : Sylow r (G ⧸ T.normalSubgroup),
        T.ExtendsToQuotientSylowPreimage R

/-- The degree of an irreducible character of a finite `p'`-group is
prime to `p`. -/
theorem character_isPPrimeDegree_of_isPPrimeGroup
    {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] [Finite H]
    (hH : IsPPrimeGroup p H)
    (chi : IrreducibleCharacter H) :
    chi.IsPPrimeDegree p := by
  rw [IrreducibleCharacter.IsPPrimeDegree]
  intro hpdegree
  have hpcard :
      p ∣ Nat.card H :=
    hpdegree.trans chi.degree_dvd_card
  exact
    ((isPPrimeGroup_iff_not_dvd
      (G := H) Fact.out).mp hH) hpcard

/-- Navarro's coprime extension input (Corollary 6.2) in the special form
needed here: a character triple with `p'` kernel and `p`-group quotient
has an ordinary extension. -/
theorem exists_extension_of_pPrimeKernel_pGroupQuotient
    {p : ℕ} [Fact p.Prime]
    (T : CharacterTriple G)
    (hN : IsPPrimeGroup p T.normalSubgroup)
    (hquotient :
      IsPGroup p (G ⧸ T.normalSubgroup)) :
    T.HasExtension := by
  have hdegree :
      T.character.IsPPrimeDegree p :=
    character_isPPrimeDegree_of_isPPrimeGroup
      hN T.character
  obtain ⟨psi, hpsi⟩ :=
    exists_pPrime_extension_of_normalHall
      T hN hquotient hdegree
  exact ⟨psi.1, hpsi⟩

/-- Every quotient Sylow preimage is an automatic extension locus when
the kernel is a `p'`-group. -/
theorem extendsToQuotientSylowPreimage_of_pPrimeKernel
    {p : ℕ} [Fact p.Prime]
    (T : CharacterTriple G)
    (hN : IsPPrimeGroup p T.normalSubgroup)
    (R : Sylow p (G ⧸ T.normalSubgroup)) :
    T.ExtendsToQuotientSylowPreimage R := by
  let H :=
    quotientSubgroupPreimage T.normalSubgroup
      (R : Subgroup (G ⧸ T.normalSubgroup))
  let hNH :
      T.normalSubgroup ≤ H :=
    normal_le_quotientSubgroupPreimage
      T.normalSubgroup
      (R : Subgroup (G ⧸ T.normalSubgroup))
  let TR := T.restrictTo H hNH
  have hNR :
      IsPPrimeGroup p TR.normalSubgroup := by
    exact
      hN.of_equiv
        (T.normalSubgroupInEquiv H hNH).symm
  have hquotient :
      IsPGroup p (H ⧸ TR.normalSubgroup) := by
    exact
      isPGroup_quotientSubgroupPreimage_sylow
        T.normalSubgroup R
  exact
    exists_extension_of_pPrimeKernel_pGroupQuotient
      TR hNR hquotient

section Comparison

variable {H : Type v} [Group H] [Finite H]

/-- Local extension equivalence for corresponding quotient Sylow
subgroups under an equivalence `T-quotient ≃ S-quotient`. -/
def SylowPreimageExtensionComparison
    (S : CharacterTriple G)
    (T : CharacterTriple H)
    (e :
      H ⧸ T.normalSubgroup ≃*
        G ⧸ S.normalSubgroup) : Prop :=
  ∀ (r : ℕ) (hr : r.Prime),
      letI : Fact r.Prime := ⟨hr⟩
    ∀ R : Sylow r (H ⧸ T.normalSubgroup),
      S.ExtendsToQuotientSylowPreimage
          (R.mapSurjective
            (f := e.toMonoidHom) e.surjective) ↔
        T.ExtendsToQuotientSylowPreimage R

/-- The same local comparison restricted to primes away from `p`. -/
def PrimeAwaySylowPreimageExtensionComparison
    (p : ℕ)
    (S : CharacterTriple G)
    (T : CharacterTriple H)
    (e :
      H ⧸ T.normalSubgroup ≃*
        G ⧸ S.normalSubgroup) : Prop :=
  ∀ (r : ℕ) (hr : r.Prime),
    r ≠ p →
      letI : Fact r.Prime := ⟨hr⟩
      ∀ R : Sylow r (H ⧸ T.normalSubgroup),
        S.ExtendsToQuotientSylowPreimage
            (R.mapSurjective
              (f := e.toMonoidHom) e.surjective) ↔
          T.ExtendsToQuotientSylowPreimage R

/-- Navarro local--global on both sides converts comparison on all
corresponding Sylow preimages into comparison of global extensions. -/
theorem hasExtension_iff_of_navarro_of_sylowPreimageComparison
    (S : CharacterTriple G)
    (T : CharacterTriple H)
    (e :
      H ⧸ T.normalSubgroup ≃*
        G ⧸ S.normalSubgroup)
    (hS : NavarroSylowPreimageExtensionConclusion S)
    (hT : NavarroSylowPreimageExtensionConclusion T)
    (hlocal :
      SylowPreimageExtensionComparison S T e) :
    S.HasExtension ↔ T.HasExtension := by
  rw [SylowPreimageExtensionComparison] at hlocal
  constructor
  · intro hSExt
    apply hT.mpr
    intro r hr
    letI : Fact r.Prime := ⟨hr⟩
    intro R
    exact
      (hlocal r hr R).mp
        (hS.mp hSExt r hr
          (R.mapSurjective
            (f := e.toMonoidHom) e.surjective))
  · intro hTExt
    apply hS.mpr
    intro r hr
    letI : Fact r.Prime := ⟨hr⟩
    intro P
    obtain ⟨R, rfl⟩ :=
      Sylow.mapSurjective_surjective
        (f := e.toMonoidHom) e.surjective r P
    exact
      (hlocal r hr R).mpr
        (hT.mp hTExt r hr R)

/-- With `p'` kernels, the distinguished-prime Sylow preimages are
automatic by coprime extension.  Consequently only the local comparisons
at primes `r ≠ p` remain. -/
theorem hasExtension_iff_of_navarro_of_primeAwayComparison
    {p : ℕ} [Fact p.Prime]
    (S : CharacterTriple G)
    (T : CharacterTriple H)
    (e :
      H ⧸ T.normalSubgroup ≃*
        G ⧸ S.normalSubgroup)
    (hSN : IsPPrimeGroup p S.normalSubgroup)
    (hTN : IsPPrimeGroup p T.normalSubgroup)
    (hS : NavarroSylowPreimageExtensionConclusion S)
    (hT : NavarroSylowPreimageExtensionConclusion T)
    (haway :
      PrimeAwaySylowPreimageExtensionComparison
        p S T e) :
    S.HasExtension ↔ T.HasExtension := by
  rw [PrimeAwaySylowPreimageExtensionComparison] at haway
  apply
    hasExtension_iff_of_navarro_of_sylowPreimageComparison
      S T e hS hT
  rw [SylowPreimageExtensionComparison]
  intro r hr
  letI : Fact r.Prime := ⟨hr⟩
  intro R
  by_cases hrp : r = p
  · subst r
    exact
      iff_of_true
        (extendsToQuotientSylowPreimage_of_pPrimeKernel
          S hSN
          (R.mapSurjective
            (f := e.toMonoidHom) e.surjective))
        (extendsToQuotientSylowPreimage_of_pPrimeKernel
          T hTN R)
  · exact haway r hr hrp R

end Comparison

end CharacterTriple
end McKayConjecture
