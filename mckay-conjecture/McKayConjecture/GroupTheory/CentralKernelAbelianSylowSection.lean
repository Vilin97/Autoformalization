/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Sylow
import McKayConjecture.GroupTheory.CentralKernelCoprimeCommutation

/-!
# Gluing Sylow-local sections above a central kernel

Let `π : E → B` have central kernel, with `B` finite abelian.  If `π`
has a homomorphic section over every Sylow subgroup of `B`, then it has
a global homomorphic section.

The proof uses only elementary finite-group structure.  Choose one Sylow
subgroup for every prime dividing `|B|`.  The chosen Sylow subgroups form
an internal direct product.  Their lifted sections commute pairwise by
`MonoidHom.commute_apply_of_coprime_card_of_ker_le_center`, so
`MonoidHom.noncommPiCoprod` glues them to a homomorphism on the direct
product.

This is the abelian local--global splitting lemma needed by the efficient
prime-local Okuyama--Wajima route.  It avoids introducing a general
restriction--corestriction API in group cohomology.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

open scoped BigOperators

universe u v

variable (B : Type u) [CommGroup B]

/-- The finite set of primes dividing the order of `B`. -/
abbrev cardPrimeFactors :=
  (Nat.card B).primeFactors

/-- A fixed Sylow subgroup for each prime dividing `|B|`. -/
def chosenCardSylow
    (r : cardPrimeFactors B) :
    Sylow r.1 B :=
  default

/-- Distinct chosen Sylow subgroups commute elementwise in an abelian
group. -/
theorem chosenCardSylow_pairwise_commute :
    Pairwise fun r s : cardPrimeFactors B =>
      ∀ x y : B,
        x ∈ chosenCardSylow B r →
          y ∈ chosenCardSylow B s →
            Commute x y :=
  fun _ _ _ _ _ _ _ => Commute.all _ _

/-- Multiplication from the product of the chosen Sylow subgroups into
the finite abelian group. -/
def chosenCardSylowProductHom [Finite B] :
    (∀ r : cardPrimeFactors B, chosenCardSylow B r) →* B :=
  Subgroup.noncommPiCoprod
    (chosenCardSylow_pairwise_commute B)

@[simp]
theorem chosenCardSylowProductHom_mulSingle
    [Finite B]
    (r : cardPrimeFactors B)
    (x : chosenCardSylow B r) :
    chosenCardSylowProductHom B (Pi.mulSingle r x) =
      (x : B) := by
  classical
  exact
    Subgroup.noncommPiCoprod_mulSingle
      (H := fun r =>
        (chosenCardSylow B r : Subgroup B))
      r x

/-- The chosen Sylow product multiplication is bijective. -/
theorem chosenCardSylowProductHom_bijective
    [Finite B] :
    Function.Bijective (chosenCardSylowProductHom B) := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  letI :
      ∀ r, Fintype (chosenCardSylow B r) :=
    fun _ => Fintype.ofFinite _
  apply
    (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · apply
      Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply
      Subgroup.independent_of_coprime_order
        (H := fun r =>
          (chosenCardSylow B r : Subgroup B))
        (chosenCardSylow_pairwise_commute B)
    rintro ⟨r, hr⟩ ⟨s, hs⟩ hrs
    letI : Fact r.Prime :=
      ⟨Nat.prime_of_mem_primeFactors hr⟩
    letI : Fact s.Prime :=
      ⟨Nat.prime_of_mem_primeFactors hs⟩
    have hrsNat : r ≠ s := by
      intro h
      apply hrs
      exact Subtype.ext h
    simp only [← Nat.card_eq_fintype_card]
    rw [
      Sylow.card_eq_multiplicity,
      Sylow.card_eq_multiplicity
    ]
    exact
      ((Nat.coprime_primes Fact.out Fact.out).mpr
        hrsNat).pow _ _
  · simp only [← Nat.card_eq_fintype_card]
    calc
      Nat.card
          (∀ r : cardPrimeFactors B,
            chosenCardSylow B r) =
          ∏ r : cardPrimeFactors B,
            Nat.card (chosenCardSylow B r) :=
        Nat.card_pi
      _ =
          ∏ r : cardPrimeFactors B,
            r.1 ^ (Nat.card B).factorization r.1 := by
        congr 1 with ⟨r, hr⟩
        letI : Fact r.Prime :=
          ⟨Nat.prime_of_mem_primeFactors hr⟩
        exact
          Sylow.card_eq_multiplicity
            (chosenCardSylow B ⟨r, hr⟩)
      _ =
          ∏ r ∈ cardPrimeFactors B,
            r ^ (Nat.card B).factorization r :=
        Finset.prod_finset_coe
          (fun r =>
            r ^ (Nat.card B).factorization r)
          (cardPrimeFactors B)
      _ =
          (Nat.card B).factorization.prod
            (fun r n => r ^ n) :=
        rfl
      _ = Nat.card B :=
        Nat.prod_factorization_pow_eq_self
          (Nat.ne_of_gt Nat.card_pos)

/-- A finite abelian group is the direct product of one chosen Sylow
subgroup for every prime dividing its order. -/
def chosenCardSylowProductEquiv [Finite B] :
    (∀ r : cardPrimeFactors B, chosenCardSylow B r) ≃* B :=
  MulEquiv.ofBijective
    (chosenCardSylowProductHom B)
    (chosenCardSylowProductHom_bijective B)

@[simp]
theorem chosenCardSylowProductEquiv_apply
    [Finite B]
    (x :
      ∀ r : cardPrimeFactors B,
        chosenCardSylow B r) :
    chosenCardSylowProductEquiv B x =
      chosenCardSylowProductHom B x :=
  rfl

variable {B}
variable {E : Type v} [Group E]

/-- Every Sylow subgroup of the quotient admits a homomorphic lift. -/
def HasSylowSections
    (projection : E →* B) : Prop :=
  ∀ (r : ℕ) (hr : r.Prime),
    letI : Fact r.Prime := ⟨hr⟩
    ∀ R : Sylow r B,
      ∃ lift : R →* E,
        projection.comp lift =
          (R : Subgroup B).subtype

/-- The selected local section on the chosen Sylow subgroup. -/
def chosenCardSylowSection
    (projection : E →* B)
    (hlocal : HasSylowSections projection)
    (r : cardPrimeFactors B) :
    chosenCardSylow B r →* E := by
  letI : Fact r.1.Prime :=
    ⟨Nat.prime_of_mem_primeFactors r.2⟩
  exact
    Classical.choose
      (hlocal r.1
        (Nat.prime_of_mem_primeFactors r.2)
        (chosenCardSylow B r))

theorem projection_comp_chosenCardSylowSection
    (projection : E →* B)
    (hlocal : HasSylowSections projection)
    (r : cardPrimeFactors B) :
    projection.comp
        (chosenCardSylowSection projection hlocal r) =
      (chosenCardSylow B r : Subgroup B).subtype := by
  letI : Fact r.1.Prime :=
    ⟨Nat.prime_of_mem_primeFactors r.2⟩
  exact
    Classical.choose_spec
      (hlocal r.1
        (Nat.prime_of_mem_primeFactors r.2)
        (chosenCardSylow B r))

@[simp]
theorem projection_chosenCardSylowSection_apply
    (projection : E →* B)
    (hlocal : HasSylowSections projection)
    (r : cardPrimeFactors B)
    (x : chosenCardSylow B r) :
    projection
        (chosenCardSylowSection projection hlocal r x) =
      (x : B) := by
  exact
    DFunLike.congr_fun
      (projection_comp_chosenCardSylowSection
        projection hlocal r)
      x

variable [Finite B]

/-- The chosen local sections have pairwise commuting images. -/
theorem chosenCardSylowSection_pairwise_commute
    (projection : E →* B)
    (hkernel :
      projection.ker ≤ Subgroup.center E)
    (hlocal : HasSylowSections projection) :
    Pairwise fun r s : cardPrimeFactors B =>
      ∀ (x : chosenCardSylow B r)
        (y : chosenCardSylow B s),
        Commute
          (chosenCardSylowSection projection hlocal r x)
          (chosenCardSylowSection projection hlocal s y) := by
  rintro ⟨r, hr⟩ ⟨s, hs⟩ hrs x y
  letI : Fact r.Prime :=
    ⟨Nat.prime_of_mem_primeFactors hr⟩
  letI : Fact s.Prime :=
    ⟨Nat.prime_of_mem_primeFactors hs⟩
  have hrsNat : r ≠ s := by
    intro h
    apply hrs
    exact Subtype.ext h
  have hcoprime :
      (Nat.card
          (chosenCardSylow B ⟨r, hr⟩)).Coprime
        (Nat.card
          (chosenCardSylow B ⟨s, hs⟩)) := by
    rw [
      Sylow.card_eq_multiplicity,
      Sylow.card_eq_multiplicity
    ]
    exact
      ((Nat.coprime_primes Fact.out Fact.out).mpr
        hrsNat).pow _ _
  exact
    MonoidHom.commute_apply_of_coprime_card_of_ker_le_center
      projection
      hkernel
      (chosenCardSylowSection
        projection hlocal ⟨r, hr⟩)
      (chosenCardSylowSection
        projection hlocal ⟨s, hs⟩)
      hcoprime x y

/-- The homomorphism obtained by multiplying all chosen local sections. -/
def gluedChosenCardSylowSections
    (projection : E →* B)
    (hkernel :
      projection.ker ≤ Subgroup.center E)
    (hlocal : HasSylowSections projection) :
    (∀ r : cardPrimeFactors B, chosenCardSylow B r) →* E :=
  MonoidHom.noncommPiCoprod
    (chosenCardSylowSection projection hlocal)
    (chosenCardSylowSection_pairwise_commute
      projection hkernel hlocal)

@[simp]
theorem gluedChosenCardSylowSections_mulSingle
    (projection : E →* B)
    (hkernel :
      projection.ker ≤ Subgroup.center E)
    (hlocal : HasSylowSections projection)
    (r : cardPrimeFactors B)
    (x : chosenCardSylow B r) :
    gluedChosenCardSylowSections
        projection hkernel hlocal
        (Pi.mulSingle r x) =
      chosenCardSylowSection projection hlocal r x := by
  classical
  exact
    MonoidHom.noncommPiCoprod_mulSingle
      (ϕ := chosenCardSylowSection projection hlocal)
      r x

/-- Projecting the glued local sections recovers multiplication in the
chosen Sylow direct product. -/
theorem projection_comp_gluedChosenCardSylowSections
    (projection : E →* B)
    (hkernel :
      projection.ker ≤ Subgroup.center E)
    (hlocal : HasSylowSections projection) :
    projection.comp
        (gluedChosenCardSylowSections
          projection hkernel hlocal) =
      chosenCardSylowProductHom B := by
  classical
  apply MonoidHom.pi_ext
  intro r x
  simp

/-- A global homomorphic section obtained by gluing the Sylow-local
sections. -/
def gluedAbelianSylowSection
    (projection : E →* B)
    (hkernel :
      projection.ker ≤ Subgroup.center E)
    (hlocal : HasSylowSections projection) :
    B →* E :=
  (gluedChosenCardSylowSections
      projection hkernel hlocal).comp
    (chosenCardSylowProductEquiv B).symm.toMonoidHom

/-- The glued homomorphism is a right inverse to the original
projection. -/
theorem projection_comp_gluedAbelianSylowSection
    (projection : E →* B)
    (hkernel :
      projection.ker ≤ Subgroup.center E)
    (hlocal : HasSylowSections projection) :
    projection.comp
        (gluedAbelianSylowSection
          projection hkernel hlocal) =
      MonoidHom.id B := by
  apply MonoidHom.ext
  intro b
  change
    (projection.comp
      (gluedChosenCardSylowSections
        projection hkernel hlocal))
        ((chosenCardSylowProductEquiv B).symm b) =
      b
  rw [
    projection_comp_gluedChosenCardSylowSections
      projection hkernel hlocal
  ]
  change
    chosenCardSylowProductEquiv B
        ((chosenCardSylowProductEquiv B).symm b) =
      b
  exact
    (chosenCardSylowProductEquiv B).apply_symm_apply b

/-- Existence form of the abelian Sylow-local to global section theorem. -/
theorem exists_section_of_hasSylowSections
    (projection : E →* B)
    (hkernel :
      projection.ker ≤ Subgroup.center E)
    (hlocal : HasSylowSections projection) :
    ∃ lift : B →* E,
      projection.comp lift =
        MonoidHom.id B :=
  ⟨gluedAbelianSylowSection
      projection hkernel hlocal,
    projection_comp_gluedAbelianSylowSection
      projection hkernel hlocal⟩

end GroupTheory
end McKayConjecture
