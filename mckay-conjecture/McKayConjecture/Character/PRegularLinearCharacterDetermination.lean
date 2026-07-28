/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PRegularDecomposition
import McKayConjecture.GroupTheory.PPrimeCore

/-!
# Determining linear characters from `p`-regular values

Every element of a finite group is a commuting product of a `p`-element
and a `p`-regular element.  Consequently a homomorphism out of the group is
determined by its values on those two kinds of elements.

The quotient form is especially useful in character theory.  If a
homomorphism kills every `p`-element, then each element of its range has a
`p`-regular representative.  This is the elementary step used near the end
of the Dade--Glauberman--Nagao character comparison.
-/

namespace McKayConjecture

universe u v

variable {p : ℕ}
variable {G : Type u} {A : Type v}
variable [Group G] [Finite G] [Group A] [Fact p.Prime]

namespace IsPElement

omit [Finite G] [Fact p.Prime] in
/-- A `p`-element of a finite `p'`-group is the identity. -/
theorem eq_one_of_isPPrimeGroup
    {g : G}
    (hg : IsPElement p g)
    (hG : GroupTheory.IsPPrimeGroup p G) :
    g = 1 := by
  obtain ⟨k, hk⟩ := hg
  have hpow : orderOf g ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one hk
  have hcard : orderOf g ∣ Nat.card G :=
    orderOf_dvd_natCard g
  have hone : orderOf g = 1 :=
    Nat.eq_one_of_dvd_coprimes
      (hG.pow_left k) hpow hcard
  exact orderOf_eq_one_iff.mp hone

end IsPElement

namespace MonoidHom

/-- A homomorphism out of a finite group is determined by its values on
`p`-elements and on `p`-regular elements. -/
theorem eq_of_eq_on_pElements_and_pRegular
    (χ ψ : G →* A)
    (hp :
      ∀ g : G, IsPElement p g →
        χ g = ψ g)
    (hregular :
      ∀ g : G, IsPRegular p g →
        χ g = ψ g) :
    χ = ψ := by
  ext g
  let d := PRegularDecomposition.chosen p g
  rw [← d.mul_eq, map_mul, map_mul,
    hp d.pPart d.isPElement,
    hregular d.regularPart d.isPRegular]

/-- If two homomorphisms kill all `p`-elements, equality on `p`-regular
elements already implies equality everywhere. -/
theorem eq_of_eq_on_pRegular_of_pElements_eq_one
    (χ ψ : G →* A)
    (hχ :
      ∀ g : G, IsPElement p g →
        χ g = 1)
    (hψ :
      ∀ g : G, IsPElement p g →
        ψ g = 1)
    (hregular :
      ∀ g : G, IsPRegular p g →
        χ g = ψ g) :
    χ = ψ := by
  apply eq_of_eq_on_pElements_and_pRegular (p := p) χ ψ
  · intro g hg
    rw [hχ g hg, hψ g hg]
  · exact hregular

/-- If a homomorphism kills every `p`-element, each value in its range is
already attained on a `p`-regular element. -/
theorem exists_pRegular_preimage_of_pElements_eq_one
    (φ : G →* A)
    (hp :
      ∀ g : G, IsPElement p g →
        φ g = 1)
    (g : G) :
    ∃ r : G,
      IsPRegular p r ∧
        φ r = φ g := by
  let d := PRegularDecomposition.chosen p g
  refine ⟨d.regularPart, d.isPRegular, ?_⟩
  have hvalue := congrArg φ d.mul_eq
  simpa only [map_mul, hp d.pPart d.isPElement, one_mul] using hvalue

/-- A surjective homomorphism whose kernel contains every `p`-element
admits a `p`-regular lift of every target element. -/
theorem exists_pRegular_preimage_of_surjective_of_pElements_mem_ker
    (φ : G →* A)
    (hsurjective : Function.Surjective φ)
    (hp :
      ∀ g : G, IsPElement p g →
        g ∈ φ.ker)
    (a : A) :
    ∃ r : G,
      IsPRegular p r ∧
        φ r = a := by
  obtain ⟨g, rfl⟩ := hsurjective a
  obtain ⟨r, hr, hvalue⟩ :=
    exists_pRegular_preimage_of_pElements_eq_one
      (p := p) φ
      (fun x hx => MonoidHom.mem_ker.mp (hp x hx))
      g
  exact ⟨r, hr, hvalue⟩

/-- Every element of a finite `p'`-quotient has a `p`-regular lift. -/
theorem exists_pRegular_preimage_of_surjective_of_isPPrimeGroup
    [Finite A]
    (φ : G →* A)
    (hsurjective : Function.Surjective φ)
    (hA : GroupTheory.IsPPrimeGroup p A)
    (a : A) :
    ∃ r : G,
      IsPRegular p r ∧
        φ r = a := by
  apply
    exists_pRegular_preimage_of_surjective_of_pElements_mem_ker
      (p := p) φ hsurjective
  intro g hg
  apply MonoidHom.mem_ker.mpr
  exact (hg.map p φ).eq_one_of_isPPrimeGroup hA

/-- If two homomorphisms agree on a normal subgroup with `p'` quotient,
then agreement on `p`-regular elements implies agreement everywhere. -/
theorem eq_of_eq_on_normal_of_isPPrimeQuotient_of_eq_on_pRegular
    (N : Subgroup G) [N.Normal]
    (hquotient :
      GroupTheory.IsPPrimeGroup p (G ⧸ N))
    (χ ψ : G →* A)
    (hN :
      ∀ x : N, χ x = ψ x)
    (hregular :
      ∀ g : G, IsPRegular p g →
        χ g = ψ g) :
    χ = ψ := by
  apply eq_of_eq_on_pElements_and_pRegular (p := p) χ ψ
  · intro g hg
    have hquotientValue :
        QuotientGroup.mk' N g = 1 :=
      (hg.map p (QuotientGroup.mk' N)).eq_one_of_isPPrimeGroup
        hquotient
    have hgN : g ∈ N :=
      (QuotientGroup.eq_one_iff g).mp hquotientValue
    exact hN ⟨g, hgN⟩
  · exact hregular

/-- A homomorphism which is trivial on both `p`-elements and `p`-regular
elements is trivial. -/
theorem eq_one_of_pElements_eq_one_of_pRegular_eq_one
    (χ : G →* A)
    (hp :
      ∀ g : G, IsPElement p g →
        χ g = 1)
    (hregular :
      ∀ g : G, IsPRegular p g →
        χ g = 1) :
    χ = 1 := by
  apply eq_of_eq_on_pElements_and_pRegular (p := p) χ 1
  · intro g hg
    simpa using hp g hg
  · intro g hg
    simpa using hregular g hg

end MonoidHom

end McKayConjecture
