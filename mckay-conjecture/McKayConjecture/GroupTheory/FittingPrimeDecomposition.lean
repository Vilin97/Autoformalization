/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.FittingProduct
import McKayConjecture.GroupTheory.PPrimeCore

/-!
# Separating the Fitting subgroup at one prime

This file records the elementary prime-by-prime step used in the McKay
reduction.  For a fixed prime `p`, every other prime core lies in the
`p′`-core.  Consequently, if both the `p`-core and `p′`-core are central,
then the whole Fitting subgroup is the center.
-/

noncomputable section

universe u

namespace McKayConjecture.GroupTheory

open scoped IsMulCommutative

variable {G : Type u} [Group G] [Finite G]
variable {p q : ℕ}

/-- A `q`-core is contained in the `p′`-core whenever `p` and `q` are
distinct primes. -/
theorem pCore_le_pPrimeCore_of_ne
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    pCore q G ≤ pPrimeCore p G := by
  letI : Fact q.Prime := ⟨hq⟩
  apply le_pPrimeCore
  · obtain ⟨n, hcard⟩ :=
      IsPGroup.iff_card.mp
        (pCore_isPGroup (p := q) (G := G))
    rw [IsPPrimeGroup, hcard]
    simpa using Nat.coprime_pow_primes 1 n hp hq hpq
  · infer_instance

/-- If the normal `p`-part and normal `p′`-part of a finite group are both
central, then its Fitting subgroup is exactly its center. -/
theorem fittingSubgroup_eq_center_of_pCore_le_center_of_pPrimeCore_le_center
    (hp : p.Prime)
    (hpCore : pCore p G ≤ Subgroup.center G)
    (hpPrimeCore : pPrimeCore p G ≤ Subgroup.center G) :
    fittingSubgroup G = Subgroup.center G := by
  apply le_antisymm
  · rw [fittingSubgroup_eq_iSup_primeFactors]
    apply iSup_le
    rintro ⟨q, hqCard⟩
    have hq : q.Prime :=
      Nat.prime_of_mem_primeFactors hqCard
    by_cases hqp : q = p
    · simpa [hqp] using hpCore
    · exact
        (pCore_le_pPrimeCore_of_ne
          hp hq (fun hpq ↦ hqp hpq.symm)).trans hpPrimeCore
  · exact normal_isNilpotent_le_fittingSubgroup
      (Subgroup.center G) inferInstance inferInstance

end McKayConjecture.GroupTheory
