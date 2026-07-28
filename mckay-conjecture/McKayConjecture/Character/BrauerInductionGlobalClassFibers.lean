/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionCentralizerFiber
import McKayConjecture.Character.PRegularConjugacyClasses

/-!
# Global fibres indexed by `p`-regular conjugacy classes

For every `p`-regular conjugacy class, Bernstein's centralizer
construction gives a class function supported on precisely that class of
canonical `p`-regular parts.  On every element in the indexed stratum its
value is a natural number prime to `p`.

Thus these functions form a diagonal family on the partition of `G` by
the conjugacy class of the canonical `p`-regular part.  This is the
unconditional local-to-global input for the subsequent ideal and
coprime-power argument.
-/

noncomputable section

namespace McKayConjecture
namespace ClassFunction

variable {p : ℕ}
variable {G : Type} [Group G] [Finite G] [Fact p.Prime]

/-- Bernstein's global fibre attached to one `p`-regular conjugacy
class. -/
def pRegularClassFiber
    (q : PRegularConjClasses p G) :
    ClassFunction G :=
  centralizerGlobalFiber
    (p := p)
    q.representative
    q.representative_isPRegular

/-- A class fibre vanishes on every different `p`-regular stratum. -/
theorem pRegularClassFiber_apply_eq_zero_of_classOfElement_ne
    (q : PRegularConjClasses p G)
    (g : G)
    (hg :
      PRegularConjClasses.classOfElement
          (p := p) g ≠
        q) :
    pRegularClassFiber q g = 0 := by
  apply
    centralizerGlobalFiber_apply_eq_zero_of_not_isConj
      q.representative
      q.representative_isPRegular
      g
  intro hconj
  apply hg
  exact
    (PRegularConjClasses.classOfElement_eq_iff_isConj_representative
        (p := p) g q).mpr hconj

/-- On its own `p`-regular stratum, a class fibre has a natural-number
value prime to `p`. -/
theorem exists_coprime_nat_pRegularClassFiber_apply
    (g : G) :
    ∃ k : ℕ, p.Coprime k ∧
      pRegularClassFiber
          (PRegularConjClasses.classOfElement
            (p := p) g) g =
        (k : ℂ) := by
  let q :=
    PRegularConjClasses.classOfElement
      (p := p) g
  obtain ⟨c, t, ht, hat, hnormal⟩ :=
    PRegularConjClasses.exists_conjugate_eq_representative_mul_pElement
        (p := p) g
  obtain ⟨k, hk, hvalue⟩ :=
    exists_coprime_nat_centralizerGlobalFiber_mul_pElement
      q.representative
      q.representative_isPRegular
      t ht hat
  refine ⟨k, hk, ?_⟩
  change
    centralizerGlobalFiber
        q.representative
        q.representative_isPRegular g =
      (k : ℂ)
  calc
    centralizerGlobalFiber
        q.representative
        q.representative_isPRegular g =
        centralizerGlobalFiber
          q.representative
          q.representative_isPRegular
          (c * g * c⁻¹) := by
      exact
        (ClassFunction.conj_apply
          (centralizerGlobalFiber
            q.representative
            q.representative_isPRegular)
          g c).symm
    _ =
        centralizerGlobalFiber
          q.representative
          q.representative_isPRegular
          (q.representative * t) := by
      rw [hnormal]
    _ = (k : ℂ) := hvalue

/-- Distinct class fibres vanish at the other chosen representatives. -/
theorem pRegularClassFiber_apply_representative_eq_zero
    {q r : PRegularConjClasses p G}
    (hqr : q ≠ r) :
    pRegularClassFiber q r.representative = 0 := by
  apply
    pRegularClassFiber_apply_eq_zero_of_classOfElement_ne
      q r.representative
  rw [PRegularConjClasses.classOfElement_representative]
  exact hqr.symm

/-- The diagonal value at a chosen representative is a natural number
prime to `p`. -/
theorem exists_coprime_nat_pRegularClassFiber_representative
    (q : PRegularConjClasses p G) :
    ∃ k : ℕ, p.Coprime k ∧
      pRegularClassFiber q q.representative =
        (k : ℂ) := by
  simpa only [
    PRegularConjClasses.classOfElement_representative]
    using
      exists_coprime_nat_pRegularClassFiber_apply
        (p := p) q.representative

end ClassFunction
end McKayConjecture
