/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SylowAutomorphismInnerAdjustment

/-!
# Conjugacy invariants and outer automorphism classes

Automorphisms with the same image modulo inner automorphisms induce the
same action on every conjugation-invariant function.  This elementary
observation lets checked conjugacy-class actions separate elements of an
outer automorphism quotient.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

universe u v

variable {G : Type u} [Group G] {ι : Type v}

/-- Equal outer classes act identically on a conjugation-invariant
function. -/
theorem conjugationInvariant_apply_eq_of_outer_eq
    (classInvariant : G → ι)
    (hclassInvariant :
      ∀ g x : G,
        classInvariant (g * x * g⁻¹) =
          classInvariant x)
    {a b : MulAut G}
    (hab :
      QuotientGroup.mk' (InnerAutomorphismSubgroup G) a =
        QuotientGroup.mk' (InnerAutomorphismSubgroup G) b)
    (x : G) :
    classInvariant (a x) = classInvariant (b x) := by
  obtain ⟨inner, ⟨g, rfl⟩, hproduct⟩ :=
    (QuotientGroup.mk'_eq_mk'
      (InnerAutomorphismSubgroup G)).1 hab
  have hvalue :=
    congrArg (fun c : MulAut G ↦ c x) hproduct
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul,
    map_inv] at hvalue
  have hinvariant :=
    hclassInvariant (a g) (a x)
  rw [hvalue] at hinvariant
  exact hinvariant.symm

end InductiveMcKay
end McKayConjecture
