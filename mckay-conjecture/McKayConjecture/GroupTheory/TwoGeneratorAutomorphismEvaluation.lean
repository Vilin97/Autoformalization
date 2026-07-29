/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Evaluating automorphisms on two generators

If two elements generate a group, an automorphism is determined by its
values on those elements.  This file packages the resulting injection into
the type of ordered pairs.  It is useful when a finite presentation turns
automorphism classification into a finite enumeration of possible generator
images.
-/

universe u v

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} {H : Type v}
variable [Group G] [Group H]

/-- Evaluation of an automorphism on an ordered pair of elements. -/
def twoGeneratorMulAutEvaluation
    (a b : G) :
    MulAut G → G × G :=
  fun α => (α a, α b)

/-- Homomorphisms out of a two-generated group are determined by the two
chosen generators. -/
theorem monoidHom_ext_of_closure_pair_eq_top
    (a b : G)
    (hgenerate :
      Subgroup.closure ({a, b} : Set G) = ⊤)
    {f g : G →* H}
    (ha : f a = g a)
    (hb : f b = g b) :
    f = g := by
  apply MonoidHom.eq_of_eqOn_dense hgenerate
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

/-- Evaluation on a generating pair is injective on the full automorphism
group. -/
theorem twoGeneratorMulAutEvaluation_injective
    (a b : G)
    (hgenerate :
      Subgroup.closure ({a, b} : Set G) = ⊤) :
    Function.Injective
      (twoGeneratorMulAutEvaluation a b) := by
  intro α β hevaluation
  apply MulEquiv.toMonoidHom_injective
  apply monoidHom_ext_of_closure_pair_eq_top a b hgenerate
  · exact congrArg Prod.fst hevaluation
  · exact congrArg Prod.snd hevaluation

end GroupTheory
end McKayConjecture
