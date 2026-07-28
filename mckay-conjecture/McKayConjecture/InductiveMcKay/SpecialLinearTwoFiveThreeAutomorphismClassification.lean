/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeOuterActions

/-!
# Automorphisms stabilizing the Sylow-three subgroup of `SL(2, 𝔽₅)`

Every automorphism stabilizing the chosen Sylow-three subgroup is either
inner by an element of its exact normalizer, or is the chosen outer
automorphism followed by such an inner automorphism.  We also identify the
restriction of both normal forms to the exact normalizer.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- If an inner automorphism stabilizes the chosen Sylow-three subgroup,
its conjugating element lies in the exact normalizer. -/
theorem specialLinearTwoFive_mem_sylowThreeNormalizer_of_stabilizing_inner
    (g : SpecialLinearTwoFive)
    (a : SylowAutStabilizer specialLinearTwoFiveSylowThree)
    (ha : a.1 = MulAut.conj g) :
    g ∈ Subgroup.normalizer
      (specialLinearTwoFiveSylowThree :
        Set SpecialLinearTwoFive) := by
  apply
    (Subgroup.mem_normalizer_iff_map_conj_eq
      (H := (specialLinearTwoFiveSylowThree :
        Subgroup SpecialLinearTwoFive))).2
  have hstabilizes :=
    congrArg
      (fun Q : Sylow 3 SpecialLinearTwoFive =>
        (Q : Subgroup SpecialLinearTwoFive))
      a.2
  rw [ha] at hstabilizes
  exact hstabilizes

/-- Every Sylow-three-stabilizing automorphism is inner by an element of
the normalizer, or the fixed outer automorphism followed by such an inner
automorphism. -/
theorem
    specialLinearTwoFive_sylowThreeStabilizer_eq_inner_or_outer_inner
    (a : SylowAutStabilizer specialLinearTwoFiveSylowThree) :
    ∃ g : SpecialLinearTwoFiveSylowThreeNormalizer,
      a.1 = MulAut.conj g.1 ∨
        a.1 =
          specialLinearTwoFiveSylowThreeOuterAutomorphism *
            MulAut.conj g.1 := by
  obtain ⟨g, hg | hg⟩ :=
    specialLinearTwoFive_automorphism_eq_inner_or_outer_inner a.1
  · exact
      ⟨⟨g,
          specialLinearTwoFive_mem_sylowThreeNormalizer_of_stabilizing_inner
            g a hg⟩,
        Or.inl hg⟩
  · let b :
        SylowAutStabilizer specialLinearTwoFiveSylowThree :=
      specialLinearTwoFiveSylowThreeOuterStabilizer⁻¹ * a
    have hb : b.1 = MulAut.conj g := by
      change
        specialLinearTwoFiveSylowThreeOuterAutomorphism⁻¹ * a.1 =
          MulAut.conj g
      rw [hg]
      simp
    exact
      ⟨⟨g,
          specialLinearTwoFive_mem_sylowThreeNormalizer_of_stabilizing_inner
            g b hb⟩,
        Or.inr hg⟩

/-- Restriction of a stabilizing inner automorphism is the corresponding
inner automorphism of the exact normalizer. -/
theorem specialLinearTwoFive_sylowThreeNormalizerRestriction_eq_inner
    (a : SylowAutStabilizer specialLinearTwoFiveSylowThree)
    (g : SpecialLinearTwoFiveSylowThreeNormalizer)
    (ha : a.1 = MulAut.conj g.1) :
    SylowAutStabilizer.normalizerRestrictionHom
        specialLinearTwoFiveSylowThree a =
      MulAut.conj g := by
  apply DFunLike.ext _ _
  intro x
  apply Subtype.ext
  change a.1 x.1 = g.1 * x.1 * g.1⁻¹
  rw [ha]
  rfl

/-- Restriction respects the outer-then-inner normal form. -/
theorem
    specialLinearTwoFive_sylowThreeNormalizerRestriction_eq_outer_inner
    (a : SylowAutStabilizer specialLinearTwoFiveSylowThree)
    (g : SpecialLinearTwoFiveSylowThreeNormalizer)
    (ha :
      a.1 =
        specialLinearTwoFiveSylowThreeOuterAutomorphism *
          MulAut.conj g.1) :
    SylowAutStabilizer.normalizerRestrictionHom
        specialLinearTwoFiveSylowThree a =
      SylowAutStabilizer.normalizerRestrictionHom
          specialLinearTwoFiveSylowThree
          specialLinearTwoFiveSylowThreeOuterStabilizer *
        MulAut.conj g := by
  apply DFunLike.ext _ _
  intro x
  apply Subtype.ext
  change
    a.1 x.1 =
      specialLinearTwoFiveSylowThreeOuterAutomorphism
        (g.1 * x.1 * g.1⁻¹)
  rw [ha]
  rfl

end InductiveMcKay
end McKayConjecture
