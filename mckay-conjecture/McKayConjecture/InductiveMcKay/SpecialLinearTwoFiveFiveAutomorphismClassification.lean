/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveAutomorphisms
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveSylowFiveNormalizer
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoAutomorphismClassification

/-!
# Automorphisms stabilizing the Sylow-five subgroup of `SL(2, 𝔽₅)`

The diagonal outer automorphism preserves the chosen upper-unitriangular
Sylow subgroup.  Every Sylow-five-stabilizing automorphism is inner by an
element of the exact normalizer, or this fixed outer automorphism followed
by such an inner automorphism.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeFiveForAutomorphismClassification :
    Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The diagonal outer automorphism, bundled in the stabilizer of the
chosen Sylow-five subgroup. -/
def specialLinearTwoFiveSylowFiveOuterAutomorphism :
    SylowAutStabilizer specialLinearTwoFiveSylowFive :=
  ⟨specialLinearTwoFiveDiagonalOuterAutomorphism, by
    apply Sylow.ext
    change
      (Subgroup.zpowers specialLinearTwoFive_orderFiveElement).map
          (specialLinearTwoFiveDiagonalOuterAutomorphism :
            SpecialLinearTwoFive →*
              SpecialLinearTwoFive) =
        Subgroup.zpowers specialLinearTwoFive_orderFiveElement
    rw [MonoidHom.map_zpowers]
    have hmap :
        specialLinearTwoFiveDiagonalOuterAutomorphism
            specialLinearTwoFive_orderFiveElement =
          specialLinearTwoFive_orderFiveElement ^ 2 := by
      decide
    change
      Subgroup.zpowers
          (specialLinearTwoFiveDiagonalOuterAutomorphism
            specialLinearTwoFive_orderFiveElement) =
        Subgroup.zpowers specialLinearTwoFive_orderFiveElement
    rw [hmap]
    apply le_antisymm
    · rw [Subgroup.zpowers_le]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
    · rw [Subgroup.zpowers_le]
      exact mem_zpowers_pow_iff.mpr <| by
        rw [orderOf_specialLinearTwoFive_orderFiveElement]
        decide⟩

@[simp]
theorem specialLinearTwoFiveSylowFiveOuterAutomorphism_normalizerA :
    specialLinearTwoFiveDiagonalOuterAutomorphism
        specialLinearTwoFiveSylowFiveNormalizerA =
      specialLinearTwoFiveSylowFiveNormalizerA ^ 7 := by
  decide

@[simp]
theorem specialLinearTwoFiveSylowFiveOuterAutomorphism_normalizerX :
    specialLinearTwoFiveDiagonalOuterAutomorphism
        specialLinearTwoFiveSylowFiveNormalizerX =
      specialLinearTwoFiveSylowFiveNormalizerX := by
  decide

/-- If an inner automorphism stabilizes the chosen Sylow subgroup, its
conjugating element lies in the exact normalizer. -/
theorem specialLinearTwoFive_mem_sylowFiveNormalizer_of_stabilizing_inner
    (g : SpecialLinearTwoFive)
    (a : SylowAutStabilizer specialLinearTwoFiveSylowFive)
    (ha : a.1 = MulAut.conj g) :
    g ∈ Subgroup.normalizer
      (specialLinearTwoFiveSylowFive :
        Set SpecialLinearTwoFive) := by
  apply
    (Subgroup.mem_normalizer_iff_map_conj_eq
      (H := (specialLinearTwoFiveSylowFive :
        Subgroup SpecialLinearTwoFive))).2
  have hstabilizes :=
    congrArg
      (fun Q : Sylow 5 SpecialLinearTwoFive =>
        (Q : Subgroup SpecialLinearTwoFive))
      a.2
  rw [ha] at hstabilizes
  exact hstabilizes

/-- Every Sylow-five-stabilizing automorphism is inner by an element of the
normalizer, or diagonal-outer followed by such an inner automorphism. -/
theorem
    specialLinearTwoFive_sylowFiveStabilizer_eq_inner_or_outer_inner
    (a : SylowAutStabilizer specialLinearTwoFiveSylowFive) :
    ∃ g : SylowNormalizer specialLinearTwoFiveSylowFive,
      a.1 = MulAut.conj g.1 ∨
        a.1 =
          specialLinearTwoFiveDiagonalOuterAutomorphism *
            MulAut.conj g.1 := by
  obtain ⟨g, hg | hg⟩ :=
    specialLinearTwoFive_automorphism_eq_inner_or_outer_inner a.1
  · exact
      ⟨⟨g,
          specialLinearTwoFive_mem_sylowFiveNormalizer_of_stabilizing_inner
            g a hg⟩,
        Or.inl hg⟩
  · let h : SpecialLinearTwoFive :=
      specialLinearTwoFiveDiagonalOuterAutomorphism.symm
          specialLinearTwoFiveOuterCorrection * g
    have hrewrite :
        specialLinearTwoFiveSylowThreeOuterAutomorphism *
              MulAut.conj g =
          specialLinearTwoFiveDiagonalOuterAutomorphism *
            MulAut.conj h := by
      simpa [h] using
        specialLinearTwoFiveSylowThreeOuter_mul_inner_eq_diagonalOuter_mul_inner
          g
    have haouter :
        a.1 =
          specialLinearTwoFiveDiagonalOuterAutomorphism *
            MulAut.conj h :=
      hg.trans hrewrite
    let b :
        SylowAutStabilizer specialLinearTwoFiveSylowFive :=
      specialLinearTwoFiveSylowFiveOuterAutomorphism⁻¹ * a
    have hb : b.1 = MulAut.conj h := by
      change
        specialLinearTwoFiveDiagonalOuterAutomorphism⁻¹ * a.1 =
          MulAut.conj h
      rw [haouter]
      simp
    exact
      ⟨⟨h,
          specialLinearTwoFive_mem_sylowFiveNormalizer_of_stabilizing_inner
            h b hb⟩,
        Or.inr haouter⟩

/-- Restriction of a stabilizing inner automorphism is the corresponding
inner automorphism of the exact normalizer. -/
theorem specialLinearTwoFive_sylowFiveNormalizerRestriction_eq_inner
    (a : SylowAutStabilizer specialLinearTwoFiveSylowFive)
    (g : SylowNormalizer specialLinearTwoFiveSylowFive)
    (ha : a.1 = MulAut.conj g.1) :
    SylowAutStabilizer.normalizerRestrictionHom
        specialLinearTwoFiveSylowFive a =
      MulAut.conj g := by
  apply DFunLike.ext _ _
  intro x
  apply Subtype.ext
  change a.1 x.1 = g.1 * x.1 * g.1⁻¹
  rw [ha]
  rfl

/-- Restriction respects the diagonal-outer-then-inner normal form. -/
theorem
    specialLinearTwoFive_sylowFiveNormalizerRestriction_eq_outer_inner
    (a : SylowAutStabilizer specialLinearTwoFiveSylowFive)
    (g : SylowNormalizer specialLinearTwoFiveSylowFive)
    (ha :
      a.1 =
        specialLinearTwoFiveDiagonalOuterAutomorphism *
          MulAut.conj g.1) :
    SylowAutStabilizer.normalizerRestrictionHom
        specialLinearTwoFiveSylowFive a =
      SylowAutStabilizer.normalizerRestrictionHom
          specialLinearTwoFiveSylowFive
          specialLinearTwoFiveSylowFiveOuterAutomorphism *
        MulAut.conj g := by
  apply DFunLike.ext _ _
  intro x
  apply Subtype.ext
  change
    a.1 x.1 =
      specialLinearTwoFiveDiagonalOuterAutomorphism
        (g.1 * x.1 * g.1⁻¹)
  rw [ha]
  rfl

end InductiveMcKay
end McKayConjecture
