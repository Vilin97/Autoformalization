/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveAutomorphisms
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveSylowTwoNormalizer
import McKayConjecture.InductiveMcKay.AutomorphismStabilizer

/-!
# Automorphisms stabilizing the Sylow-two subgroup of `SL(2, 𝔽₅)`

The determinant-nonsquare diagonal automorphism preserves the chosen
quaternion Sylow subgroup and acts by inversion on the `C₃` quotient of its
binary-tetrahedral normalizer.  Combining this explicit outer automorphism
with the global inner-or-outer classification gives a normal form for every
element of `Aut(SL(2,5))_P`:

`conj(g)` or `outer * conj(g)`, with `g ∈ N_G(P)`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeTwoForAutomorphismClassification :
    Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The determinant-nonsquare diagonal outer automorphism, bundled in the
stabilizer of the chosen quaternion Sylow subgroup. -/
def specialLinearTwoFiveSylowTwoOuterAutomorphism :
    SylowAutStabilizer specialLinearTwoFiveSylowTwo :=
  ⟨specialLinearTwoFiveDiagonalOuterAutomorphism, by
    apply Sylow.ext
    ext x
    change
      x ∈ (specialLinearTwoFiveSylowTwo :
        Subgroup SpecialLinearTwoFive).map
          (specialLinearTwoFiveDiagonalOuterAutomorphism :
            SpecialLinearTwoFive →*
              SpecialLinearTwoFive) ↔
        x ∈ (specialLinearTwoFiveSylowTwo :
          Subgroup SpecialLinearTwoFive)
    simp only [Subgroup.mem_map]
    have hmem (z : SpecialLinearTwoFive) :
        z ∈ (specialLinearTwoFiveSylowTwo :
            Subgroup SpecialLinearTwoFive) ↔
          z ∈ specialLinearTwoFiveQuaternionElements := by
      change
        z ∈ (specialLinearTwoFiveSylowTwo :
          Set SpecialLinearTwoFive) ↔
            z ∈ specialLinearTwoFiveQuaternionElements
      rw [coe_specialLinearTwoFiveSylowTwo]
      rfl
    simp only [hmem]
    revert x
    native_decide⟩

/-- The restricted outer automorphism inverts the cyclic quotient
coordinate. -/
theorem
    specialLinearTwoFiveSylowTwoOuterAutomorphism_cyclicQuotient_symm
    (x : SpecialLinearTwoFiveSylowTwoNormalizer) :
    Multiplicative.toAdd
        (specialLinearTwoFiveSylowTwoNormalizerCyclicQuotient
          ((SylowAutStabilizer.normalizerRestrictionHom
              specialLinearTwoFiveSylowTwo
              specialLinearTwoFiveSylowTwoOuterAutomorphism).symm x)) =
      -Multiplicative.toAdd
        (specialLinearTwoFiveSylowTwoNormalizerCyclicQuotient x) := by
  revert x
  native_decide

/-- Rewrite the outer representative used by the global classification in
terms of the diagonal representative which stabilizes the Sylow-two
subgroup. -/
theorem specialLinearTwoFiveSylowThreeOuter_mul_inner_eq_diagonalOuter_mul_inner
    (g : SpecialLinearTwoFive) :
    specialLinearTwoFiveSylowThreeOuterAutomorphism *
          MulAut.conj g =
      specialLinearTwoFiveDiagonalOuterAutomorphism *
        MulAut.conj
          (specialLinearTwoFiveDiagonalOuterAutomorphism.symm
              specialLinearTwoFiveOuterCorrection * g) := by
  apply DFunLike.ext _ _
  intro x
  apply Subtype.ext
  simp only [
    specialLinearTwoFiveSylowThreeOuterAutomorphism,
    MulAut.mul_apply, MulAut.conj_apply]
  apply congrArg Subtype.val
  simp only [map_mul, map_inv,
    MulEquiv.apply_symm_apply]
  group
  rfl

/-- If an inner automorphism stabilizes the chosen Sylow subgroup, its
conjugating element lies in the exact normalizer. -/
theorem specialLinearTwoFive_mem_sylowTwoNormalizer_of_stabilizing_inner
    (g : SpecialLinearTwoFive)
    (a : SylowAutStabilizer specialLinearTwoFiveSylowTwo)
    (ha : a.1 = MulAut.conj g) :
    g ∈ Subgroup.normalizer
      (specialLinearTwoFiveSylowTwo :
        Set SpecialLinearTwoFive) := by
  apply
    (Subgroup.mem_normalizer_iff_map_conj_eq
      (H := (specialLinearTwoFiveSylowTwo :
        Subgroup SpecialLinearTwoFive))).2
  have hstabilizes :=
    congrArg
      (fun Q : Sylow 2 SpecialLinearTwoFive =>
        (Q : Subgroup SpecialLinearTwoFive))
      a.2
  rw [ha] at hstabilizes
  exact hstabilizes

/-- Every Sylow-two-stabilizing automorphism is inner by an element of the
normalizer, or the fixed diagonal outer automorphism followed by such an
inner automorphism. -/
theorem
    specialLinearTwoFive_sylowTwoStabilizer_eq_inner_or_outer_inner
    (a : SylowAutStabilizer specialLinearTwoFiveSylowTwo) :
    ∃ g : SpecialLinearTwoFiveSylowTwoNormalizer,
      a.1 = MulAut.conj g.1 ∨
        a.1 =
          specialLinearTwoFiveDiagonalOuterAutomorphism *
            MulAut.conj g.1 := by
  obtain ⟨g, hg | hg⟩ :=
    specialLinearTwoFive_automorphism_eq_inner_or_outer_inner a.1
  · exact
      ⟨⟨g,
          specialLinearTwoFive_mem_sylowTwoNormalizer_of_stabilizing_inner
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
        SylowAutStabilizer specialLinearTwoFiveSylowTwo :=
      specialLinearTwoFiveSylowTwoOuterAutomorphism⁻¹ * a
    have hb : b.1 = MulAut.conj h := by
      change
        specialLinearTwoFiveDiagonalOuterAutomorphism⁻¹ * a.1 =
          MulAut.conj h
      rw [haouter]
      simp
    exact
      ⟨⟨h,
          specialLinearTwoFive_mem_sylowTwoNormalizer_of_stabilizing_inner
            h b hb⟩,
        Or.inr haouter⟩

/-- Restriction of a stabilizing inner automorphism is the corresponding
inner automorphism of the exact normalizer. -/
theorem specialLinearTwoFive_sylowTwoNormalizerRestriction_eq_inner
    (a : SylowAutStabilizer specialLinearTwoFiveSylowTwo)
    (g : SpecialLinearTwoFiveSylowTwoNormalizer)
    (ha : a.1 = MulAut.conj g.1) :
    SylowAutStabilizer.normalizerRestrictionHom
        specialLinearTwoFiveSylowTwo a =
      MulAut.conj g := by
  apply DFunLike.ext _ _
  intro x
  apply Subtype.ext
  change a.1 x.1 = g.1 * x.1 * g.1⁻¹
  rw [ha]
  rfl

/-- Restriction respects the diagonal-outer-then-inner normal form. -/
theorem specialLinearTwoFive_sylowTwoNormalizerRestriction_eq_outer_inner
    (a : SylowAutStabilizer specialLinearTwoFiveSylowTwo)
    (g : SpecialLinearTwoFiveSylowTwoNormalizer)
    (ha :
      a.1 =
        specialLinearTwoFiveDiagonalOuterAutomorphism *
          MulAut.conj g.1) :
    SylowAutStabilizer.normalizerRestrictionHom
        specialLinearTwoFiveSylowTwo a =
      SylowAutStabilizer.normalizerRestrictionHom
          specialLinearTwoFiveSylowTwo
          specialLinearTwoFiveSylowTwoOuterAutomorphism *
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
