import McKayConjecture.GroupTheory.SpecialLinearTwoFiveAutomorphisms
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# The general-linear central cover of `Aut(SL(2, 𝔽₅))`

Conjugation by `GL(2, 𝔽₅)` realizes every automorphism of
`SL(2, 𝔽₅)`.  Its kernel consists of scalar matrices and is therefore
central.  This file records that concrete central cover, together with
the representatives needed for the diagonal outer automorphism.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace McKayConjecture.GroupTheory

abbrev GeneralLinearTwoFive := GL (Fin 2) (ZMod 5)

def specialLinearTwoFiveInGeneralLinear :
    Subgroup GeneralLinearTwoFive :=
  (Matrix.GeneralLinearGroup.det :
    GeneralLinearTwoFive →* (ZMod 5)ˣ).ker

instance specialLinearTwoFiveInGeneralLinear_normal :
    specialLinearTwoFiveInGeneralLinear.Normal := by
  change
    (Matrix.GeneralLinearGroup.det :
      GeneralLinearTwoFive →* (ZMod 5)ˣ).ker.Normal
  infer_instance

def specialLinearTwoFiveEquivDetKernel :
    SpecialLinearTwoFive ≃*
      specialLinearTwoFiveInGeneralLinear where
  toFun g :=
    ⟨Matrix.SpecialLinearGroup.toGL g, by
      change
        Matrix.GeneralLinearGroup.det
            (Matrix.SpecialLinearGroup.toGL g) =
          1
      simp⟩
  invFun u :=
    ⟨(u.1 : Matrix (Fin 2) (Fin 2) (ZMod 5)),
      congrArg Units.val u.2⟩
  left_inv g := by
    apply Subtype.ext
    rfl
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    rfl

def generalLinearTwoFiveConjugation :
    GeneralLinearTwoFive →* MulAut SpecialLinearTwoFive :=
  (MulAut.congr specialLinearTwoFiveEquivDetKernel.symm).toMonoidHom.comp
    (MulAut.conjNormal :
      GeneralLinearTwoFive →*
        MulAut specialLinearTwoFiveInGeneralLinear)

@[simp]
theorem generalLinearTwoFiveConjugation_apply
    (u : GeneralLinearTwoFive)
    (g : SpecialLinearTwoFive) :
    (generalLinearTwoFiveConjugation u g :
        Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      (u : Matrix (Fin 2) (Fin 2) (ZMod 5)) * g.1 *
        (u⁻¹ : GeneralLinearTwoFive) := by
  change
    (↑(u *
        Matrix.SpecialLinearGroup.toGL g * u⁻¹) :
        Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      _
  rfl

@[simp]
theorem generalLinearTwoFiveConjugation_toGL
    (g : SpecialLinearTwoFive) :
    generalLinearTwoFiveConjugation
        (Matrix.SpecialLinearGroup.toGL g) =
      MulAut.conj g := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [generalLinearTwoFiveConjugation_apply]
  change
    (g.1 * x.1 *
        ((Matrix.SpecialLinearGroup.toGL g)⁻¹ :
          GeneralLinearTwoFive)) =
      g.1 * x.1 * (g⁻¹).1
  rw [show
    (Matrix.SpecialLinearGroup.toGL g)⁻¹ =
      Matrix.SpecialLinearGroup.toGL (g⁻¹) by
        simp]
  rfl

def specialLinearTwoFiveOuterGeneralLinear :
    GeneralLinearTwoFive :=
  ⟨specialLinearTwoFiveOuterDiagonal,
    specialLinearTwoFiveOuterDiagonalInv,
    specialLinearTwoFiveOuterDiagonal_mul_inv,
    specialLinearTwoFiveOuterDiagonal_inv_mul⟩

@[simp]
theorem generalLinearTwoFiveConjugation_outer :
    generalLinearTwoFiveConjugation
        specialLinearTwoFiveOuterGeneralLinear =
      specialLinearTwoFiveDiagonalOuterAutomorphism := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  rw [generalLinearTwoFiveConjugation_apply]
  change
    specialLinearTwoFiveOuterDiagonal * g.1 *
        specialLinearTwoFiveOuterDiagonalInv =
      specialLinearTwoFiveOuterDiagonal * g.1 *
        specialLinearTwoFiveOuterDiagonalInv
  rfl

def specialLinearTwoFiveSylowThreeOuterGeneralLinear :
    GeneralLinearTwoFive :=
  Matrix.SpecialLinearGroup.toGL
      specialLinearTwoFiveOuterCorrection *
    specialLinearTwoFiveOuterGeneralLinear

@[simp]
theorem generalLinearTwoFiveConjugation_sylowThreeOuter :
    generalLinearTwoFiveConjugation
        specialLinearTwoFiveSylowThreeOuterGeneralLinear =
      specialLinearTwoFiveSylowThreeOuterAutomorphism := by
  simp [specialLinearTwoFiveSylowThreeOuterGeneralLinear,
    specialLinearTwoFiveSylowThreeOuterAutomorphism]

theorem generalLinearTwoFiveConjugation_surjective :
    Function.Surjective generalLinearTwoFiveConjugation := by
  intro a
  obtain ⟨g, rfl | rfl⟩ :=
    specialLinearTwoFive_automorphism_eq_inner_or_outer_inner a
  · exact ⟨Matrix.SpecialLinearGroup.toGL g, by simp⟩
  · refine
      ⟨specialLinearTwoFiveSylowThreeOuterGeneralLinear *
          Matrix.SpecialLinearGroup.toGL g, ?_⟩
    simp

/-- The lower unitriangular matrix used to detect scalar matrices in the
kernel of the conjugation cover. -/
def specialLinearTwoFiveLowerUnipotent :
    SpecialLinearTwoFive :=
  ⟨!![(1 : ZMod 5), 0; 1, 1], by native_decide⟩

theorem generalLinearTwoFiveConjugation_ker_le_center :
    generalLinearTwoFiveConjugation.ker ≤
      Subgroup.center GeneralLinearTwoFive := by
  intro u hu
  have hfix (g : SpecialLinearTwoFive) :
      generalLinearTwoFiveConjugation u g = g := by
    have h :=
      DFunLike.congr_fun (MonoidHom.mem_ker.mp hu) g
    simpa using h
  have hcomm (g : SpecialLinearTwoFive) :
      u * Matrix.SpecialLinearGroup.toGL g =
        Matrix.SpecialLinearGroup.toGL g * u := by
    have hconj :
        u * Matrix.SpecialLinearGroup.toGL g * u⁻¹ =
          Matrix.SpecialLinearGroup.toGL g := by
      apply Units.ext
      change
        (u : Matrix (Fin 2) (Fin 2) (ZMod 5)) * g.1 *
            (u⁻¹ : GeneralLinearTwoFive) =
          g.1
      rw [← generalLinearTwoFiveConjugation_apply]
      exact congrArg Subtype.val (hfix g)
    calc
      u * Matrix.SpecialLinearGroup.toGL g =
          (u * Matrix.SpecialLinearGroup.toGL g * u⁻¹) * u := by
            group
      _ = Matrix.SpecialLinearGroup.toGL g * u := by
        rw [hconj]
  have hupper :=
    congrArg Units.val
      (hcomm specialLinearTwoFive_orderFiveElement)
  change
    (u : Matrix (Fin 2) (Fin 2) (ZMod 5)) *
        specialLinearTwoFive_orderFiveElement.1 =
      specialLinearTwoFive_orderFiveElement.1 *
        (u : Matrix (Fin 2) (Fin 2) (ZMod 5)) at hupper
  have hlower :=
    congrArg Units.val
      (hcomm specialLinearTwoFiveLowerUnipotent)
  change
    (u : Matrix (Fin 2) (Fin 2) (ZMod 5)) *
        specialLinearTwoFiveLowerUnipotent.1 =
      specialLinearTwoFiveLowerUnipotent.1 *
        (u : Matrix (Fin 2) (Fin 2) (ZMod 5)) at hlower
  have hc : (u : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = 0 := by
    have h :=
      congrArg
        (fun A : Matrix (Fin 2) (Fin 2) (ZMod 5) ↦ A 0 0)
        hupper
    simpa [specialLinearTwoFive_orderFiveElement,
      Matrix.mul_apply, Fin.sum_univ_two] using h
  have had :
      (u : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 =
        (u : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 := by
    have h :=
      congrArg
        (fun A : Matrix (Fin 2) (Fin 2) (ZMod 5) ↦ A 0 1)
        hupper
    simp [specialLinearTwoFive_orderFiveElement,
      Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have hb : (u : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = 0 := by
    have h :=
      congrArg
        (fun A : Matrix (Fin 2) (Fin 2) (ZMod 5) ↦ A 0 0)
        hlower
    simpa [specialLinearTwoFiveLowerUnipotent,
      Matrix.mul_apply, Fin.sum_univ_two] using h
  rw [Subgroup.mem_center_iff]
  intro v
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hb, had, mul_comm]

/-- The image of `SL(2, 𝔽₅)` in the general linear group is exactly the
kernel of the determinant. -/
theorem specialLinearTwoFive_toGL_range_eq_detKernel :
    (Matrix.SpecialLinearGroup.toGL :
      SpecialLinearTwoFive →* GeneralLinearTwoFive).range =
      specialLinearTwoFiveInGeneralLinear := by
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    change
      Matrix.GeneralLinearGroup.det
          (Matrix.SpecialLinearGroup.toGL g) =
        1
    simp
  · intro hu
    let x : specialLinearTwoFiveInGeneralLinear := ⟨u, hu⟩
    refine
      ⟨specialLinearTwoFiveEquivDetKernel.symm x, ?_⟩
    exact
      congrArg Subtype.val
        (specialLinearTwoFiveEquivDetKernel.apply_symm_apply x)

instance specialLinearTwoFive_toGL_range_normal :
    (Matrix.SpecialLinearGroup.toGL :
      SpecialLinearTwoFive →* GeneralLinearTwoFive).range.Normal := by
  rw [specialLinearTwoFive_toGL_range_eq_detKernel]
  infer_instance

/-- The quotient `GL(2, 𝔽₅)/SL(2, 𝔽₅)` is cyclic (indeed, it is the
four-element unit group of `𝔽₅`). -/
theorem specialLinearTwoFive_generalLinearQuotient_isCyclic :
    IsCyclic
      (GeneralLinearTwoFive ⧸
        (Matrix.SpecialLinearGroup.toGL :
          SpecialLinearTwoFive →* GeneralLinearTwoFive).range) := by
  let det :
      GeneralLinearTwoFive →* (ZMod 5)ˣ :=
    Matrix.GeneralLinearGroup.det
  let quotientEquiv :
      GeneralLinearTwoFive ⧸
          (Matrix.SpecialLinearGroup.toGL :
            SpecialLinearTwoFive →* GeneralLinearTwoFive).range ≃*
        (ZMod 5)ˣ :=
    (QuotientGroup.quotientMulEquivOfEq
      specialLinearTwoFive_toGL_range_eq_detKernel).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (φ := det) Matrix.GeneralLinearGroup.det_surjective)
  apply quotientEquiv.isCyclic.mpr
  exact ZMod.isCyclic_units_prime Nat.prime_five

end McKayConjecture.GroupTheory
