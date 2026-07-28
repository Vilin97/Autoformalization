/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalar
import McKayConjecture.Character.CliffordCorrespondence

/-!
# Central scalars of irreducible constituents

If an irreducible representation of `G`, restricted along a homomorphism
`H → G`, contains an irreducible representation of `H`, then central
elements acting centrally on both sides have the same scalar on the two
representations.  The resulting cross-multiplied character-value identity
is the elementary mechanism by which Clifford assembly preserves prescribed
central scalars.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CliffordCorrespondence

variable {G H : Type}
variable [Group G] [Group H]

/-- A constituent of a restricted irreducible character has the same
normalized value on a pair of corresponding central elements. -/
theorem central_cross_of_liesOverAlong
    (φ : H →* G)
    (η : IrreducibleCharacter H)
    (χ : IrreducibleCharacter G)
    (hχ : LiesOverAlong φ η χ)
    (z : H)
    (hzH : z ∈ Subgroup.center H)
    (hzG : φ z ∈ Subgroup.center G) :
    χ.values (φ z) * (η.degree : ℂ) =
      η.values z * (χ.degree : ℂ) := by
  obtain ⟨f, hf⟩ :=
    (liesOverAlong_iff_exists_nonzero φ η χ).mp hχ
  let fRep :=
    (FDRep.forget₂HomLinearEquiv
      η.realization
      (FDRep.res φ χ.realization)).symm f
  let L :
      η.realization →ₗ[ℂ] χ.realization :=
    fRep.hom.toLinearMap
  have hfinjective : Function.Injective L := by
    intro x y hxy
    exact
      (fdRepHom_injective_of_nonzero_from_simple
        f hf) hxy
  letI : Nontrivial η.realization :=
    CliffordRestriction.nontrivial_of_simple η.realization
  obtain ⟨v : η.realization, hv⟩ :=
    exists_ne (0 : η.realization)
  have hfv : L v ≠ 0 := by
    intro hzero
    apply hv
    apply hfinjective
    exact hzero.trans L.map_zero.symm
  obtain ⟨c, hc⟩ :=
    χ.exists_realization_scalar_of_mem_center
      (φ z) hzG
  obtain ⟨d, hd⟩ :=
    η.exists_realization_scalar_of_mem_center
      z hzH
  have hintertwine :
      L (η.realization.ρ z v) =
        χ.realization.ρ (φ z) (L v) := by
    exact
      LinearMap.congr_fun
        (fRep.hom.isIntertwining' z) v
  have hscalar : d = c := by
    have hsmul : d • L v = c • L v := by
      have hmap : d • L v = L (d • v) :=
        (L.map_smul d v).symm
      have hsource :
          L (d • v) = L (η.realization.ρ z v) := by
        congr 1
        have hvd := LinearMap.congr_fun hd v
        simpa using hvd.symm
      have htarget :
          χ.realization.ρ (φ z) (L v) = c • L v := by
        have hvc := LinearMap.congr_fun hc (L v)
        have hscalarApply :
            (c • (LinearMap.id :
              Module.End ℂ χ.realization)) (L v) =
                c • L v := by
          rw [LinearMap.smul_apply, LinearMap.id_apply]
        exact hvc.trans hscalarApply
      exact hmap.trans (hsource.trans (hintertwine.trans htarget))
    exact (smul_left_injective ℂ hfv) hsmul
  rw [χ.values_eq_scalar_mul_degree (φ z) c hc,
    η.values_eq_scalar_mul_degree z d hd,
    hscalar]
  ring

/-- Subgroup-inclusion specialization.  An ambient-central element lying
in a subgroup is automatically central in that subgroup. -/
theorem central_cross_of_liesOverSubgroup
    (N : Subgroup G)
    (η : IrreducibleCharacter N)
    (χ : IrreducibleCharacter G)
    (hχ : LiesOverAlong N.subtype η χ)
    (z : N)
    (hzG : (z : G) ∈ Subgroup.center G) :
    χ.values (z : G) * (η.degree : ℂ) =
      η.values z * (χ.degree : ℂ) := by
  apply
    central_cross_of_liesOverAlong
      N.subtype η χ hχ z
  · rw [Subgroup.mem_center_iff]
    intro n
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hzG (n : G)
  · exact hzG

end CliffordCorrespondence
end McKayConjecture
