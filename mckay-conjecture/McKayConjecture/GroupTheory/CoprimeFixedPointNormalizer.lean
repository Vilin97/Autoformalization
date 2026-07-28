/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanCorrespondence

/-!
# Normalizer action on coprime fixed points

If `K` is normal in `G`, then every element normalizing a subgroup `P`
also normalizes `C_K(P) = K ∩ C_G(P)`.  This elementary observation gives
the conjugation automorphism on the target of the Glauberman
correspondence.
-/

namespace McKayConjecture

variable {G : Type} [Group G]

/-- The normalizer of `P` normalizes its fixed-point subgroup inside every
normal subgroup `K`. -/
theorem normalizer_le_normalizer_coprimeFixedPoints
    (K P : Subgroup G) [K.Normal] :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (coprimeFixedPoints K P : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg x hx
  refine ⟨(inferInstance : K.Normal).conj_mem x hx.1 g, ?_⟩
  change g * x * g⁻¹ ∈
    Subgroup.centralizer (P : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : g⁻¹ * y * g ∈ P :=
    (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mpr (by
      simpa [mul_assoc] using hy)
  have hcomm :
      (g⁻¹ * y * g) * x =
        x * (g⁻¹ * y * g) :=
    Subgroup.mem_centralizer_iff.mp hx.2
      (g⁻¹ * y * g) hy'
  have hconj :=
    congrArg (fun z : G => g * z * g⁻¹) hcomm
  simpa [mul_assoc] using hconj

/-- Conjugation by an element of `N_G(P)`, restricted to `C_K(P)`. -/
def coprimeFixedPointsNormalizerAction
    (K P : Subgroup G) [K.Normal]
    (g : Subgroup.normalizer (P : Set G)) :
    MulAut (coprimeFixedPoints K P) :=
  (coprimeFixedPoints K P).normalizerMonoidHom
    ⟨g, normalizer_le_normalizer_coprimeFixedPoints
      K P g.property⟩

@[simp]
theorem coprimeFixedPointsNormalizerAction_apply_coe
    (K P : Subgroup G) [K.Normal]
    (g : Subgroup.normalizer (P : Set G))
    (x : coprimeFixedPoints K P) :
    (coprimeFixedPointsNormalizerAction K P g x : G) =
      (g : G) * (x : G) * (g : G)⁻¹ :=
  rfl

end McKayConjecture
