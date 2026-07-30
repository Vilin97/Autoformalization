/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaFullFixedOuterCoordinates
import McKayConjecture.Character.OkuyamaWajimaFullFixedOuterIndex

/-!
# Ambient normality of the full-fixed source group

In the full-fixed Okuyama--Wajima branch, let `M` be the canonical
complement and let `U ◁ M` centralize the Sylow subgroup `P`.  The
source group `U K` is normal not only in the middle group `M K`, but in
the whole ambient group.

Indeed, `P` normalizes `U K`, `M K` normalizes `U K`, and the outer
factorization theorem gives `G = P (M K)`.  This small observation lets
the ordinary normalizer-equivariance theorem for the Glauberman
correspondence be applied directly to `U K`.
-/

noncomputable section

namespace McKayConjecture
namespace OkuyamaWajimaFullFixedSourceNormality

open GroupTheory
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable
  (hK : IsPPrimeGroup p K)
  (hKP : (K ⊔ (P : Subgroup G)).Normal)

/-- The selected source product `U K` is ambient normal in the
full-fixed coordinates. -/
theorem source_normal
    (U : Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hUnormal :
      (U.subgroupOf
        (okuyamaWajimaProperBranchComplement K P hK hKP)).Normal)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G)) :
    (U ⊔ K : Subgroup G).Normal := by
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let H : Subgroup G := M ⊔ K
  have hPnormalizes :
      (P : Subgroup G) ≤
        Subgroup.normalizer ((U ⊔ K : Subgroup G) : Set G) :=
    OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
      (P : Subgroup G) K U hcentral
  have hHnormalizes :
      H ≤ Subgroup.normalizer ((U ⊔ K : Subgroup G) : Set G) := by
    exact sup_le
      (OkuyamaWajimaFullFixedOuterCoordinates.M_le_normalizer_source
        K M U hUM hUnormal)
      (le_sup_right.trans Subgroup.le_normalizer)
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  intro g _hg
  have hg :
      g ∈ ((P : Subgroup G) : Set G) * (H : Set G) := by
    rw [
      OkuyamaWajimaFullFixedOuterIndex.sylow_mul_okuyamaWajimaFullFixedMiddle_eq_top
        K P hK hKP]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := hg
  exact
    (Subgroup.normalizer ((U ⊔ K : Subgroup G) : Set G)).mul_mem
      (hPnormalizes hx) (hHnormalizes hy)

end OkuyamaWajimaFullFixedSourceNormality
end McKayConjecture
