/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.PPrimeCore

/-!
# Full preimages of quotient subgroups

Let `N ◁ G` and let `R ≤ G / N`.  The full preimage of `R` contains
`N`, maps onto `R`, and its quotient by the internal copy of `N` is
canonically isomorphic to `R`.

The final specialization records that the full preimage of a Sylow
subgroup has a Sylow-group quotient.  These are the subgroup coordinates
used by Navarro's local--global extension criterion.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G]

/-- The full preimage in `G` of a subgroup of `G / N`. -/
abbrev quotientSubgroupPreimage
    (N : Subgroup G) [N.Normal]
    (R : Subgroup (G ⧸ N)) :
    Subgroup G :=
  R.comap (QuotientGroup.mk' N)

/-- The quotient kernel lies in every full preimage. -/
theorem normal_le_quotientSubgroupPreimage
    (N : Subgroup G) [N.Normal]
    (R : Subgroup (G ⧸ N)) :
    N ≤ quotientSubgroupPreimage N R := by
  intro n hn
  change QuotientGroup.mk' N n ∈ R
  have hnq :
      QuotientGroup.mk' N n = 1 :=
    (QuotientGroup.eq_one_iff n).mpr hn
  rw [hnq]
  exact R.one_mem

/-- The quotient map restricted from a full preimage to the chosen
quotient subgroup. -/
def quotientSubgroupPreimageProjection
    (N : Subgroup G) [N.Normal]
    (R : Subgroup (G ⧸ N)) :
    quotientSubgroupPreimage N R →* R :=
  ((QuotientGroup.mk' N).domRestrict
      (quotientSubgroupPreimage N R)).codRestrict
    R (fun x => x.2)

@[simp]
theorem quotientSubgroupPreimageProjection_apply
    (N : Subgroup G) [N.Normal]
    (R : Subgroup (G ⧸ N))
    (x : quotientSubgroupPreimage N R) :
    ((quotientSubgroupPreimageProjection N R x : R) :
        G ⧸ N) =
      QuotientGroup.mk' N (x : G) :=
  rfl

/-- The restricted quotient map is onto. -/
theorem quotientSubgroupPreimageProjection_surjective
    (N : Subgroup G) [N.Normal]
    (R : Subgroup (G ⧸ N)) :
    Function.Surjective
      (quotientSubgroupPreimageProjection N R) := by
  intro r
  obtain ⟨g, hg⟩ :=
    QuotientGroup.mk'_surjective N (r : G ⧸ N)
  let x : quotientSubgroupPreimage N R :=
    ⟨g, by
      change QuotientGroup.mk' N g ∈ R
      rw [hg]
      exact r.2⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hg

/-- The kernel of the restricted quotient map is the internal copy of
the original normal subgroup. -/
theorem ker_quotientSubgroupPreimageProjection
    (N : Subgroup G) [N.Normal]
    (R : Subgroup (G ⧸ N)) :
    (quotientSubgroupPreimageProjection N R).ker =
      N.subgroupOf (quotientSubgroupPreimage N R) := by
  ext x
  change
    quotientSubgroupPreimageProjection N R x = 1 ↔
      (x : G) ∈ N
  constructor
  · intro hx
    have hx' :=
      congrArg
        (fun y : R => (y : G ⧸ N)) hx
    change QuotientGroup.mk' N (x : G) = 1 at hx'
    exact (QuotientGroup.eq_one_iff (x : G)).mp hx'
  · intro hx
    apply Subtype.ext
    change QuotientGroup.mk' N (x : G) = 1
    exact (QuotientGroup.eq_one_iff (x : G)).mpr hx

/-- Noether's first isomorphism theorem for a full quotient-subgroup
preimage. -/
def quotientSubgroupPreimageQuotientEquiv
    (N : Subgroup G) [N.Normal]
    (R : Subgroup (G ⧸ N)) :
    quotientSubgroupPreimage N R ⧸
        N.subgroupOf (quotientSubgroupPreimage N R) ≃*
      R := by
  let f := quotientSubgroupPreimageProjection N R
  have hker :
      N.subgroupOf (quotientSubgroupPreimage N R) =
        f.ker :=
    (ker_quotientSubgroupPreimageProjection N R).symm
  have hrange : f.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      (quotientSubgroupPreimageProjection_surjective N R)
  exact
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      ((QuotientGroup.quotientKerEquivRange f).trans
        ((MulEquiv.subgroupCongr hrange).trans
          Subgroup.topEquiv))

@[simp]
theorem quotientSubgroupPreimageQuotientEquiv_mk
    (N : Subgroup G) [N.Normal]
    (R : Subgroup (G ⧸ N))
    (x : quotientSubgroupPreimage N R) :
    quotientSubgroupPreimageQuotientEquiv N R
        (QuotientGroup.mk'
          (N.subgroupOf (quotientSubgroupPreimage N R)) x) =
      quotientSubgroupPreimageProjection N R x :=
  rfl

/-- The quotient of a Sylow preimage by its kernel is a `p`-group. -/
theorem isPGroup_quotientSubgroupPreimage_sylow
    {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal]
    (R : Sylow p (G ⧸ N)) :
    IsPGroup p
      (quotientSubgroupPreimage N (R : Subgroup (G ⧸ N)) ⧸
        N.subgroupOf
          (quotientSubgroupPreimage N
            (R : Subgroup (G ⧸ N)))) :=
  R.isPGroup'.of_equiv
    (quotientSubgroupPreimageQuotientEquiv
      N (R : Subgroup (G ⧸ N))).symm

/-- A full quotient-subgroup preimage is a `p'`-group when both its
kernel and quotient subgroup are `p'`-groups. -/
theorem isPPrimeGroup_quotientSubgroupPreimage
    {p : ℕ}
    (N : Subgroup G) [N.Normal]
    (hN : IsPPrimeGroup p N)
    (R : Subgroup (G ⧸ N))
    (hR : IsPPrimeGroup p R) :
    IsPPrimeGroup p
      (quotientSubgroupPreimage N R) := by
  apply
    IsPPrimeGroup.comap_of_surjective
      (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
  · simpa only [QuotientGroup.ker_mk'] using hN
  · exact hR

/-- If `r ≠ p`, the full preimage of an `r`-Sylow subgroup over a
`p'`-kernel remains a `p'`-group. -/
theorem isPPrimeGroup_quotientSubgroupPreimage_sylow_of_ne
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    [Finite G]
    (hpr : p ≠ r)
    (N : Subgroup G) [N.Normal]
    (hN : IsPPrimeGroup p N)
    (R : Sylow r (G ⧸ N)) :
    IsPPrimeGroup p
      (quotientSubgroupPreimage N
        (R : Subgroup (G ⧸ N))) := by
  apply
    isPPrimeGroup_quotientSubgroupPreimage
      N hN (R : Subgroup (G ⧸ N))
  rw [IsPPrimeGroup, Sylow.card_eq_multiplicity]
  exact
    ((Nat.coprime_primes
      (show p.Prime from Fact.out)
      (show r.Prime from Fact.out)).mpr hpr).pow_right _

end GroupTheory
end McKayConjecture
