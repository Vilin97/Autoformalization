/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordEquivalence
import McKayConjecture.GroupTheory.PPrimeCore

/-!
# Characteristic subgroup copies inside an inertia group

Let `N ◁ G`, let `theta` be an irreducible character of `N`, and write
`I = I_G(theta)`.  The canonical copy of `N` in `I` is normal.  Hence every
characteristic subgroup `K` of `N` has a canonical normal copy in `I`.

This file packages that two-stage transport.  It also records preservation
of joins and of the prime-to-`p` property.  The intended application is the
canonical `p'`-core used in the ordinary Okuyama--Wajima argument.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordEquivalence

open CliffordCorrespondence
open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal]
variable (theta : IrreducibleCharacter N)

/-- Transport a subgroup of `N` through the canonical copy of `N` in the
inertia group. -/
def inertiaSubgroupCopy (K : Subgroup N) :
    Subgroup (IrreducibleCharacter.inertia N theta) :=
  let N' := inertiaNormalCopy N theta
  (K.map (inertiaNormalCopyEquiv N theta).symm.toMonoidHom).map N'.subtype

/-- The canonical equivalence from a subgroup to its inertia-group copy. -/
def inertiaSubgroupCopyEquiv (K : Subgroup N) :
    K ≃* inertiaSubgroupCopy N theta K :=
  let N' := inertiaNormalCopy N theta
  ((inertiaNormalCopyEquiv N theta).symm.subgroupMap K).trans
    ((K.map
      (inertiaNormalCopyEquiv N theta).symm.toMonoidHom).equivMapOfInjective
        N'.subtype N'.subtype_injective)

omit [Finite G] in
@[simp]
theorem inertiaSubgroupCopyEquiv_apply_coe
    (K : Subgroup N) (x : K) :
    ((inertiaSubgroupCopyEquiv N theta K x :
        inertiaSubgroupCopy N theta K) :
      IrreducibleCharacter.inertia N theta) =
      inertiaInclusion N theta x :=
  rfl

omit [Finite G] in
/-- Transporting a join into the inertia group gives the join of the two
transported copies. -/
theorem inertiaSubgroupCopy_sup
    (K L : Subgroup N) :
    inertiaSubgroupCopy N theta (K ⊔ L) =
      inertiaSubgroupCopy N theta K ⊔
        inertiaSubgroupCopy N theta L := by
  simp only [inertiaSubgroupCopy, Subgroup.map_sup]

omit [Finite G] in
/-- The copy of the whole of `N` is the usual inertia normal copy. -/
theorem inertiaSubgroupCopy_top :
    inertiaSubgroupCopy N theta ⊤ =
      inertiaNormalCopy N theta := by
  let N' := inertiaNormalCopy N theta
  change
    ((⊤ : Subgroup N).map
        (inertiaNormalCopyEquiv N theta).symm.toMonoidHom).map N'.subtype =
      N'
  rw [Subgroup.map_top_of_surjective
    (inertiaNormalCopyEquiv N theta).symm.toMonoidHom
    (inertiaNormalCopyEquiv N theta).symm.surjective]
  ext x
  simp

omit [Finite G] in
/-- A generating pair in `N` gives a generating pair for its canonical
normal copy in the inertia group. -/
theorem inertiaSubgroupCopy_sup_eq_normalCopy
    {K L : Subgroup N}
    (hKL : K ⊔ L = ⊤) :
    inertiaSubgroupCopy N theta K ⊔
        inertiaSubgroupCopy N theta L =
      inertiaNormalCopy N theta := by
  rw [← inertiaSubgroupCopy_sup, hKL,
    inertiaSubgroupCopy_top]

/-- A characteristic subgroup remains characteristic after relabelling
the ambient group by a multiplicative equivalence. -/
theorem characteristic_map_mulEquiv
    {A B : Type} [Group A] [Group B]
    (K : Subgroup A) [K.Characteristic]
    (e : A ≃* B) :
    (K.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro phi y hy
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨x, hx, hxz⟩ := hz
  let psi : A ≃* A :=
    (e.trans phi).trans e.symm
  have hpsi :
      psi x ∈ K :=
    Subgroup.characteristic_iff_map_le.mp
      (inferInstance : K.Characteristic) psi
      ⟨x, hx, rfl⟩
  refine ⟨psi x, hpsi, ?_⟩
  calc
    e (psi x) = phi (e x) := by simp [psi]
    _ = phi z := congrArg phi hxz
    _ = y := hzy

/-- The inertia-group copy of a characteristic subgroup is normal in the
whole inertia group. -/
instance inertiaSubgroupCopy_normal
    (K : Subgroup N) [K.Characteristic] :
    (inertiaSubgroupCopy N theta K).Normal := by
  let N' := inertiaNormalCopy N theta
  let K' :=
    K.map (inertiaNormalCopyEquiv N theta).symm.toMonoidHom
  letI : K'.Characteristic :=
    characteristic_map_mulEquiv K
      (inertiaNormalCopyEquiv N theta).symm
  change (K'.map N'.subtype).Normal
  infer_instance

omit [Finite G] in
/-- Prime-to-`p` order is preserved by passage to the inertia-group copy. -/
theorem inertiaSubgroupCopy_isPPrimeGroup
    {p : ℕ} (K : Subgroup N)
    (hK : IsPPrimeGroup p K) :
    IsPPrimeGroup p (inertiaSubgroupCopy N theta K) :=
  hK.of_equiv (inertiaSubgroupCopyEquiv N theta K)

end CliffordEquivalence
end McKayConjecture
