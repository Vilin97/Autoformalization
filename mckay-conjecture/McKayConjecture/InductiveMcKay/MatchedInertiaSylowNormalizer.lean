/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.MatchedInertiaRestriction
import McKayConjecture.InductiveMcKay.Normalizer

/-!
# A matched target inertia group as a source Sylow normalizer

Let `N ◁ G`, let `S` be a Sylow subgroup of `G`, and work in
`H = N_G(S)`.  Suppose an `H`-equivariant character equivalence matches a
character `theta` of `N` with a character of a normal subgroup `M ◁ H`.
If `S ≤ I_G(theta)`, the canonical matched-inertia embedding identifies
the target inertia group exactly with the normalizer of the induced Sylow
subgroup inside `I_G(theta)`.

This is a group-theoretic statement.  It uses only equivariance and
injectivity of the character equivalence; no projective representations or
factor sets occur.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace MatchedInertiaRestriction

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ}
variable (N : Subgroup G) [N.Normal]
variable (S : Sylow p G)
variable
  (M : Subgroup (Subgroup.normalizer (S : Set G)))
  [M.Normal]

/-- The target inertia group is canonically the normalizer of the Sylow
subgroup induced in the source inertia group.  On underlying elements this
is precisely the usual matched-inertia embedding. -/
def targetInertiaEquivSourceSylowNormalizer
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : Subgroup.normalizer (S : Set G))
        (chi : PPrimeIrreducibleCharacter N p),
        e (h • chi) = h • e chi)
    (theta : PPrimeIrreducibleCharacter N p)
    (hS :
      (S : Subgroup G) ≤
        IrreducibleCharacter.inertia N theta.1) :
    IrreducibleCharacter.inertia M (e theta).1 ≃*
      Subgroup.normalizer
        (sylowIn S
          (IrreducibleCharacter.inertia N theta.1) hS :
          Set (IrreducibleCharacter.inertia N theta.1)) where
  toFun b :=
    ⟨embedding N (Subgroup.normalizer (S : Set G))
        M e he theta b,
      by
        rw [normalizer_sylowIn_eq_subgroupOf
          S (IrreducibleCharacter.inertia N theta.1) hS]
        change
          ((b : Subgroup.normalizer (S : Set G)) : G) ∈
            Subgroup.normalizer (S : Set G)
        exact (b : Subgroup.normalizer (S : Set G)).property⟩
  invFun x := by
    have hxNormalizer :
        ((x.1 :
          IrreducibleCharacter.inertia N theta.1) : G) ∈
          Subgroup.normalizer (S : Set G) := by
      have hx :
          x.1 ∈
            (Subgroup.normalizer (S : Set G)).subgroupOf
              (IrreducibleCharacter.inertia N theta.1) := by
        rw [← normalizer_sylowIn_eq_subgroupOf
          S (IrreducibleCharacter.inertia N theta.1) hS]
        exact x.property
      exact hx
    let h : Subgroup.normalizer (S : Set G) :=
      ⟨((x.1 :
        IrreducibleCharacter.inertia N theta.1) : G),
        hxNormalizer⟩
    exact
      ⟨h,
        mem_target_inertia_of_mem_source_inertia
          N (Subgroup.normalizer (S : Set G))
          M e he theta h x.1.property⟩
  left_inv b := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' b c := by
    apply Subtype.ext
    exact
      map_mul
        (embedding N (Subgroup.normalizer (S : Set G))
          M e he theta) b c

omit [Finite G] in
@[simp]
theorem targetInertiaEquivSourceSylowNormalizer_apply_coe
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : Subgroup.normalizer (S : Set G))
        (chi : PPrimeIrreducibleCharacter N p),
        e (h • chi) = h • e chi)
    (theta : PPrimeIrreducibleCharacter N p)
    (hS :
      (S : Subgroup G) ≤
        IrreducibleCharacter.inertia N theta.1)
    (b : IrreducibleCharacter.inertia M (e theta).1) :
    (targetInertiaEquivSourceSylowNormalizer
        N S M e he theta hS b :
      IrreducibleCharacter.inertia N theta.1) =
      embedding N (Subgroup.normalizer (S : Set G))
        M e he theta b :=
  rfl

end MatchedInertiaRestriction
end InductiveMcKay
end McKayConjecture
