/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InnerOrbitReduction
import McKayConjecture.Character.PPrimeCliffordOrbit
import McKayConjecture.GroupTheory.EquivariantOrbitEquiv

/-!
# Transport of active Clifford orbits

Suppose that `N ◁ G`, that `H ≤ G`, and that `G = N H`.  Let `M ◁ H`.
An `H`-equivariant equivalence between the prime-to-`p` characters of
`N` and `M` induces an equivalence of active Clifford orbits as soon as
it preserves the exact activity predicate.

The proof keeps all three logically separate ingredients visible:

* inner conjugation by `N` is trivial on characters of `N`;
* consequently the `G`-orbit quotient is the `H`-orbit quotient when
  `G = N H`; and
* an equivariant equivalence descends to orbit quotients.

No assertion that every prime-to-`p` orbit is active is made.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordPartition

open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable (N H : Subgroup G) [N.Normal]
variable (M : Subgroup H) [M.Normal]
variable {p : ℕ}

/-- The predicate of lying over a Clifford orbit depends only on the
orbit, not on the chosen representative. -/
theorem liesOverOrbit_iff_of_quotient_mk_eq
    {A : Type} [Group A]
    (K : Subgroup A) [K.Normal]
    {θ φ : IrreducibleCharacter K}
    (horbit :
      (Quotient.mk'' θ :
          MulAction.orbitRel.Quotient A
            (IrreducibleCharacter K)) =
        Quotient.mk'' φ)
    (χ : IrreducibleCharacter A) :
    CliffordCorrespondence.LiesOverOrbit K θ χ ↔
      CliffordCorrespondence.LiesOverOrbit K φ χ := by
  obtain ⟨g, hg⟩ := Quotient.exact horbit
  change g • φ = θ at hg
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a * g, ?_⟩
    convert ha using 1
    change (a * g) • φ = a • θ
    rw [mul_smul, hg]
  · rintro ⟨a, ha⟩
    refine ⟨a * g⁻¹, ?_⟩
    convert ha using 1
    change (a * g⁻¹) • θ = a • φ
    rw [mul_smul, ← hg, inv_smul_smul]

/-- Prime-to-`p` Clifford blocks can be repackaged along an equality of
their orbit representatives. -/
def pPrimeOrbitBlockEquivOfQuotientMkEq
    {A : Type} [Group A]
    (K : Subgroup A) [K.Normal]
    {θ φ : IrreducibleCharacter K}
    (horbit :
      (Quotient.mk'' θ :
          MulAction.orbitRel.Quotient A
            (IrreducibleCharacter K)) =
        Quotient.mk'' φ)
    (p : ℕ) :
    CliffordCorrespondence.PPrimeIrreducibleCharactersOverOrbit
        K θ p ≃
      CliffordCorrespondence.PPrimeIrreducibleCharactersOverOrbit
        K φ p :=
  (Equiv.refl (IrreducibleCharacter A)).subtypeEquiv
    (fun χ ↦
      liesOverOrbit_iff_of_quotient_mk_eq
        K horbit χ) |>.subtypeEquiv (fun _ ↦ Iff.rfl)

@[simp]
theorem pPrimeOrbitBlockEquivOfQuotientMkEq_apply_coe
    {A : Type} [Group A]
    (K : Subgroup A) [K.Normal]
    {θ φ : IrreducibleCharacter K}
    (horbit :
      (Quotient.mk'' θ :
          MulAction.orbitRel.Quotient A
            (IrreducibleCharacter K)) =
        Quotient.mk'' φ)
    (p : ℕ)
    (χ :
      CliffordCorrespondence.PPrimeIrreducibleCharactersOverOrbit
        K θ p) :
    (pPrimeOrbitBlockEquivOfQuotientMkEq
      K horbit p χ).1.1 =
        χ.1.1 :=
  rfl

/-- Restrict an activity-preserving equivalence of prime-to-`p`
characters to the exact active subtypes. -/
def activePPrimeEquivOfActivityIff
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (hactive :
      ∀ θ : PPrimeIrreducibleCharacter N p,
        @IsActivePPrimeCharacter G _ N _ p θ ↔
          @IsActivePPrimeCharacter H _ M _ p (e θ)) :
    @ActivePPrimeIrreducibleCharacter G _ N _ p ≃
      @ActivePPrimeIrreducibleCharacter H _ M _ p where
  toFun θ := ⟨e θ.1, (hactive θ.1).mp θ.2⟩
  invFun φ :=
    ⟨e.symm φ.1, by
      have h :=
        (hactive (e.symm φ.1)).mpr
          (by simpa using φ.2)
      exact h⟩
  left_inv θ := by
    apply Subtype.ext
    exact e.symm_apply_apply θ.1
  right_inv φ := by
    apply Subtype.ext
    exact e.apply_symm_apply φ.1

@[simp]
theorem activePPrimeEquivOfActivityIff_apply_coe
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (hactive :
      ∀ θ : PPrimeIrreducibleCharacter N p,
        @IsActivePPrimeCharacter G _ N _ p θ ↔
          @IsActivePPrimeCharacter H _ M _ p (e θ))
    (θ : @ActivePPrimeIrreducibleCharacter G _ N _ p) :
    (activePPrimeEquivOfActivityIff
      N H M e hactive θ).1 =
        e θ.1 :=
  rfl

@[simp]
theorem activePPrimeEquivOfActivityIff_symm_apply_coe
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (hactive :
      ∀ θ : PPrimeIrreducibleCharacter N p,
        @IsActivePPrimeCharacter G _ N _ p θ ↔
          @IsActivePPrimeCharacter H _ M _ p (e θ))
    (φ : @ActivePPrimeIrreducibleCharacter H _ M _ p) :
    ((activePPrimeEquivOfActivityIff
      N H M e hactive).symm φ).1 =
        e.symm φ.1 :=
  rfl

/-- The restricted active-character equivalence is equivariant whenever
the original prime-to-`p` character equivalence is equivariant. -/
theorem activePPrimeEquivOfActivityIff_map_smul
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (θ : PPrimeIrreducibleCharacter N p),
        e (h • θ) = h • e θ)
    (hactive :
      ∀ θ : PPrimeIrreducibleCharacter N p,
        @IsActivePPrimeCharacter G _ N _ p θ ↔
          @IsActivePPrimeCharacter H _ M _ p (e θ))
    (h : H)
    (θ : @ActivePPrimeIrreducibleCharacter G _ N _ p) :
    activePPrimeEquivOfActivityIff N H M e hactive (h • θ) =
      h • activePPrimeEquivOfActivityIff N H M e hactive θ := by
  apply Subtype.ext
  exact he h θ.1

/-- Replacing the ambient `G`-action by the restricted `H`-action does
not change the orbit quotient of active prime-to-`p` characters when
`G = N H`. -/
def activePPrimeOrbitQuotientEquivSubgroupOfSupEqTop
    (hsup : N ⊔ H = ⊤) :
    MulAction.orbitRel.Quotient G
        (ActivePPrimeIrreducibleCharacter N p) ≃
      MulAction.orbitRel.Quotient H
        (ActivePPrimeIrreducibleCharacter N p) :=
  GroupTheory.orbitQuotientEquivSubgroupOfProductOfTrivial
    N H
    (fun g ↦ by
      have hg : g ∈ N ⊔ H := by
        rw [hsup]
        exact Subgroup.mem_top g
      obtain ⟨n, hn, h, hh, hnh⟩ :=
        Subgroup.mem_sup_of_normal_left.mp hg
      exact ⟨⟨n, hn⟩, ⟨h, hh⟩, hnh⟩)
    (fun n θ ↦ by
      apply Subtype.ext
      exact
        PPrimeIrreducibleCharacter.normalSubgroup_smul_eq
          N p n θ.1)

@[simp]
theorem activePPrimeOrbitQuotientEquivSubgroupOfSupEqTop_mk
    (hsup : N ⊔ H = ⊤)
    (θ : ActivePPrimeIrreducibleCharacter N p) :
    activePPrimeOrbitQuotientEquivSubgroupOfSupEqTop
        N H (p := p) hsup (Quotient.mk'' θ) =
      Quotient.mk'' θ :=
  rfl

/-- An equivariant, activity-preserving equivalence of prime-to-`p`
normal-subgroup characters induces an equivalence of the exact active
Clifford orbit spaces.

The source active orbits use the ambient group `G`; the target active
orbits use the subgroup `H`, in which `M` is normal. -/
def activeOrbitEquivOfEquivariantActivityIff
    (hsup : N ⊔ H = ⊤)
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (θ : PPrimeIrreducibleCharacter N p),
        e (h • θ) = h • e θ)
    (hactive :
      ∀ θ : PPrimeIrreducibleCharacter N p,
        @IsActivePPrimeCharacter G _ N _ p θ ↔
          @IsActivePPrimeCharacter H _ M _ p (e θ)) :
    ActiveOrbit N p ≃ ActiveOrbit M p :=
  (activeOrbitEquivActivePPrimeOrbitSpace N p).trans <|
    (activePPrimeOrbitQuotientEquivSubgroupOfSupEqTop
      N H (p := p) hsup).trans <|
      (GroupTheory.equivariantOrbitQuotientEquiv
        (activePPrimeEquivOfActivityIff
          N H M e hactive)
        (activePPrimeEquivOfActivityIff_map_smul
          N H M e he hactive)).trans <|
        (activeOrbitEquivActivePPrimeOrbitSpace M p).symm

/-- The induced active-orbit equivalence sends an active character
representative to the orbit of its image. -/
@[simp]
theorem activeOrbitEquivOfEquivariantActivityIff_apply_coe
    (hsup : N ⊔ H = ⊤)
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (θ : PPrimeIrreducibleCharacter N p),
        e (h • θ) = h • e θ)
    (hactive :
      ∀ θ : PPrimeIrreducibleCharacter N p,
        @IsActivePPrimeCharacter G _ N _ p θ ↔
          @IsActivePPrimeCharacter H _ M _ p (e θ))
    (q : ActiveOrbit N p) :
    (activeOrbitEquivOfEquivariantActivityIff
      N H M hsup e he hactive q).1 =
        (Quotient.mk'' (e (q.pPrimeOut N)).1 :
          OrbitSpace M) :=
  rfl

end CliffordPartition
end McKayConjecture
