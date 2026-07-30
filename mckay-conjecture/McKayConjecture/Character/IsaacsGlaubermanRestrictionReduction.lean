/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordPartition
import McKayConjecture.Character.GlaubermanActionOrbitSum
import McKayConjecture.Character.GlaubermanActionStrong
import McKayConjecture.Character.IsaacsGlaubermanRestriction
import McKayConjecture.Character.RestrictionMultiplicityDegree
import McKayConjecture.Character.RestrictionMultiplicityTransitivity
import McKayConjecture.GroupTheory.PGroupInvariantSum
import Mathlib.Algebra.BigOperators.ModEq

/-!
# Numerical reduction of Isaacs's Glauberman restriction theorem

For a `p`-group `S`, the proof of Isaacs, Theorem 13.29, compares two
computations of the multiplicity

`[χ ↓ (N^S), θ*]`.

Restriction through `G^S` gives, modulo `p`,

`[χ ↓ (N^S), θ*] ≡ [χ ↓ G^S, χ*] [χ* ↓ N^S, θ*]`,

whereas restriction through `N`, followed by the fixed-point orbit
congruence, gives

`[χ ↓ (N^S), θ*] ≡ [χ ↓ N, θ] [θ ↓ N^S, θ*]`.

The two factors selecting `χ*` and `θ*` are prime to `p`.  Consequently
the source and target normal-restriction multiplicities are simultaneously
prime to `p`.  The last step in the printed proof uses the standard
Clifford divisibility fact that a nonzero multiplicity in the restriction
of an irreducible character to a normal subgroup divides the ambient
degree.

This file formalizes the two congruences, proves the isolated Clifford
divisibility milestone from the existing conjugacy and restriction-degree
APIs, and thereby discharges the exact
`IsaacsGlaubermanRestrictionInput`.

## Reference

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 13.29,
  especially equations (1) and (2) in its proof.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture

open CliffordCorrespondence

namespace IsaacsGlaubermanRestrictionReduction

variable {S G : Type}
variable [Group S] [Group G] [Finite S] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (N : Subgroup G) [N.Normal]
variable [MulDistribMulAction S G]
variable [MulDistribMulAction S N]
variable
  (hsmul : ∀ (s : S) (n : N),
    ((s • n : N) : G) = s • (n : G))

local instance irreducibleCharacterActionG :
    MulAction S (IrreducibleCharacter G) :=
  actionIrreducibleCharacterMulAction S G

local instance irreducibleCharacterActionN :
    MulAction S (IrreducibleCharacter N) :=
  actionIrreducibleCharacterMulAction S N

/-! ## Fixed-point and action coordinates -/

/-- The two routes from `N^S` to `G` are literally the same homomorphism. -/
theorem fixedNormalInclusion_then_ambient_eq_normal_then_fixed :
    (actionFixedPointsInclusion S G).comp
        (IsaacsGlaubermanRestriction.fixedNormalInclusion
          N hsmul) =
      N.subtype.comp (actionFixedPointsInclusion S N) := by
  ext n
  rfl

/-- Simultaneously acting on a normal-subgroup character and an ambient
character preserves normal restriction multiplicity. -/
theorem restrictionMultiplicity_action_normal
    (hsmul : ∀ (s : S) (n : N),
      ((s • n : N) : G) = s • (n : G))
    (s : S)
    (eta : IrreducibleCharacter N)
    (chi : IrreducibleCharacter G) :
    restrictionMultiplicity N.subtype (s • eta) (s • chi) =
      restrictionMultiplicity N.subtype eta chi := by
  let eG : G ≃* G :=
    (MulDistribMulAction.toMulAut S G s).symm
  let eN : N ≃* N :=
    (MulDistribMulAction.toMulAut S N s).symm
  have hcomm :
      eG.toMonoidHom.comp N.subtype =
        N.subtype.comp eN.toMonoidHom := by
    ext n
    exact (hsmul s⁻¹ n).symm
  exact
    restrictionMultiplicity_comap_equiv
      eG eN N.subtype N.subtype hcomm eta chi

/-- Fixing the ambient character leaves normal restriction multiplicity
constant on `S`-orbits of normal-subgroup characters. -/
theorem restrictionMultiplicity_action_normal_of_invariant
    (hsmul : ∀ (s : S) (n : N),
      ((s • n : N) : G) = s • (n : G))
    (chi :
      ActionInvariantPPrimeIrreducibleCharacter S G p)
    (s : S)
    (eta : IrreducibleCharacter N) :
    restrictionMultiplicity N.subtype (s • eta) chi.1.1 =
      restrictionMultiplicity N.subtype eta chi.1.1 := by
  have hfixed : s • chi.1.1 = chi.1.1 := by
    apply
      (mem_actionIrreducibleCharacter_fixedPoints_iff
        S G chi.1.1).2
    exact chi.2
  calc
    restrictionMultiplicity N.subtype (s • eta) chi.1.1 =
        restrictionMultiplicity N.subtype
          (s • eta) (s • chi.1.1) := by
      rw [hfixed]
    _ =
        restrictionMultiplicity N.subtype eta chi.1.1 :=
      restrictionMultiplicity_action_normal
        N hsmul s eta chi.1.1

/-! ## Strong uniqueness is automatic on a `p'`-group -/

/-- On a `p'`-group every irreducible fixed-point character has
prime-to-`p` degree, so the ordinary action-level Glauberman interface
already has uniqueness among all irreducible target characters. -/
def strongOfIsPPrimeGroup
    {A : Type} [Group A] [Finite A]
    [MulDistribMulAction S A]
    (d : ActionGlaubermanCorrespondence S A p)
    (hA : GroupTheory.IsPPrimeGroup p A) :
    StrongActionGlaubermanCorrespondence S A p where
  characterEquiv := d.characterEquiv
  multiplicity_isPPrime := d.multiplicity_isPPrime
  eq_correspondent_of_multiplicity_isPPrime := by
    intro chi eta heta
    let etaP :
        PPrimeIrreducibleCharacter
          (FixedPoints.subgroup S A) p :=
      ⟨eta,
        IsaacsGlaubermanRestriction.isPPrimeDegree_of_isPPrimeGroup
          (hA.to_subgroup (FixedPoints.subgroup S A)) eta⟩
    exact congrArg Subtype.val
      (d.eq_correspondent_of_multiplicity_isPPrime
        chi etaP heta)

/-- Hence every non-correspondent fixed-point character has restriction
multiplicity divisible by `p`. -/
theorem multiplicity_dvd_of_ne_of_isPPrimeGroup
    {A : Type} [Group A] [Finite A]
    [MulDistribMulAction S A]
    (d : ActionGlaubermanCorrespondence S A p)
    (hA : GroupTheory.IsPPrimeGroup p A)
    (chi :
      ActionInvariantPPrimeIrreducibleCharacter S A p)
    (eta : IrreducibleCharacter
      (FixedPoints.subgroup S A))
    (hne : eta ≠ (d.characterEquiv chi).1) :
    p ∣
      restrictionMultiplicity
        (actionFixedPointsInclusion S A)
        eta chi.1.1 :=
  (strongOfIsPPrimeGroup d hA).multiplicity_dvd_of_ne
    chi eta hne

/-! ## Equation (1): restriction through the ambient fixed group -/

/-- The first congruence in the proof of Isaacs 13.29.  In restriction
through `G^S`, every intermediate irreducible character other than `chi*`
has multiplicity divisible by `p`. -/
theorem directFixedRestriction_modEq_ambientCorrespondentProduct
    (dG : ActionGlaubermanCorrespondence S G p)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (chi :
      ActionInvariantPPrimeIrreducibleCharacter S G p)
    (phi :
      IrreducibleCharacter (FixedPoints.subgroup S N)) :
    restrictionMultiplicity
        ((actionFixedPointsInclusion S G).comp
          (IsaacsGlaubermanRestriction.fixedNormalInclusion
            N hsmul))
        phi chi.1.1 ≡
      restrictionMultiplicity
          (IsaacsGlaubermanRestriction.fixedNormalInclusion
            N hsmul)
          phi (dG.characterEquiv chi).1 *
        restrictionMultiplicity
          (actionFixedPointsInclusion S G)
          (dG.characterEquiv chi).1 chi.1.1
        [MOD p] := by
  classical
  letI :
      Fintype
        (IrreducibleCharacter
          (FixedPoints.subgroup S G)) :=
    Fintype.ofFinite _
  rw [restrictionMultiplicity_comp]
  apply Nat.sum_modEq_single
  · intro hnot
    exact (hnot (Finset.mem_univ (dG.characterEquiv chi).1)).elim
  · intro eta _ heta
    apply Nat.modEq_zero_iff_dvd.mpr
    exact
      dvd_mul_of_dvd_right
        (multiplicity_dvd_of_ne_of_isPPrimeGroup
          dG hG chi eta heta)
        _

/-! ## Equation (2): restriction through the normal subgroup -/

/-- The product occurring in the restriction-transitivity formula through
`N`, with a fixed character of `N^S` in the first slot. -/
def normalRestrictionProduct
    (phi : IrreducibleCharacter
      (FixedPoints.subgroup S N))
    (chi : IrreducibleCharacter G)
    (eta : IrreducibleCharacter N) : ℕ :=
  restrictionMultiplicity
      (actionFixedPointsInclusion S N)
      phi eta *
    restrictionMultiplicity N.subtype eta chi

/-- A fixed irreducible character of a `p'`-group, packaged in the source
type of the action-level Glauberman correspondence. -/
def invariantPPrimeCharacterOfFixedPoint
    (hN : GroupTheory.IsPPrimeGroup p N)
    (eta :
      MulAction.fixedPoints S
        (IrreducibleCharacter N)) :
    ActionInvariantPPrimeIrreducibleCharacter S N p :=
  ⟨⟨eta.1,
      IsaacsGlaubermanRestriction.isPPrimeDegree_of_isPPrimeGroup
        hN eta.1⟩,
    (mem_actionIrreducibleCharacter_fixedPoints_iff
      S N eta.1).1 eta.2⟩

@[simp]
theorem invariantPPrimeCharacterOfFixedPoint_coe
    (hN : GroupTheory.IsPPrimeGroup p N)
    (eta :
      MulAction.fixedPoints S
        (IrreducibleCharacter N)) :
    (invariantPPrimeCharacterOfFixedPoint N hN eta).1.1 =
      eta.1 :=
  rfl

/-- Packaging fixed characters of a `p'`-group is injective. -/
theorem invariantPPrimeCharacterOfFixedPoint_injective
    (hN : GroupTheory.IsPPrimeGroup p N) :
    Function.Injective
      (invariantPPrimeCharacterOfFixedPoint
        (S := S) (p := p) N hN) := by
  intro eta zeta heq
  apply Subtype.ext
  exact congrArg
    (fun x :
      ActionInvariantPPrimeIrreducibleCharacter S N p ↦
        x.1.1)
    heq

/-- The fixed point corresponding to an already invariant character. -/
def fixedPointOfInvariantPPrimeCharacter
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    MulAction.fixedPoints S
      (IrreducibleCharacter N) :=
  ⟨theta.1.1,
    (mem_actionIrreducibleCharacter_fixedPoints_iff
      S N theta.1.1).2 theta.2⟩

@[simp]
theorem invariantPPrimeCharacterOfFixedPoint_fixedPointOfInvariant
    (hN : GroupTheory.IsPPrimeGroup p N)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    invariantPPrimeCharacterOfFixedPoint N hN
        (fixedPointOfInvariantPPrimeCharacter N theta) =
      theta := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- On the fixed-point sum, every summand other than the one indexed by
`theta` is zero modulo `p`.  This is the uniqueness step in equation (2)
of Isaacs's proof. -/
theorem fixedPoint_normalRestrictionProduct_sum_modEq_single
    (dN : ActionGlaubermanCorrespondence S N p)
    (hN : GroupTheory.IsPPrimeGroup p N)
    (chi : IrreducibleCharacter G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    letI := Fintype.ofFinite
      (MulAction.fixedPoints S
        (IrreducibleCharacter N))
    (∑ eta :
        MulAction.fixedPoints S
          (IrreducibleCharacter N),
      normalRestrictionProduct N
        (dN.characterEquiv theta).1 chi eta.1) ≡
      normalRestrictionProduct N
        (dN.characterEquiv theta).1 chi theta.1.1
      [MOD p] := by
  classical
  letI :
      Fintype
        (MulAction.fixedPoints S
          (IrreducibleCharacter N)) :=
    Fintype.ofFinite _
  let thetaFixed :=
    fixedPointOfInvariantPPrimeCharacter N theta
  apply Nat.sum_modEq_single
      (s := Finset.univ)
      (a := thetaFixed)
  · intro hnot
    exact (hnot (Finset.mem_univ thetaFixed)).elim
  · intro eta _ heta
    apply Nat.modEq_zero_iff_dvd.mpr
    apply dvd_mul_of_dvd_left
    · let etaInvariant :=
        invariantPPrimeCharacterOfFixedPoint N hN eta
      have hetaInvariant : etaInvariant ≠ theta := by
        intro heq
        apply heta
        exact
          invariantPPrimeCharacterOfFixedPoint_injective N hN
            (heq.trans
              (invariantPPrimeCharacterOfFixedPoint_fixedPointOfInvariant
                N hN theta).symm)
      have hcorrespondent :
          (dN.characterEquiv theta).1 ≠
            (dN.characterEquiv etaInvariant).1 := by
        intro heq
        apply hetaInvariant
        apply dN.characterEquiv.injective
        apply Subtype.ext
        exact heq.symm
      exact
        multiplicity_dvd_of_ne_of_isPPrimeGroup
          dN hN etaInvariant
          (dN.characterEquiv theta).1
          hcorrespondent

/-- The weighted orbit congruence deletes all nontrivial `S`-orbits in
the restriction-transitivity sum through `N`. -/
theorem normalRestrictionProduct_sum_modEq_fixedPoints
    (hS : IsPGroup p S)
    (hsmul : ∀ (s : S) (n : N),
      ((s • n : N) : G) = s • (n : G))
    (chi :
      ActionInvariantPPrimeIrreducibleCharacter S G p)
    (phi :
      IrreducibleCharacter (FixedPoints.subgroup S N)) :
    letI := Fintype.ofFinite (IrreducibleCharacter N)
    letI := Fintype.ofFinite
      (MulAction.fixedPoints S
        (IrreducibleCharacter N))
    (∑ eta : IrreducibleCharacter N,
      normalRestrictionProduct N phi chi.1.1 eta) ≡
      ∑ eta :
          MulAction.fixedPoints S
            (IrreducibleCharacter N),
        normalRestrictionProduct N phi chi.1.1 eta.1
      [MOD p] := by
  letI : Fintype (IrreducibleCharacter N) :=
    Fintype.ofFinite _
  letI :
      Fintype
        (MulAction.fixedPoints S
          (IrreducibleCharacter N)) :=
    Fintype.ofFinite _
  apply
    PGroupInvariantSum.sum_modEq_sum_fixedPoints
      hS
  intro s eta
  unfold normalRestrictionProduct
  rw [restrictionMultiplicity_actionIrreducibleCharacter
    S N s phi eta]
  exact congrArg
    (fun m : ℕ ↦
      restrictionMultiplicity
          (actionFixedPointsInclusion S N)
          phi eta * m)
    (restrictionMultiplicity_action_normal_of_invariant
      N hsmul chi s eta)

/-- The second congruence in the proof of Isaacs 13.29.  Restriction
through `N` is first expanded over all of `Irr(N)`.  The weighted
fixed-point congruence deletes the nontrivial `S`-orbits, and uniqueness
of the Glauberman correspondent of `theta` deletes every remaining fixed
character except `theta`. -/
theorem directFixedRestriction_modEq_normalCorrespondentProduct
    (dN : ActionGlaubermanCorrespondence S N p)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (chi :
      ActionInvariantPPrimeIrreducibleCharacter S G p)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    restrictionMultiplicity
        ((actionFixedPointsInclusion S G).comp
          (IsaacsGlaubermanRestriction.fixedNormalInclusion
            N hsmul))
        (dN.characterEquiv theta).1 chi.1.1 ≡
      restrictionMultiplicity
          N.subtype theta.1.1 chi.1.1 *
        restrictionMultiplicity
          (actionFixedPointsInclusion S N)
          (dN.characterEquiv theta).1 theta.1.1
        [MOD p] := by
  classical
  letI : Fintype (IrreducibleCharacter N) :=
    Fintype.ofFinite _
  letI :
      Fintype
        (MulAction.fixedPoints S
          (IrreducibleCharacter N)) :=
    Fintype.ofFinite _
  calc
    restrictionMultiplicity
        ((actionFixedPointsInclusion S G).comp
          (IsaacsGlaubermanRestriction.fixedNormalInclusion
            N hsmul))
        (dN.characterEquiv theta).1 chi.1.1 =
        ∑ eta : IrreducibleCharacter N,
          normalRestrictionProduct N
            (dN.characterEquiv theta).1 chi.1.1 eta := by
      rw [fixedNormalInclusion_then_ambient_eq_normal_then_fixed
        N hsmul]
      exact restrictionMultiplicity_comp
        N.subtype (actionFixedPointsInclusion S N)
        (dN.characterEquiv theta).1 chi.1.1
    _ ≡
        ∑ eta :
            MulAction.fixedPoints S
              (IrreducibleCharacter N),
          normalRestrictionProduct N
            (dN.characterEquiv theta).1 chi.1.1 eta.1
          [MOD p] :=
      normalRestrictionProduct_sum_modEq_fixedPoints
        N hS hsmul chi (dN.characterEquiv theta).1
    _ ≡
        normalRestrictionProduct N
          (dN.characterEquiv theta).1 chi.1.1 theta.1.1
          [MOD p] :=
      fixedPoint_normalRestrictionProduct_sum_modEq_single
        N dN (hG.to_subgroup N) chi.1.1 theta
    _ =
        restrictionMultiplicity
            N.subtype theta.1.1 chi.1.1 *
          restrictionMultiplicity
            (actionFixedPointsInclusion S N)
            (dN.characterEquiv theta).1 theta.1.1 := by
      unfold normalRestrictionProduct
      exact Nat.mul_comm _ _

/-! ## Comparing the two computations -/

/-- Equations (1) and (2) give the unit-weighted multiplicity congruence
at the heart of the `p`-group case of Isaacs 13.29. -/
theorem target_mul_ambientMultiplicity_modEq_source_mul_normalMultiplicity
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (chi :
      ActionInvariantPPrimeIrreducibleCharacter S G p)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    restrictionMultiplicity
        (IsaacsGlaubermanRestriction.fixedNormalInclusion
          N hsmul)
        (dN.characterEquiv theta).1
        (dG.characterEquiv chi).1 *
      restrictionMultiplicity
        (actionFixedPointsInclusion S G)
        (dG.characterEquiv chi).1 chi.1.1 ≡
      restrictionMultiplicity
          N.subtype theta.1.1 chi.1.1 *
        restrictionMultiplicity
          (actionFixedPointsInclusion S N)
          (dN.characterEquiv theta).1 theta.1.1
      [MOD p] :=
  (directFixedRestriction_modEq_ambientCorrespondentProduct
      N hsmul dG hG chi (dN.characterEquiv theta).1).symm.trans
    (directFixedRestriction_modEq_normalCorrespondentProduct
      N hsmul dN hS hG chi theta)

/-- Before invoking Clifford theory, the source normal-restriction
multiplicity is prime to `p` exactly when the target normal-restriction
multiplicity is.  This is the complete numerical content of the two
congruences because the two Glauberman selection multiplicities are
prime to `p`. -/
theorem sourceMultiplicity_isPPrime_iff_targetMultiplicity_isPPrime
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (chi :
      ActionInvariantPPrimeIrreducibleCharacter S G p)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    (¬p ∣
        restrictionMultiplicity
          N.subtype theta.1.1 chi.1.1) ↔
      ¬p ∣
        restrictionMultiplicity
          (IsaacsGlaubermanRestriction.fixedNormalInclusion
            N hsmul)
          (dN.characterEquiv theta).1
          (dG.characterEquiv chi).1 := by
  let targetMultiplicity :=
    restrictionMultiplicity
      (IsaacsGlaubermanRestriction.fixedNormalInclusion
        N hsmul)
      (dN.characterEquiv theta).1
      (dG.characterEquiv chi).1
  let ambientMultiplicity :=
    restrictionMultiplicity
      (actionFixedPointsInclusion S G)
      (dG.characterEquiv chi).1 chi.1.1
  let sourceMultiplicity :=
    restrictionMultiplicity
      N.subtype theta.1.1 chi.1.1
  let normalMultiplicity :=
    restrictionMultiplicity
      (actionFixedPointsInclusion S N)
      (dN.characterEquiv theta).1 theta.1.1
  have hmod :
      targetMultiplicity * ambientMultiplicity ≡
        sourceMultiplicity * normalMultiplicity [MOD p] :=
    target_mul_ambientMultiplicity_modEq_source_mul_normalMultiplicity
      N hsmul dG dN hS hG chi theta
  have hdvd :
      p ∣ targetMultiplicity * ambientMultiplicity ↔
        p ∣ sourceMultiplicity * normalMultiplicity :=
    hmod.dvd_iff dvd_rfl
  have hambient : ¬p ∣ ambientMultiplicity :=
    dG.multiplicity_isPPrime chi
  have hnormal : ¬p ∣ normalMultiplicity :=
    dN.multiplicity_isPPrime theta
  constructor
  · intro hsource
    have hright :
        ¬p ∣ sourceMultiplicity * normalMultiplicity :=
      (not_dvd_mul_iff (Fact.out : p.Prime)).2
        ⟨hsource, hnormal⟩
    have hleft :
        ¬p ∣ targetMultiplicity * ambientMultiplicity :=
      (not_congr hdvd).2 hright
    exact
      ((not_dvd_mul_iff (Fact.out : p.Prime)).1 hleft).1
  · intro htarget
    have hleft :
        ¬p ∣ targetMultiplicity * ambientMultiplicity :=
      (not_dvd_mul_iff (Fact.out : p.Prime)).2
        ⟨htarget, hambient⟩
    have hright :
        ¬p ∣ sourceMultiplicity * normalMultiplicity :=
      (not_congr hdvd).1 hleft
    exact
      ((not_dvd_mul_iff (Fact.out : p.Prime)).1 hright).1

/-! ## The Clifford milestone and the exact source theorem -/

/-- The precise standard Clifford-theory fact needed after the two
Glauberman congruences: a multiplicity in the restriction of an
irreducible character to a normal subgroup divides the ambient degree.

Unlike Isaacs 13.29, this statement has no group action, fixed points, or
Glauberman correspondence in it. -/
def NormalRestrictionMultiplicityDividesDegreeInput : Prop :=
  ∀ {A : Type} [Group A] [Finite A]
    (M : Subgroup A) [M.Normal]
    (eta : IrreducibleCharacter M)
    (chi : IrreducibleCharacter A),
    LiesOverAlong M.subtype eta chi →
      restrictionMultiplicity M.subtype eta chi ∣ chi.degree

/-- Conjugating a normal-subgroup character by an ambient group element
does not change its multiplicity in the restriction of an ambient
irreducible character. -/
theorem restrictionMultiplicity_conjBy_normal
    {A : Type} [Group A] [Finite A]
    (M : Subgroup A) [M.Normal]
    (a : A)
    (eta : IrreducibleCharacter M)
    (chi : IrreducibleCharacter A) :
    restrictionMultiplicity M.subtype
        (IrreducibleCharacter.conjBy M a eta) chi =
      restrictionMultiplicity M.subtype eta chi := by
  let eA : A ≃* A := (MulAut.conj a).symm
  let eM : M ≃* M :=
    (MulAut.conjNormal (H := M) a).symm
  have hcomm :
      eA.toMonoidHom.comp M.subtype =
        M.subtype.comp eM.toMonoidHom := by
    ext m
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      eA, eM, MulAut.conj_symm_apply]
    exact (MulAut.conjNormal_symm_apply a m).symm
  have htransport :=
    restrictionMultiplicity_comap_equiv
      eA eM M.subtype M.subtype hcomm eta chi
  change
    restrictionMultiplicity M.subtype
        (IrreducibleCharacter.conjBy M a eta)
        (MulAut.conj a • chi) =
      restrictionMultiplicity M.subtype eta chi at htransport
  simpa using htransport

/-- Clifford conjugacy makes normal-restriction multiplicity constant on
all constituents of one irreducible ambient restriction. -/
theorem restrictionMultiplicity_eq_of_both_lieOver_normal
    {A : Type} [Group A] [Finite A]
    (M : Subgroup A) [M.Normal]
    (eta zeta : IrreducibleCharacter M)
    (chi : IrreducibleCharacter A)
    (heta : LiesOverAlong M.subtype eta chi)
    (hzeta : LiesOverAlong M.subtype zeta chi) :
    restrictionMultiplicity M.subtype zeta chi =
      restrictionMultiplicity M.subtype eta chi := by
  letI : Fintype A := Fintype.ofFinite A
  obtain ⟨g, hg⟩ :=
    CliffordPartition.exists_conjBy_normalSimpleConstituent_eq
      M chi eta heta
  obtain ⟨a, ha⟩ :=
    CliffordPartition.exists_conjBy_normalSimpleConstituent_eq
      M chi zeta hzeta
  have hconj :
      IrreducibleCharacter.conjBy M (a * g⁻¹) eta = zeta := by
    change (a * g⁻¹) • eta = zeta
    rw [← hg, ← mul_smul]
    simpa using ha
  calc
    restrictionMultiplicity M.subtype zeta chi =
        restrictionMultiplicity M.subtype
          (IrreducibleCharacter.conjBy M (a * g⁻¹) eta) chi := by
      rw [hconj]
    _ = restrictionMultiplicity M.subtype eta chi :=
      restrictionMultiplicity_conjBy_normal M (a * g⁻¹) eta chi

/-- The standard Clifford divisibility milestone: every nonzero
normal-restriction multiplicity divides the ambient irreducible degree. -/
theorem normalRestrictionMultiplicity_dvd_degree :
    NormalRestrictionMultiplicityDividesDegreeInput := by
  intro A _ _ M _ eta chi heta
  classical
  letI : Fintype (IrreducibleCharacter M) :=
    Fintype.ofFinite _
  rw [degree_eq_sum_restrictionMultiplicity_mul_degree_nat
    M.subtype chi]
  apply Finset.dvd_sum
  intro zeta _
  by_cases hzero :
      restrictionMultiplicity M.subtype zeta chi = 0
  · simp [hzero]
  · have hzeta :
        LiesOverAlong M.subtype zeta chi :=
      Nat.pos_of_ne_zero hzero
    rw [restrictionMultiplicity_eq_of_both_lieOver_normal
      M eta zeta chi heta hzeta]
    exact dvd_mul_right _ _

/-- Clifford multiplicity divisibility turns ordinary nonvanishing into
prime-to-`p` nonvanishing whenever the ambient character has `p'` degree. -/
theorem liesOverAlong_iff_multiplicity_isPPrime_of_normal
    {A : Type} [Group A] [Finite A]
    (M : Subgroup A) [M.Normal]
    (eta : IrreducibleCharacter M)
    (chi : IrreducibleCharacter A)
    (hdiv :
      LiesOverAlong M.subtype eta chi →
        restrictionMultiplicity M.subtype eta chi ∣
          chi.degree)
    (hdegree : chi.IsPPrimeDegree p) :
    LiesOverAlong M.subtype eta chi ↔
      ¬p ∣ restrictionMultiplicity M.subtype eta chi := by
  constructor
  · intro hlies hp
    exact hdegree (hp.trans (hdiv hlies))
  · intro hp
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hp (hzero ▸ dvd_zero p)

/-- The remaining Clifford input gives the same prime-to-`p`
characterization for restriction from `G^S` to the literal normal
subgroup `N ∩ G^S`. -/
theorem target_liesOver_iff_multiplicity_isPPrime_of_clifford
    (hclifford :
      NormalRestrictionMultiplicityDividesDegreeInput)
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (chi :
      ActionInvariantPPrimeIrreducibleCharacter S G p)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    LiesOverAlong
        (IsaacsGlaubermanRestriction.fixedNormalInclusion
          N hsmul)
        (dN.characterEquiv theta).1
        (dG.characterEquiv chi).1 ↔
      ¬p ∣
        restrictionMultiplicity
          (IsaacsGlaubermanRestriction.fixedNormalInclusion
            N hsmul)
          (dN.characterEquiv theta).1
          (dG.characterEquiv chi).1 := by
  let M :=
    IsaacsGlaubermanRestriction.fixedNormalSubgroup
      (S := S) (G := G) N
  let eta :=
    (dN.characterEquiv theta).1.comap
      (IsaacsGlaubermanRestriction.fixedNormalSubgroupEquiv
        N hsmul).symm
  have h :=
    liesOverAlong_iff_multiplicity_isPPrime_of_normal
      (p := p) M eta (dG.characterEquiv chi).1
      (hclifford M eta (dG.characterEquiv chi).1)
      (dG.characterEquiv chi).2
  rw [IsaacsGlaubermanRestriction.liesOver_fixedNormalSubgroupEquiv_iff
      N hsmul (dN.characterEquiv theta).1
      (dG.characterEquiv chi).1,
    IsaacsGlaubermanRestriction.restrictionMultiplicity_fixedNormalSubgroupEquiv
      N hsmul (dN.characterEquiv theta).1
      (dG.characterEquiv chi).1] at h
  exact h

/-- The source-side form of the same Clifford prime-to-`p`
characterization. -/
theorem source_liesOver_iff_multiplicity_isPPrime_of_clifford
    (hclifford :
      NormalRestrictionMultiplicityDividesDegreeInput)
    (chi :
      ActionInvariantPPrimeIrreducibleCharacter S G p)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    LiesOverAlong N.subtype theta.1.1 chi.1.1 ↔
      ¬p ∣
        restrictionMultiplicity
          N.subtype theta.1.1 chi.1.1 :=
  liesOverAlong_iff_multiplicity_isPPrime_of_normal
    (p := p) N theta.1.1 chi.1.1
    (hclifford N theta.1.1 chi.1.1)
    chi.1.2

/-- **Reduction of Isaacs 13.29.**  The exact action-level input follows
from the standard action-free Clifford divisibility milestone.

All Glauberman-specific work is discharged by the two compiled
restriction congruences above. -/
theorem isaacsGlaubermanRestrictionInput_of_normalRestrictionMultiplicity_dvd_degree
    (hclifford :
      NormalRestrictionMultiplicityDividesDegreeInput)
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p) :
    IsaacsGlaubermanRestriction.IsaacsGlaubermanRestrictionInput
      N hsmul dG dN := by
  intro hS hG chi theta
  exact
    (source_liesOver_iff_multiplicity_isPPrime_of_clifford
      N hclifford chi theta).trans
      ((sourceMultiplicity_isPPrime_iff_targetMultiplicity_isPPrime
        N hsmul dG dN hS hG chi theta).trans
        (target_liesOver_iff_multiplicity_isPPrime_of_clifford
          N hsmul hclifford dG dN chi theta).symm)

/-- **Isaacs 13.29, `p`-group case.**  The action-level Glauberman
correspondence preserves lying over a normal subgroup. -/
theorem isaacsGlaubermanRestrictionInput
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p) :
    IsaacsGlaubermanRestriction.IsaacsGlaubermanRestrictionInput
      N hsmul dG dN :=
  isaacsGlaubermanRestrictionInput_of_normalRestrictionMultiplicity_dvd_degree
    N hsmul normalRestrictionMultiplicity_dvd_degree dG dN

end IsaacsGlaubermanRestrictionReduction

end McKayConjecture
