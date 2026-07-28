/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanLinearCharacter
import McKayConjecture.GroupTheory.CoprimeActionFixedDual
import McKayConjecture.GroupTheory.PPrimeCore

/-!
# Glauberman correspondence for a commutative coprime kernel

For a finite commutative normal `p′`-subgroup `K`, every irreducible
character is linear.  The group-action norm proves that restriction
identifies the `P`-invariant linear characters of `K` with the linear
characters of `C_K(P)`.  Together with the multiplicity-one calculation
for linear restriction, this gives the full Glauberman correspondence in
this case.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K P : Subgroup G) [K.Normal]
variable [IsMulCommutative K]

local instance commGroupOfCommutativeKernel : CommGroup K :=
  CommGroup.mk
    (fun a b : K ↦ IsMulCommutative.is_comm.comm a b)

local instance fixedPointsIsMulCommutative :
    IsMulCommutative (coprimeFixedPoints K P) :=
  ⟨⟨fun a b ↦ by
    apply Subtype.ext
    have hcomm :=
      IsMulCommutative.is_comm.comm
        (coprimeFixedPointsInclusion K P a)
        (coprimeFixedPointsInclusion K P b)
    exact congrArg (fun z : K ↦ (z : G)) hcomm⟩⟩

/-- Conjugation by `P` on the normal subgroup `K`. -/
local instance subgroupConjugationAction :
    MulDistribMulAction P K :=
  MulDistribMulAction.compHom K
    ((MulAut.conjNormal (H := K)).comp P.subtype)

@[simp]
theorem subgroupConjugation_smul_coe
    (g : P) (k : K) :
    ((g • k : K) : G) =
      (g : G) * (k : G) * (g : G)⁻¹ :=
  rfl

/-- Fixed points for the conjugation action of `P` on `K` are exactly
the subgroup `C_K(P)`. -/
def conjugationFixedPointsEquiv :
    GroupTheory.actionFixedPoints P K ≃*
      coprimeFixedPoints K P where
  toFun x :=
    ⟨x.1.1, x.1.2, by
      change
        (x.1.1 : G) ∈
          Subgroup.centralizer (P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hfixed := congrArg Subtype.val
        (x.2 ⟨g, hg⟩)
      change
        (g : G) * (x.1 : G) * (g : G)⁻¹ =
          (x.1 : G) at hfixed
      calc
        (g : G) * (x.1 : G) =
            ((g : G) * (x.1 : G) * (g : G)⁻¹) *
              (g : G) := by group
        _ = (x.1 : G) * (g : G) := by rw [hfixed]⟩
  invFun x :=
    ⟨⟨x.1, x.2.1⟩, fun g ↦ by
      apply Subtype.ext
      change
        (g : G) * (x : G) * (g : G)⁻¹ =
          (x : G)
      have hcomm :
          (g : G) * (x : G) =
            (x : G) * (g : G) :=
        Subgroup.mem_centralizer_iff.mp x.2.2
          g g.2
      rw [hcomm]
      group⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

/-- The fixed-point equivalence commutes with the inclusions into `K`. -/
@[simp]
theorem conjugationFixedPointsEquiv_inclusion
    (x : GroupTheory.actionFixedPoints P K) :
    coprimeFixedPointsInclusion K P
        (conjugationFixedPointsEquiv K P x) =
      (GroupTheory.actionFixedPoints P K).subtype x := by
  apply Subtype.ext
  rfl

/-- The orders of a `p′`-kernel and a `p`-group are coprime. -/
theorem card_coprime_of_isPPrimeGroup_isPGroup
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P) :
    (Nat.card K).Coprime (Nat.card P) := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn]
  exact (hK.pow_left n).symm

/-- On a commutative kernel, taking the underlying multiplicative
parameter identifies `P`-invariant prime-to-`p` irreducible characters
with `P`-invariant homomorphisms to `ℂˣ`. -/
def invariantPPrimeLinearEquiv :
    PInvariantPPrimeIrreducibleCharacter K P p ≃
      GroupTheory.InvariantMonoidHom P K ℂˣ where
  toFun θ :=
    let lam :=
      IrreducibleCharacter.linearParameterOfDegreeOne
        θ.1.1
        (IrreducibleCharacter.degree_eq_one_of_isMulCommutative
          θ.1.1)
    ⟨lam, fun g k ↦ by
      apply Units.ext
      dsimp only [lam]
      rw [
        IrreducibleCharacter.linearParameterOfDegreeOne_values,
        IrreducibleCharacter.linearParameterOfDegreeOne_values]
      have hinertia :
          ((g : G)⁻¹) ∈
            IrreducibleCharacter.inertia K θ.1.1 :=
        θ.2 (P.inv_mem g.2)
      have hfix :=
        (IrreducibleCharacter.mem_inertia_iff
          K θ.1.1 (g : G)⁻¹).mp hinertia
      have hvalue :=
        congrArg
          (fun χ : IrreducibleCharacter K ↦
            χ.values k) hfix
      rw [IrreducibleCharacter.conjBy_values] at hvalue
      have harg :
          g • k =
            (MulAut.conjNormal
              (H := K) (g : G)⁻¹).symm k := by
        apply Subtype.ext
        simp only [
          MulAut.conjNormal_symm_apply, inv_inv]
        rfl
      rw [harg]
      exact hvalue⟩
  invFun lam :=
    let θ : PPrimeIrreducibleCharacter K p :=
      ⟨IrreducibleCharacter.linear lam.1,
        IrreducibleCharacter.linear_isPPrimeDegree
          lam.1 p⟩
    ⟨θ, by
      intro g hg
      rw [IrreducibleCharacter.mem_inertia_iff]
      apply IrreducibleCharacter.ext
      funext k
      rw [IrreducibleCharacter.conjBy_values]
      dsimp only [θ]
      rw [
        IrreducibleCharacter.linear_values,
        IrreducibleCharacter.linear_values]
      change
        ((lam.1
          ((MulAut.conjNormal (H := K) g).symm k) :
            ℂˣ) : ℂ) =
          (lam.1 k : ℂ)
      have hinvariant :=
        lam.2 ⟨g⁻¹, P.inv_mem hg⟩ k
      exact congrArg (fun z : ℂˣ ↦ (z : ℂ))
        (by
          have harg :
              (⟨g⁻¹, P.inv_mem hg⟩ : P) • k =
                (MulAut.conjNormal
                  (H := K) g).symm k := by
            apply Subtype.ext
            rw [
              subgroupConjugation_smul_coe,
              MulAut.conjNormal_symm_apply,
              inv_inv]
          rw [harg] at hinvariant
          exact hinvariant)⟩
  left_inv θ := by
    apply Subtype.ext
    apply Subtype.ext
    exact
      IrreducibleCharacter.linear_linearParameterOfDegreeOne
        θ.1.1
        (IrreducibleCharacter.degree_eq_one_of_isMulCommutative
          θ.1.1)
  right_inv lam := by
    apply Subtype.ext
    apply IrreducibleCharacter.linear_injective
    exact
      IrreducibleCharacter.linear_linearParameterOfDegreeOne
        (IrreducibleCharacter.linear lam.1)
        (IrreducibleCharacter.linear_degree lam.1)

@[simp]
theorem invariantPPrimeLinearEquiv_apply_coe
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    (invariantPPrimeLinearEquiv
      (p := p) K P θ).1 =
      IrreducibleCharacter.linearParameterOfDegreeOne
        θ.1.1
        (IrreducibleCharacter.degree_eq_one_of_isMulCommutative
          θ.1.1) :=
  rfl

/-- Transport homomorphisms across the identification of action fixed
points with `C_K(P)`. -/
def fixedPointLinearHomEquiv :
    (GroupTheory.actionFixedPoints P K →* ℂˣ) ≃
      (coprimeFixedPoints K P →* ℂˣ) where
  toFun lam :=
    lam.comp
      (conjugationFixedPointsEquiv K P).symm.toMonoidHom
  invFun lam :=
    lam.comp
      (conjugationFixedPointsEquiv K P).toMonoidHom
  left_inv lam := by
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply]
    change
      lam ((conjugationFixedPointsEquiv K P).symm
        (conjugationFixedPointsEquiv K P x)) =
        lam x
    rw [
      (conjugationFixedPointsEquiv K P).symm_apply_apply]
  right_inv lam := by
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply]
    change
      lam (conjugationFixedPointsEquiv K P
        ((conjugationFixedPointsEquiv K P).symm x)) =
        lam x
    rw [
      (conjugationFixedPointsEquiv K P).apply_symm_apply]

@[simp]
theorem fixedPointLinearHomEquiv_apply
    (lam :
      GroupTheory.actionFixedPoints P K →* ℂˣ) :
    fixedPointLinearHomEquiv K P lam =
      lam.comp
        (conjugationFixedPointsEquiv
          K P).symm.toMonoidHom :=
  rfl

/-- The character bijection underlying Glauberman correspondence for a
commutative `p′`-kernel.  It is the restriction map on linear
characters; the inverse is supplied by the coprime-action norm. -/
def commutativeKernelGlaubermanCharacterEquiv
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P) :
    PInvariantPPrimeIrreducibleCharacter K P p ≃
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints K P) p := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype P := Fintype.ofFinite P
  exact
    (invariantPPrimeLinearEquiv
      (p := p) K P).trans
      ((GroupTheory.invariantMonoidHomEquivFixedPoints
        (P := P) (A := K) ℂˣ
        (card_coprime_of_isPPrimeGroup_isPGroup
          K P hK hP)).trans
        ((fixedPointLinearHomEquiv K P).trans
          (IrreducibleCharacter.commutativePPrimeLinearEquiv
            (G := coprimeFixedPoints K P) p).symm))

/-- The forward map in the commutative-kernel correspondence is literal
restriction to `C_K(P)`. -/
@[simp]
theorem commutativeKernelGlaubermanCharacterEquiv_apply_coe
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    (commutativeKernelGlaubermanCharacterEquiv
      K P hK hP θ).1 =
      (commutativeKernelGlaubermanCandidate
        K P θ).1 := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype P := Fintype.ofFinite P
  apply IrreducibleCharacter.ext
  funext x
  simp [
    commutativeKernelGlaubermanCharacterEquiv,
    invariantPPrimeLinearEquiv,
    fixedPointLinearHomEquiv,
    commutativeKernelGlaubermanCandidate,
    linearGlaubermanCandidate]
  congr 1

/-- The full Glauberman correspondence for a finite commutative normal
`p′`-kernel acted on by a `p`-group. -/
def glaubermanCorrespondenceOfCommutativeKernel
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P) :
    GlaubermanCorrespondence K P p where
  characterEquiv :=
    commutativeKernelGlaubermanCharacterEquiv
      K P hK hP
  multiplicity_isPPrime θ := by
    rw [
      commutativeKernelGlaubermanCharacterEquiv_apply_coe,
      restrictionMultiplicity_commutativeKernelGlaubermanCandidate_eq_one]
    exact (Fact.out : p.Prime).not_dvd_one
  eq_correspondent_of_multiplicity_isPPrime θ φ hφ := by
    refine
      (eq_commutativeKernelGlaubermanCandidate_of_multiplicity_isPPrime
        K P θ φ hφ).trans ?_
    apply Subtype.ext
    exact
      (commutativeKernelGlaubermanCharacterEquiv_apply_coe
        K P hK hP θ).symm

end McKayConjecture
