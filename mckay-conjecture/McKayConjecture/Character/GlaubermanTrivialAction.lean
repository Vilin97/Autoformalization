/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EquivalenceRestrictionMultiplicity
import McKayConjecture.Character.GlaubermanCorrespondence

/-!
# The Glauberman correspondence for a trivial action

When `P` centralizes `K`, the fixed-point subgroup `C_K(P)` is literally
`K`.  The Glauberman correspondence is therefore transport along this
subgroup equality.  Restriction along the resulting group equivalence has
multiplicity one on the matching character and zero on every other
irreducible character, proving the full unique prime-to-`p` multiplicity
characterization without any correspondence hypothesis.

This is the terminal case of an inductive construction of the general
coprime-action correspondence.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K P : Subgroup G) [K.Normal]

/-- If `P` centralizes `K`, then `C_K(P)` is canonically isomorphic to
`K`. -/
def coprimeFixedPointsEquivOfCentralizes
    (hcentralizes :
      K ≤ Subgroup.centralizer (P : Set G)) :
    coprimeFixedPoints K P ≃* K :=
  MulEquiv.subgroupCongr
    (inf_eq_left.mpr hcentralizes)

omit [Finite G] [K.Normal] in
@[simp]
theorem coprimeFixedPointsEquivOfCentralizes_apply_coe
    (hcentralizes :
      K ≤ Subgroup.centralizer (P : Set G))
    (x : coprimeFixedPoints K P) :
    ((coprimeFixedPointsEquivOfCentralizes
      K P hcentralizes x : K) : G) = x :=
  rfl

omit [Finite G] [Fact p.Prime] in
/-- Triviality of the `P`-action on `K` makes every irreducible character
of `K` `P`-invariant. -/
theorem le_inertia_of_le_centralizer
    (hcentralizes :
      K ≤ Subgroup.centralizer (P : Set G))
    (θ : IrreducibleCharacter K) :
    P ≤ IrreducibleCharacter.inertia K θ := by
  intro g hg
  rw [IrreducibleCharacter.mem_inertia_iff]
  apply IrreducibleCharacter.ext
  funext k
  rw [IrreducibleCharacter.conjBy_values]
  congr 1
  apply Subtype.ext
  rw [MulAut.conjNormal_symm_apply]
  have hcomm :
      (g : G) * (k : G) =
        (k : G) * (g : G) :=
    Subgroup.mem_centralizer_iff.mp
      (hcentralizes k.property) g hg
  calc
    (g : G)⁻¹ * (k : G) * (g : G) =
        (g : G)⁻¹ * ((k : G) * (g : G)) := by
          rw [mul_assoc]
    _ = (g : G)⁻¹ * ((g : G) * (k : G)) := by
          rw [← hcomm]
    _ = k := by group

/-- In the trivial-action case, transport along `C_K(P) = K` is the
Glauberman character bijection. -/
def trivialActionGlaubermanCharacterEquiv
    (hcentralizes :
      K ≤ Subgroup.centralizer (P : Set G)) :
    PInvariantPPrimeIrreducibleCharacter K P p ≃
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints K P) p where
  toFun θ :=
    IrreducibleCharacter.pPrimeComapEquiv p
      (coprimeFixedPointsEquivOfCentralizes
        K P hcentralizes) θ.1
  invFun φ :=
    let θ :=
      IrreducibleCharacter.pPrimeComapEquiv p
        (coprimeFixedPointsEquivOfCentralizes
          K P hcentralizes).symm φ
    ⟨θ,
      le_inertia_of_le_centralizer
        K P hcentralizes θ.1⟩
  left_inv θ := by
    apply Subtype.ext
    exact
      (IrreducibleCharacter.pPrimeComapEquiv p
        (coprimeFixedPointsEquivOfCentralizes
          K P hcentralizes)).symm_apply_apply θ.1
  right_inv φ := by
    exact
      (IrreducibleCharacter.pPrimeComapEquiv p
        (coprimeFixedPointsEquivOfCentralizes
          K P hcentralizes)).apply_symm_apply φ

omit [Finite G] [Fact p.Prime] in
@[simp]
theorem trivialActionGlaubermanCharacterEquiv_apply_coe
    (hcentralizes :
      K ≤ Subgroup.centralizer (P : Set G))
    (θ :
      PInvariantPPrimeIrreducibleCharacter K P p) :
    (trivialActionGlaubermanCharacterEquiv
      K P hcentralizes θ).1 =
      θ.1.1.comap
        (coprimeFixedPointsEquivOfCentralizes
          K P hcentralizes) :=
  rfl

/-- The full Glauberman correspondence when the action is trivial. -/
def glaubermanCorrespondenceOfCentralizes
    (hcentralizes :
      K ≤ Subgroup.centralizer (P : Set G)) :
    GlaubermanCorrespondence K P p where
  characterEquiv :=
    trivialActionGlaubermanCharacterEquiv
      K P hcentralizes
  multiplicity_isPPrime := by
    intro θ
    have hinclusion :
        (coprimeFixedPointsInclusion K P) =
          (coprimeFixedPointsEquivOfCentralizes
            K P hcentralizes).toMonoidHom := by
      ext x
      rfl
    rw [hinclusion,
      trivialActionGlaubermanCharacterEquiv_apply_coe,
      restrictionMultiplicity_comap_mulEquiv_eq_one]
    exact (Fact.out : p.Prime).not_dvd_one
  eq_correspondent_of_multiplicity_isPPrime := by
    intro θ φ hφ
    have hinclusion :
        (coprimeFixedPointsInclusion K P) =
          (coprimeFixedPointsEquivOfCentralizes
            K P hcentralizes).toMonoidHom := by
      ext x
      rfl
    by_contra hne
    have hzero :
        restrictionMultiplicity
            (coprimeFixedPointsInclusion K P)
            φ.1 θ.1.1 =
          0 := by
      rw [hinclusion]
      apply
        restrictionMultiplicity_mulEquiv_eq_zero_of_ne
      intro heq
      apply hne
      apply Subtype.ext
      simpa only [
        trivialActionGlaubermanCharacterEquiv_apply_coe]
        using heq
    exact hφ (hzero ▸ dvd_zero p)

/-- A central normal kernel has the trivial-action Glauberman
correspondence for every acting subgroup. -/
def glaubermanCorrespondenceOfKernelCentral
    (hcenter : K ≤ Subgroup.center G) :
    GlaubermanCorrespondence K P p :=
  glaubermanCorrespondenceOfCentralizes K P
    (hcenter.trans
      (Subgroup.center_le_centralizer
        (P : Set G)))

/-- A central acting subgroup has the trivial-action Glauberman
correspondence on every normal kernel. -/
def glaubermanCorrespondenceOfActingSubgroupCentral
    (hcenter : P ≤ Subgroup.center G) :
    GlaubermanCorrespondence K P p :=
  glaubermanCorrespondenceOfCentralizes K P
    (Subgroup.le_centralizer_iff.mpr
      (hcenter.trans
        (Subgroup.center_le_centralizer
          (K : Set G))))

/-- The Glauberman correspondence for the trivial acting subgroup. -/
def glaubermanCorrespondenceBot :
    GlaubermanCorrespondence K (⊥ : Subgroup G) p :=
  glaubermanCorrespondenceOfCentralizes K ⊥ (by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxone : x = 1 :=
      Subgroup.mem_bot.mp hx
    subst x
    simp)

end McKayConjecture
