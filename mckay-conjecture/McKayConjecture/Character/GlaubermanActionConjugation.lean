/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionPGroupInduction
import McKayConjecture.Character.GlaubermanCorrespondence
import McKayConjecture.Character.OverAlongTransport

/-!
# From action-level to ambient Glauberman correspondences

For a normal subgroup `K ◁ G` and a subgroup `P ≤ G`, conjugation gives
an abstract action of `P` on `K`.  Its fixed-point subgroup is canonically
`C_K(P)`.  This file transports invariant characters, restriction
multiplicities, and the strong action correspondence through those
canonical coordinates.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K P : Subgroup G) [K.Normal]

/-- Conjugation by `P` on the normal subgroup `K`. -/
def subgroupConjugationMulDistribMulAction :
    MulDistribMulAction P K :=
  MulDistribMulAction.compHom K
    ((MulAut.conjNormal (H := K)).comp P.subtype)

local instance glaubermanActionConjugationInstance :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K P

@[simp]
theorem subgroupConjugationAction_smul_coe
    (g : P) (k : K) :
    ((g • k : K) : G) =
      (g : G) * (k : G) * (g : G)⁻¹ :=
  rfl

/-- Fixed points for conjugation are canonically the ambient
fixed-point subgroup `C_K(P)`. -/
def subgroupConjugationFixedPointsEquiv :
    FixedPoints.subgroup P K ≃*
      coprimeFixedPoints K P where
  toFun x :=
    ⟨x.1.1, x.1.2, by
      change
        (x.1.1 : G) ∈
          Subgroup.centralizer (P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hfixed :=
        congrArg Subtype.val (x.2 ⟨g, hg⟩)
      change
        (g : G) * (x.1 : G) * (g : G)⁻¹ =
          (x.1 : G) at hfixed
      calc
        g * (x.1 : G) =
            (g * (x.1 : G) * g⁻¹) * g := by
          group
        _ = (x.1 : G) * g := by rw [hfixed]⟩
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

@[simp]
theorem subgroupConjugationFixedPointsEquiv_apply_coe
    (x : FixedPoints.subgroup P K) :
    ((subgroupConjugationFixedPointsEquiv
      K P x : coprimeFixedPoints K P) : G) =
      ((x : K) : G) :=
  rfl

/-- Ambient inertia invariance and invariance under the abstract
conjugation action are equivalent. -/
def pInvariantCharacterEquivActionInvariant :
    PInvariantPPrimeIrreducibleCharacter K P p ≃
      ActionInvariantPPrimeIrreducibleCharacter
        P K p where
  toFun θ :=
    ⟨θ.1, by
      intro g k
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
            χ.values k)
          hfix
      rw [IrreducibleCharacter.conjBy_values] at hvalue
      have harg :
          (MulAut.conjNormal
            (H := K) ((g : G)⁻¹)).symm k =
            g • k := by
        apply Subtype.ext
        simp only [MulAut.conjNormal_symm_apply,
          inv_inv]
        rfl
      rw [harg] at hvalue
      exact hvalue⟩
  invFun θ :=
    ⟨θ.1, by
      intro g hg
      rw [IrreducibleCharacter.mem_inertia_iff]
      apply IrreducibleCharacter.ext
      funext k
      rw [IrreducibleCharacter.conjBy_values]
      exact θ.2 ⟨g⁻¹, P.inv_mem hg⟩ k⟩
  left_inv θ := by
    apply Subtype.ext
    rfl
  right_inv θ := by
    apply Subtype.ext
    rfl

/-- The two fixed-point inclusions have equal restriction multiplicities
after transport through the canonical fixed-point equivalence. -/
theorem restrictionMultiplicity_subgroupConjugationFixedPointsEquiv
    (φ : IrreducibleCharacter
      (FixedPoints.subgroup P K))
    (θ : IrreducibleCharacter K) :
    restrictionMultiplicity
        (coprimeFixedPointsInclusion K P)
        (φ.comap
          (subgroupConjugationFixedPointsEquiv
            K P).symm)
        θ =
      restrictionMultiplicity
        (actionFixedPointsInclusion P K)
        φ θ := by
  have hcomm :
      (MulEquiv.refl K).toMonoidHom.comp
          (coprimeFixedPointsInclusion K P) =
        (actionFixedPointsInclusion P K).comp
          (subgroupConjugationFixedPointsEquiv
            K P).symm.toMonoidHom := by
    ext x
    rfl
  simpa using
    restrictionMultiplicity_comap_equiv
      (MulEquiv.refl K)
      (subgroupConjugationFixedPointsEquiv K P).symm
      (actionFixedPointsInclusion P K)
      (coprimeFixedPointsInclusion K P)
      hcomm φ θ

/-- A strong correspondence for the abstract conjugation action gives
the ordinary ambient-subgroup Glauberman correspondence. -/
def glaubermanCorrespondenceOfStrongConjugationAction
    (d : StrongActionGlaubermanCorrespondence P K p) :
    GlaubermanCorrespondence K P p where
  characterEquiv :=
    (pInvariantCharacterEquivActionInvariant
      K P).trans
      (d.characterEquiv.trans
        (IrreducibleCharacter.pPrimeComapEquiv p
          (subgroupConjugationFixedPointsEquiv
            K P).symm))
  multiplicity_isPPrime := by
    intro θ
    change
      ¬p ∣
        restrictionMultiplicity
          (coprimeFixedPointsInclusion K P)
          ((d.characterEquiv
            (pInvariantCharacterEquivActionInvariant
              K P θ)).1.comap
                (subgroupConjugationFixedPointsEquiv
                  K P).symm)
          θ.1.1
    rw [
      restrictionMultiplicity_subgroupConjugationFixedPointsEquiv
        K P]
    exact
      d.multiplicity_isPPrime
        (pInvariantCharacterEquivActionInvariant
          K P θ)
  eq_correspondent_of_multiplicity_isPPrime := by
    intro θ φ hφ
    let θa :=
      pInvariantCharacterEquivActionInvariant K P θ
    let e :=
      subgroupConjugationFixedPointsEquiv K P
    let φa :
        IrreducibleCharacter
          (FixedPoints.subgroup P K) :=
      φ.1.comap e
    have hφa :
        ¬p ∣
          restrictionMultiplicity
            (actionFixedPointsInclusion P K)
            φa θ.1.1 := by
      rw [←
        restrictionMultiplicity_subgroupConjugationFixedPointsEquiv
          K P]
      have hback :
          φa.comap e.symm = φ.1 := by
        change (φ.1.comap e).comap e.symm = φ.1
        simp
      rw [hback]
      exact hφ
    have heq :
        φa = (d.characterEquiv θa).1 :=
      d.eq_correspondent_of_multiplicity_isPPrime
        θa φa hφa
    apply Subtype.ext
    calc
      φ.1 = φa.comap e.symm := by
        change φ.1 = (φ.1.comap e).comap e.symm
        simp
      _ = (d.characterEquiv θa).1.comap e.symm :=
        congrArg
          (fun χ : IrreducibleCharacter
            (FixedPoints.subgroup P K) ↦
            χ.comap e.symm)
          heq
      _ = _ := by rfl

/-- Once the cyclic action theorem is available, every normal `p'`-kernel
and acting `p`-subgroup have the ambient Glauberman correspondence. -/
theorem exists_glaubermanCorrespondence_of_cyclicStrongAction
    (cyclic : CyclicStrongActionGlaubermanHypothesis p)
    (hP : IsPGroup p P)
    (hK : GroupTheory.IsPPrimeGroup p K) :
    Nonempty (GlaubermanCorrespondence K P p) := by
  obtain ⟨d⟩ :=
    strongActionGlaubermanCorrespondenceOfPGroup
      cyclic P K hP hK
  exact
    ⟨glaubermanCorrespondenceOfStrongConjugationAction
      K P d⟩

end McKayConjecture
