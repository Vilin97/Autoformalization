/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Module.Torsion.Basic
import McKayConjecture.CharacterTriple.FactorSetPPrimaryValues
import McKayConjecture.CharacterTriple.FiniteRootResidueField

/-!
# Reduction of an integral projective lattice modulo an ideal

The determinant-normalized operators on the integral lattice preserve
every ideal multiple of that lattice.  They therefore descend to the
quotient lattice modulo any ideal of the cyclotomic coefficient ring.
Their projective multiplication scalar is exactly the residue of the
finite roots-of-unity factor set.

When the ideal is maximal, the quotient ring is a field and the
descended automorphisms assemble into a projective representation over
that residue field.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {G : Type u} {V : Type v} {ι : Type w}
variable [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable [Finite ι]

private instance projectiveFinrankNeZero :
    NeZero (Module.finrank ℂ V) :=
  ⟨Module.finrank_pos.ne'⟩

variable
  (P : ProjectiveRepresentation ℂ G V)
  (b : Module.Basis ι ℂ V)

/-- Scalar multiplication by a unit as a linear automorphism over a
commutative ring. -/
def unitScalarLinearEquiv
    {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M]
    (a : Rˣ) :
    M ≃ₗ[R] M where
  toFun x := (a : R) • x
  invFun x := (↑(a⁻¹) : R) • x
  left_inv x := by
    change
      (↑(a⁻¹) : R) • ((a : R) • x) = x
    rw [← mul_smul]
    simp
  right_inv x := by
    change
      (a : R) • ((↑(a⁻¹) : R) • x) = x
    rw [← mul_smul]
    simp
  map_add' x y := smul_add (a : R) x y
  map_smul' r x := by
    change
      (a : R) • (r • x) =
        r • ((a : R) • x)
    rw [← mul_smul, ← mul_smul, mul_comm]

@[simp]
theorem unitScalarLinearEquiv_apply
    {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M]
    (a : Rˣ) (x : M) :
    unitScalarLinearEquiv a x = (a : R) • x :=
  rfl

/-- The projective multiplication law already holds on the integral
lattice, with scalar in the cyclotomic coefficient ring. -/
theorem integralLatticeEndomorphism_mul
    (g h : G) :
    P.integralLatticeEndomorphism b g *
        P.integralLatticeEndomorphism b h =
      FiniteRootCoefficientRing.root
          (Module.finrank ℂ V)
          (P.finiteFactorSet g h) •
        P.integralLatticeEndomorphism b (g * h) := by
  ext x
  change
    P.finiteFactorNormalize.operator g
        (P.finiteFactorNormalize.operator h (x : V)) =
      (((P.finiteFactorSet g h :
          rootsOfUnity (Module.finrank ℂ V) ℂ) :
        ℂˣ) : ℂ) •
        P.finiteFactorNormalize.operator (g * h) (x : V)
  have hmul :=
    congrArg
      (fun f : V ≃ₗ[ℂ] V ↦ f (x : V))
      (P.finiteFactorNormalize.map_mul g h)
  simpa only [
    LinearEquiv.mul_apply,
    scalarLinearEquiv_apply,
    finiteFactorSet_coe] using hmul

@[simp]
theorem integralLatticeEndomorphism_one :
    P.integralLatticeEndomorphism b 1 = 1 := by
  ext x
  change P.finiteFactorNormalize.operator 1 (x : V) = x
  rw [P.finiteFactorNormalize_isNormalized]
  rfl

theorem integralLatticeEndomorphism_injective
    (g : G) :
    Function.Injective
      (P.integralLatticeEndomorphism b g) := by
  intro x y hxy
  apply Subtype.ext
  apply (P.finiteFactorNormalize.operator g).injective
  exact congrArg Subtype.val hxy

theorem integralLatticeEndomorphism_surjective
    (g : G) :
    Function.Surjective
      (P.integralLatticeEndomorphism b g) := by
  intro y
  let z : rootsOfUnity (Module.finrank ℂ V) ℂ :=
    P.finiteFactorSet g g⁻¹
  let u :
      (FiniteRootCoefficientRing
        (Module.finrank ℂ V))ˣ :=
    FiniteRootCoefficientRing.rootUnit
      (Module.finrank ℂ V) z
  let r :
      FiniteRootCoefficientRing (Module.finrank ℂ V) :=
    (↑(u⁻¹) :
      FiniteRootCoefficientRing (Module.finrank ℂ V))
  refine
    ⟨r • P.integralLatticeEndomorphism b g⁻¹ y, ?_⟩
  have hmul :=
    LinearMap.congr_fun
      (P.integralLatticeEndomorphism_mul b g g⁻¹) y
  change
    P.integralLatticeEndomorphism b g
        (r • P.integralLatticeEndomorphism b g⁻¹ y) =
      y
  rw [map_smul]
  change
    r •
      (P.integralLatticeEndomorphism b g *
        P.integralLatticeEndomorphism b g⁻¹) y = y
  rw [hmul, mul_inv_cancel, integralLatticeEndomorphism_one]
  change r •
      FiniteRootCoefficientRing.root
          (Module.finrank ℂ V) z • y = y
  rw [← mul_smul]
  change
    ((↑(u⁻¹) :
      FiniteRootCoefficientRing (Module.finrank ℂ V)) *
        FiniteRootCoefficientRing.root
          (Module.finrank ℂ V) z) • y = y
  rw [← FiniteRootCoefficientRing.rootUnit_val]
  change
    ((↑(u⁻¹) :
      FiniteRootCoefficientRing (Module.finrank ℂ V)) *
        (u :
          FiniteRootCoefficientRing (Module.finrank ℂ V))) •
      y = y
  simp

/-- Each normalized operator is an automorphism of the integral
lattice, not merely an endomorphism. -/
def integralLatticeAutomorphism
    (g : G) :
    P.integralLattice b ≃ₗ[
      FiniteRootCoefficientRing (Module.finrank ℂ V)]
      P.integralLattice b :=
  LinearEquiv.ofBijective
    (P.integralLatticeEndomorphism b g)
    ⟨P.integralLatticeEndomorphism_injective b g,
      P.integralLatticeEndomorphism_surjective b g⟩

@[simp]
theorem integralLatticeAutomorphism_apply
    (g : G) (x : P.integralLattice b) :
    P.integralLatticeAutomorphism b g x =
      P.integralLatticeEndomorphism b g x :=
  rfl

/-- The integral lattice reduced modulo an ideal of its cyclotomic
coefficient ring. -/
abbrev residueLattice
    (I :
      Ideal
        (FiniteRootCoefficientRing
          (Module.finrank ℂ V))) :=
  P.integralLattice b ⧸
    I •
      (⊤ :
        Submodule
          (FiniteRootCoefficientRing
            (Module.finrank ℂ V))
          (P.integralLattice b))

/-- The finite roots-of-unity factor set reduced modulo an ideal of the
cyclotomic coefficient ring. -/
def finiteFactorResidueReduction
    (I :
      Ideal
        (FiniteRootCoefficientRing
          (Module.finrank ℂ V))) :
    FactorSet G
      (FiniteRootCoefficientRing
          (Module.finrank ℂ V) ⧸ I)ˣ :=
  P.finiteFactorSet.map
    (FiniteRootCoefficientRing.residueRootHom
      (Module.finrank ℂ V) I)

@[simp]
theorem finiteFactorResidueReduction_apply
    (I :
      Ideal
        (FiniteRootCoefficientRing
          (Module.finrank ℂ V)))
    (g h : G) :
    P.finiteFactorResidueReduction I g h =
      FiniteRootCoefficientRing.residueRootHom
        (Module.finrank ℂ V) I
        (P.finiteFactorSet g h) :=
  rfl

private theorem integralLatticeAutomorphism_map_ideal_smul
    (I :
      Ideal
        (FiniteRootCoefficientRing
          (Module.finrank ℂ V)))
    (g : G) :
    (I •
        (⊤ :
          Submodule
            (FiniteRootCoefficientRing
              (Module.finrank ℂ V))
            (P.integralLattice b))).map
        (P.integralLatticeAutomorphism b g :
          P.integralLattice b →ₗ[
            FiniteRootCoefficientRing
              (Module.finrank ℂ V)]
            P.integralLattice b) =
      I •
        (⊤ :
          Submodule
            (FiniteRootCoefficientRing
              (Module.finrank ℂ V))
            (P.integralLattice b)) := by
  rw [Submodule.map_smul'', Submodule.map_top]
  rw [LinearMap.range_eq_top.mpr
    (P.integralLatticeAutomorphism b g).surjective]

/-- A normalized projective operator descended to the quotient
lattice modulo `I`. -/
def residueLatticeAutomorphism
    (I :
      Ideal
        (FiniteRootCoefficientRing
          (Module.finrank ℂ V)))
    (g : G) :
    P.residueLattice b I ≃ₗ[
      FiniteRootCoefficientRing
          (Module.finrank ℂ V) ⧸ I]
      P.residueLattice b I :=
  LinearEquiv.extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective
    (Submodule.Quotient.equiv
      (I •
        (⊤ :
          Submodule
            (FiniteRootCoefficientRing
              (Module.finrank ℂ V))
            (P.integralLattice b)))
      (I •
        (⊤ :
          Submodule
            (FiniteRootCoefficientRing
              (Module.finrank ℂ V))
            (P.integralLattice b)))
      (P.integralLatticeAutomorphism b g)
      (P.integralLatticeAutomorphism_map_ideal_smul b I g))

@[simp]
theorem residueLatticeAutomorphism_mk
    (I :
      Ideal
        (FiniteRootCoefficientRing
          (Module.finrank ℂ V)))
    (g : G) (x : P.integralLattice b) :
    P.residueLatticeAutomorphism b I g
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (P.integralLatticeEndomorphism b g x) :=
  rfl

/-- The descended operators obey the projective multiplication law,
whose scalar is exactly the residue of the finite factor set. -/
theorem residueLatticeAutomorphism_mul
    (I :
      Ideal
        (FiniteRootCoefficientRing
          (Module.finrank ℂ V)))
    (g h : G) :
    P.residueLatticeAutomorphism b I g *
        P.residueLatticeAutomorphism b I h =
      unitScalarLinearEquiv
          (P.finiteFactorResidueReduction I g h) *
        P.residueLatticeAutomorphism b I (g * h) := by
  let quotientTorsion :=
    Module.isTorsionBySet_quotient_ideal_smul
      (P.integralLattice b) I
  let quotientSMul :
      SMul
        (FiniteRootCoefficientRing
          (Module.finrank ℂ V) ⧸ I)
        (P.residueLattice b I) :=
    quotientTorsion.hasSMul
  letI :
      Module
        (FiniteRootCoefficientRing
          (Module.finrank ℂ V) ⧸ I)
        (P.residueLattice b I) :=
    quotientTorsion.module
  ext x
  obtain ⟨x, rfl⟩ :=
    Submodule.mkQ_surjective
      (I •
        (⊤ :
          Submodule
            (FiniteRootCoefficientRing
              (Module.finrank ℂ V))
            (P.integralLattice b)))
      x
  change
    Submodule.Quotient.mk
        (P.integralLatticeEndomorphism b g
          (P.integralLatticeEndomorphism b h x)) =
      (@SMul.smul
        (FiniteRootCoefficientRing
          (Module.finrank ℂ V) ⧸ I)
        (P.residueLattice b I)
        quotientSMul
        (P.finiteFactorResidueReduction I g h :
          FiniteRootCoefficientRing
            (Module.finrank ℂ V) ⧸ I)
        (Submodule.Quotient.mk
            (p := I •
              (⊤ :
                Submodule
                  (FiniteRootCoefficientRing
                    (Module.finrank ℂ V))
                  (P.integralLattice b)))
            (P.integralLatticeEndomorphism b (g * h) x) :
          P.residueLattice b I) :
        P.residueLattice b I)
  rw [finiteFactorResidueReduction_apply]
  rw [FiniteRootCoefficientRing.residueRootHom_val]
  change
    Submodule.Quotient.mk
        (P.integralLatticeEndomorphism b g
          (P.integralLatticeEndomorphism b h x)) =
      Submodule.Quotient.mk
        (FiniteRootCoefficientRing.root
            (Module.finrank ℂ V)
            (P.finiteFactorSet g h) •
          P.integralLatticeEndomorphism b (g * h) x)
  exact
    congrArg
      (Submodule.Quotient.mk
        (p := I •
          (⊤ :
            Submodule
              (FiniteRootCoefficientRing
                (Module.finrank ℂ V))
              (P.integralLattice b))))
      (LinearMap.congr_fun
        (P.integralLatticeEndomorphism_mul b g h) x)

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
