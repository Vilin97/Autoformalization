/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalar
import McKayConjecture.Character.ClassFunctionGroupAlgebra
import McKayConjecture.Character.ClassFunctionPairingIntegrality
import McKayConjecture.Character.FiniteOrderTraceIntegrality
import Mathlib.GroupTheory.ClassEquation
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Divisibility of an irreducible character degree

This file proves the ordinary character-degree divisibility theorem

`χ.degree ∣ |G|`

for an irreducible complex character `χ` of a finite group `G`.

The algebraic-integrality step uses a short module-finiteness argument.
An integral conjugacy-class sum is integral because `ℤ[G]` is finite as a
`ℤ`-module. Mapping it into the chosen irreducible realization, Schur's
lemma makes its action scalar; injectivity of the scalar action then shows
that scalar to be an algebraic integer. Character orthogonality finishes
the usual rational-algebraic-integer argument.
-/

noncomputable section

open scoped BigOperators MonoidAlgebra
open CategoryTheory

namespace McKayConjecture

universe u

namespace IrreducibleCharacter

variable {G : Type u} [Group G] [Finite G]

noncomputable local instance : DecidableEq G := Classical.decEq G
noncomputable local instance characterDegreePropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p
noncomputable local instance : Fintype G := Fintype.ofFinite G
noncomputable local instance (C : ConjClasses G) :
    Fintype C.carrier := Fintype.ofFinite C.carrier

/-- The integral group-algebra sum of one conjugacy class. -/
def integralClassSum (C : ConjClasses G) : MonoidAlgebra ℤ G :=
  ∑ g : C.carrier, MonoidAlgebra.single (g : G) 1

/-- The complex group-algebra sum of one conjugacy class. -/
def complexClassSum (C : ConjClasses G) : MonoidAlgebra ℂ G :=
  ∑ g : C.carrier, MonoidAlgebra.single (g : G) 1

theorem map_integralClassSum (C : ConjClasses G) :
    (MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ))
        (integralClassSum C) =
      complexClassSum C := by
  simp [integralClassSum, complexClassSum]

theorem isIntegral_complexClassSum (C : ConjClasses G) :
    IsIntegral ℤ (complexClassSum C) := by
  rw [← map_integralClassSum C]
  exact
    (IsIntegral.of_finite ℤ (integralClassSum C)).map
      ((MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ)).toIntAlgHom)

@[simp]
theorem complexClassSum_coeff (C : ConjClasses G) (x : G) :
    (complexClassSum C).coeff x =
      if x ∈ C.carrier then 1 else 0 := by
  classical
  simp only [complexClassSum, MonoidAlgebra.coeff_sum,
    MonoidAlgebra.coeff_single]
  change
    (∑ g : C.carrier,
      Finsupp.single (g : G) (1 : ℂ)) x =
        if x ∈ C.carrier then 1 else 0
  rw [Finsupp.finsetSum_apply]
  by_cases hx : x ∈ C.carrier
  · simp only [if_pos hx]
    rw [Finset.sum_eq_single ⟨x, hx⟩]
    · simp
    · intro g _ hg
      apply Finsupp.single_eq_of_ne
      exact fun h ↦ hg (Subtype.ext h.symm)
    · simp
  · simp only [if_neg hx]
    apply Finset.sum_eq_zero
    intro g _
    apply Finsupp.single_eq_of_ne
    exact fun h ↦ hx (h ▸ g.property)

theorem complexClassSum_commute_single
    (C : ConjClasses G) (h : G) :
    complexClassSum C * MonoidAlgebra.single h 1 =
      MonoidAlgebra.single h 1 * complexClassSum C := by
  classical
  ext x
  simp only [MonoidAlgebra.coeff_mul_single_apply,
    MonoidAlgebra.coeff_single_mul_apply, one_mul, mul_one,
    complexClassSum_coeff]
  have hmk :
      ConjClasses.mk (x * h⁻¹) =
        ConjClasses.mk (h⁻¹ * x) := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    rw [isConj_iff]
    exact ⟨h⁻¹, by simp [mul_assoc]⟩
  rw [ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mem_carrier_iff_mk_eq, hmk]

theorem complexClassSum_mem_center (C : ConjClasses G) :
    complexClassSum C ∈
      Submonoid.center (MonoidAlgebra ℂ G) := by
  rw [Submonoid.mem_center_iff]
  intro z
  induction z using MonoidAlgebra.induction_on with
  | of h =>
      exact (complexClassSum_commute_single C h).symm
  | add x y hx hy =>
      calc
        (x + y) * complexClassSum C =
            x * complexClassSum C + y * complexClassSum C := add_mul x y _
        _ = complexClassSum C * x + complexClassSum C * y := by rw [hx, hy]
        _ = complexClassSum C * (x + y) := (mul_add _ x y).symm
  | smul c x hx =>
      calc
        (c • x) * complexClassSum C =
            c • (x * complexClassSum C) := by
              exact Algebra.smul_mul_assoc c x _
        _ = c • (complexClassSum C * x) := by rw [hx]
        _ = complexClassSum C * (c • x) := by
              exact (Algebra.mul_smul_comm c _ x).symm

/-- The action of a conjugacy-class sum on the chosen realization. -/
def classSumAction
    (χ : IrreducibleCharacter G) (C : ConjClasses G) :
    Module.End ℂ χ.realization :=
  Representation.asAlgebraHom χ.realization.ρ
    (complexClassSum C)

/-- The class-sum action as an equivariant endomorphism. -/
def classSumEndomorphism
    (χ : IrreducibleCharacter G) (C : ConjClasses G) :
    χ.realization ⟶ χ.realization := by
  let F : Representation.IntertwiningMap
      χ.realization.ρ χ.realization.ρ :=
    Representation.IntertwiningMap.centralAlgebraMul
      χ.realization.ρ (complexClassSum_mem_center C)
  exact
    ⟨InducedCategory.homMk
        (ModuleCat.ofHom F.toLinearMap),
      fun g ↦ by
        ext x
        exact LinearMap.congr_fun (F.2 g) x⟩

@[simp]
theorem underlyingLinearMap_classSumEndomorphism
    (χ : IrreducibleCharacter G) (C : ConjClasses G) :
    ClassFunction.underlyingLinearMap
        (classSumEndomorphism χ C) =
      classSumAction χ C :=
  rfl

/-- The scalar by which one central conjugacy-class sum acts. -/
def classSumScalar
    (χ : IrreducibleCharacter G) (C : ConjClasses G) : ℂ :=
  Classical.choose
    (endomorphism_simple_eq_smul_id ℂ
      (classSumEndomorphism χ C))

theorem classSumScalar_smul_id
    (χ : IrreducibleCharacter G) (C : ConjClasses G) :
    classSumScalar χ C •
        (LinearMap.id : Module.End ℂ χ.realization) =
      classSumAction χ C := by
  have h :=
    Classical.choose_spec
      (endomorphism_simple_eq_smul_id ℂ
        (classSumEndomorphism χ C))
  have h' := congrArg
    (fun f : χ.realization ⟶ χ.realization ↦
      ClassFunction.underlyingLinearMap f) h
  simpa [classSumScalar] using h'

theorem isIntegral_classSumScalar
    (χ : IrreducibleCharacter G) (C : ConjClasses G) :
    IsIntegral ℤ (classSumScalar χ C) := by
  letI : Nontrivial χ.realization :=
    CliffordRestriction.nontrivial_of_simple χ.realization
  let scalarMap :
      ℂ →ₐ[ℤ] Module.End ℂ χ.realization :=
    IsScalarTower.toAlgHom ℤ ℂ
      (Module.End ℂ χ.realization)
  have hmap :
      scalarMap (classSumScalar χ C) =
        classSumAction χ C := by
    rw [show scalarMap (classSumScalar χ C) =
        classSumScalar χ C •
          (LinearMap.id :
            Module.End ℂ χ.realization) by
      ext v
      simp [scalarMap]]
    exact classSumScalar_smul_id χ C
  have haction :
      IsIntegral ℤ (classSumAction χ C) :=
    (isIntegral_complexClassSum C).map
      (Representation.asAlgebraHom χ.realization.ρ)
  apply
    (isIntegral_algHom_iff scalarMap
      (FaithfulSMul.algebraMap_injective ℂ
        (Module.End ℂ χ.realization))).mp
  rw [hmap]
  exact haction

/-- A chosen representative of a bundled conjugacy class. -/
def classRepresentative (C : ConjClasses G) : G :=
  Classical.choose (ConjClasses.mk_surjective C)

omit [Finite G] in
@[simp]
theorem mk_classRepresentative (C : ConjClasses G) :
    ConjClasses.mk (classRepresentative C) = C :=
  Classical.choose_spec (ConjClasses.mk_surjective C)

omit [Finite G] in
theorem classRepresentative_mem (C : ConjClasses G) :
    classRepresentative C ∈ C.carrier := by
  rw [ConjClasses.mem_carrier_iff_mk_eq,
    mk_classRepresentative]

omit [Finite G] in
theorem values_eq_classRepresentative
    (χ : IrreducibleCharacter G) (C : ConjClasses G)
    (g : C.carrier) :
    χ.values (g : G) =
      χ.values (classRepresentative C) := by
  have hmkG : ConjClasses.mk (g : G) = C :=
    (ConjClasses.mem_carrier_iff_mk_eq).mp g.property
  have hmk :
      ConjClasses.mk (g : G) =
        ConjClasses.mk (classRepresentative C) := by
    rw [hmkG, mk_classRepresentative]
  obtain ⟨a, ha⟩ :=
    isConj_iff.mp
      (ConjClasses.mk_eq_mk_iff_isConj.mp hmk)
  calc
    χ.values (g : G) =
        χ.toClassFunction (g : G) := rfl
    _ =
        χ.toClassFunction
          (a * (g : G) * a⁻¹) :=
      (ClassFunction.conj_apply
        χ.toClassFunction (g : G) a).symm
    _ =
        χ.values (classRepresentative C) := by
      rw [ha]
      rfl

omit [Finite G] in
theorem values_inv_eq_classRepresentative_inv
    (χ : IrreducibleCharacter G) (C : ConjClasses G)
    (g : C.carrier) :
    χ.values (g : G)⁻¹ =
      χ.values (classRepresentative C)⁻¹ := by
  have hmkG : ConjClasses.mk (g : G) = C :=
    (ConjClasses.mem_carrier_iff_mk_eq).mp g.property
  have hmk :
      ConjClasses.mk (g : G) =
        ConjClasses.mk (classRepresentative C) := by
    rw [hmkG, mk_classRepresentative]
  obtain ⟨a, ha⟩ :=
    isConj_iff.mp
      (ConjClasses.mk_eq_mk_iff_isConj.mp hmk)
  have ha_inv :
      a * (g : G)⁻¹ * a⁻¹ =
        (classRepresentative C)⁻¹ := by
    rw [← ha]
    group
  calc
    χ.values (g : G)⁻¹ =
        χ.toClassFunction (g : G)⁻¹ := rfl
    _ =
        χ.toClassFunction
          (a * (g : G)⁻¹ * a⁻¹) :=
      (ClassFunction.conj_apply
        χ.toClassFunction (g : G)⁻¹ a).symm
    _ =
        χ.values (classRepresentative C)⁻¹ := by
      rw [ha_inv]
      rfl

theorem trace_classSumAction
    (χ : IrreducibleCharacter G) (C : ConjClasses G) :
    LinearMap.trace ℂ χ.realization
        (classSumAction χ C) =
      (Nat.card C.carrier : ℂ) *
        χ.values (classRepresentative C) := by
  rw [classSumAction, complexClassSum]
  simp only [map_sum, Representation.asAlgebraHom_single,
    one_smul, map_sum]
  change
    (∑ x : C.carrier,
      χ.realization.character (x : G)) =
      (Nat.card C.carrier : ℂ) *
        χ.values (classRepresentative C)
  rw [χ.realization_character]
  simp_rw [values_eq_classRepresentative χ C]
  rw [Finset.sum_const, Nat.card_eq_fintype_card]
  simp

theorem classSumScalar_mul_degree
    (χ : IrreducibleCharacter G) (C : ConjClasses G) :
    classSumScalar χ C * (χ.degree : ℂ) =
      (Nat.card C.carrier : ℂ) *
        χ.values (classRepresentative C) := by
  rw [← trace_classSumAction χ C,
    ← classSumScalar_smul_id χ C, map_smul,
    LinearMap.trace_id, χ.realization_finrank]
  rfl

/-- Conjugacy classes, together with their elements, partition the group. -/
def conjugacyClassSigmaEquiv :
    (Σ C : ConjClasses G, C.carrier) ≃ G where
  toFun x := x.2
  invFun g :=
    ⟨ConjClasses.mk g, ⟨g, ConjClasses.mem_carrier_mk⟩⟩
  left_inv x := by
    cases x with
    | mk C g =>
      have hC :
          ConjClasses.mk (g : G) = C :=
        ConjClasses.mem_carrier_iff_mk_eq.mp
          g.property
      apply Sigma.ext hC
      rw [Subtype.heq_iff_coe_eq
        (fun x => by
          change
            x ∈ (ConjClasses.mk (g : G)).carrier ↔
              x ∈ C.carrier
          rw [hC])]
  right_inv g := rfl

theorem sum_eq_sum_conjugacyClasses
    {R : Type*} [AddCommMonoid R] (f : G → R) :
    ∑ g : G, f g =
      ∑ C : ConjClasses G,
        ∑ g : C.carrier, f (g : G) := by
  symm
  calc
    (∑ C : ConjClasses G,
        ∑ g : C.carrier, f (g : G)) =
        ∑ x : (Σ C : ConjClasses G, C.carrier),
          f (conjugacyClassSigmaEquiv x) :=
      (Fintype.sum_sigma
        (fun x : (Σ C : ConjClasses G, C.carrier) ↦
          f (conjugacyClassSigmaEquiv x))).symm
    _ = ∑ g : G, f g :=
      (conjugacyClassSigmaEquiv (G := G)).sum_comp f

theorem character_self_sum_eq_card
    (χ : IrreducibleCharacter G) :
    ∑ g : G, χ.values g * χ.values g⁻¹ =
      (Nat.card G : ℂ) := by
  have hpair :=
    ClassFunction.normalizedPairing_irreducible_self χ
  change
    (Nat.card G : ℂ)⁻¹ *
        ∑ g : G, χ.values g * χ.values g⁻¹ =
      1 at hpair
  have hcardne : (Nat.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp [hcardne] at hpair
  exact hpair

theorem degree_mul_classScalarSum_eq_card
    (χ : IrreducibleCharacter G) :
    (χ.degree : ℂ) *
        ∑ C : ConjClasses G,
          classSumScalar χ C *
            χ.values (classRepresentative C)⁻¹ =
      (Nat.card G : ℂ) := by
  rw [← character_self_sum_eq_card χ,
    sum_eq_sum_conjugacyClasses]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  simp_rw [values_eq_classRepresentative χ C]
  simp_rw [values_inv_eq_classRepresentative_inv χ C]
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card]
  simp only [nsmul_eq_mul]
  calc
    (χ.degree : ℂ) *
          (classSumScalar χ C *
            χ.values (classRepresentative C)⁻¹) =
        (classSumScalar χ C * (χ.degree : ℂ)) *
          χ.values (classRepresentative C)⁻¹ := by
      ring
    _ =
        ((Nat.card C.carrier : ℂ) *
          χ.values (classRepresentative C)) *
            χ.values (classRepresentative C)⁻¹ := by
      rw [classSumScalar_mul_degree]
    _ =
        (Nat.card C.carrier : ℂ) *
          (χ.values (classRepresentative C) *
            χ.values (classRepresentative C)⁻¹) := by
      ring

theorem isIntegral_degreeQuotientWitness
    (χ : IrreducibleCharacter G) :
    IsIntegral ℤ
      (∑ C : ConjClasses G,
        classSumScalar χ C *
          χ.values (classRepresentative C)⁻¹) := by
  apply IsIntegral.sum
  intro C _
  exact
    (isIntegral_classSumScalar χ C).mul
      (χ.isIntegral_value
        (classRepresentative C)⁻¹)

/-- The degree of an irreducible complex character of a finite group
divides the order of the group. -/
theorem degree_dvd_card
    (χ : IrreducibleCharacter G) :
    χ.degree ∣ Nat.card G := by
  let S : ℂ :=
    ∑ C : ConjClasses G,
      classSumScalar χ C *
        χ.values (classRepresentative C)⁻¹
  have hmul :
      (χ.degree : ℂ) * S =
        (Nat.card G : ℂ) :=
    degree_mul_classScalarSum_eq_card χ
  have hdegree : (χ.degree : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr χ.degree_ne_zero
  have hSrat :
      ∃ q : ℚ, S = (q : ℂ) := by
    refine ⟨(Nat.card G : ℚ) / (χ.degree : ℚ), ?_⟩
    apply (mul_left_cancel₀ hdegree)
    rw [hmul]
    push_cast
    field_simp [χ.degree_ne_zero]
  obtain ⟨n, hn⟩ :=
    ClassFunction.exists_int_eq_of_isIntegral_of_eq_rat
      (isIntegral_degreeQuotientWitness χ) hSrat
  have hcomplex :
      (Nat.card G : ℂ) =
        (χ.degree : ℂ) * (n : ℂ) := by
    have hnS : S = (n : ℂ) := by
      simpa [S] using hn
    rw [← hmul, hnS]
  have hint :
      (Nat.card G : ℤ) =
        (χ.degree : ℤ) * n := by
    exact_mod_cast hcomplex
  have hz :
      (χ.degree : ℤ) ∣ (Nat.card G : ℤ) :=
    ⟨n, hint⟩
  exact_mod_cast hz

end IrreducibleCharacter
end McKayConjecture
