/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CharacterDegreeDivisibility
import McKayConjecture.Character.CentralUnit
import McKayConjecture.Character.KernelQuotient
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Character-degree divisibility by the character-center index

For an irreducible complex character `χ` of a finite group, this file
defines its character center and proves

`χ.degree ∣ χ.characterCenter.index`.

The faithful case refines ordinary character-degree divisibility. The
group center acts on conjugacy classes by multiplication. On the classes
where `χ` is nonzero this action is free, and the algebraic-integer class
terms in the ordinary proof are constant on its orbits. Grouping those
terms extracts a factor of `|Z(G)|`, proving that the degree divides
`|G : Z(G)|`.

For general `χ`, the character center is defined intrinsically as the
preimage of the center of `G ⧸ ker χ`. Descent to the faithful quotient
then gives the stated theorem.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

universe u

variable {G : Type u} [Group G]

def centerSMulConjClass
    (z : Subgroup.center G) :
    ConjClasses G → ConjClasses G :=
  Quotient.lift
    (fun g : G => ConjClasses.mk ((z : G) * g))
    (fun a b hab => by
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      obtain ⟨c, hc⟩ := isConj_iff.mp hab
      rw [isConj_iff]
      refine ⟨c, ?_⟩
      have hcz : c * (z : G) = (z : G) * c :=
        Subgroup.mem_center_iff.mp z.property c
      calc
        c * ((z : G) * a) * c⁻¹ =
            (c * (z : G)) * a * c⁻¹ := by group
        _ = ((z : G) * c) * a * c⁻¹ := by rw [hcz]
        _ = (z : G) * (c * a * c⁻¹) := by group
        _ = (z : G) * b := by rw [hc])

@[simp]
theorem centerSMulConjClass_mk
    (z : Subgroup.center G) (g : G) :
    centerSMulConjClass z (ConjClasses.mk g) =
      ConjClasses.mk ((z : G) * g) :=
  rfl

instance centerConjClassesSMul :
    SMul (Subgroup.center G) (ConjClasses G) where
  smul := centerSMulConjClass

instance centerConjClassesMulAction :
    MulAction (Subgroup.center G) (ConjClasses G) where
  one_smul C := by
    refine Quotient.inductionOn C ?_
    intro g
    change
      ConjClasses.mk (((1 : Subgroup.center G) : G) * g) =
        ConjClasses.mk g
    simp
  mul_smul z w C := by
    refine Quotient.inductionOn C ?_
    intro g
    change
      ConjClasses.mk (((z * w : Subgroup.center G) : G) * g) =
        ConjClasses.mk ((z : G) * ((w : G) * g))
    simp [mul_assoc]

theorem centralUnit_inv
    (χ : IrreducibleCharacter G)
    (z : G) (hz : z ∈ Subgroup.center G) :
    χ.centralUnit z⁻¹ (inv_mem hz) =
      (χ.centralUnit z hz)⁻¹ := by
  apply mul_left_cancel
    (a := χ.centralUnit z hz)
  rw [← χ.centralUnit_mul z z⁻¹ hz (inv_mem hz)]
  simp

theorem values_center_mul
    (χ : IrreducibleCharacter G)
    (z : G) (hz : z ∈ Subgroup.center G)
    (g : G) :
    χ.values (z * g) =
      (χ.centralUnit z hz : ℂ) * χ.values g := by
  have hzAction :
      χ.realization.ρ z =
        (χ.centralUnit z hz : ℂ) •
          (LinearMap.id :
            Module.End ℂ χ.realization) := by
    have h :=
      congrArg LinearEquiv.toLinearMap
        (χ.realizationAction_eq_centralUnit z hz)
    calc
      χ.realization.ρ z =
          (CharacterTriple.scalarLinearEquiv
            ℂ χ.realization
            (χ.centralUnit z hz)).toLinearMap := by
        simpa only [
          CharacterTriple.AssociatedExistence.realizationAction_toLinearMap]
          using h
      _ =
          (χ.centralUnit z hz : ℂ) •
            (LinearMap.id :
              Module.End ℂ χ.realization) := by
        ext v
        simp
  calc
    χ.values (z * g) =
        χ.realization.character (z * g) :=
      (congrFun χ.realization_character (z * g)).symm
    _ =
        LinearMap.trace ℂ χ.realization
          (χ.realization.ρ (z * g)) := rfl
    _ =
        LinearMap.trace ℂ χ.realization
          ((χ.centralUnit z hz : ℂ) •
            χ.realization.ρ g) := by
      congr 1
      rw [map_mul, hzAction]
      ext v
      simp
    _ =
        (χ.centralUnit z hz : ℂ) *
          LinearMap.trace ℂ χ.realization
            (χ.realization.ρ g) := by
      rw [map_smul]
      rfl
    _ =
        (χ.centralUnit z hz : ℂ) * χ.values g := by
      change
        (χ.centralUnit z hz : ℂ) *
            χ.realization.character g =
          (χ.centralUnit z hz : ℂ) * χ.values g
      rw [χ.realization_character]

theorem values_inv_center_mul
    (χ : IrreducibleCharacter G)
    (z : G) (hz : z ∈ Subgroup.center G)
    (g : G) :
    χ.values (z * g)⁻¹ =
      ((χ.centralUnit z hz : ℂ)⁻¹) *
        χ.values g⁻¹ := by
  rw [mul_inv_rev]
  have hcomm : g⁻¹ * z⁻¹ = z⁻¹ * g⁻¹ :=
    Subgroup.mem_center_iff.mp (inv_mem hz) g⁻¹
  rw [hcomm, χ.values_center_mul z⁻¹ (inv_mem hz) g⁻¹,
    χ.centralUnit_inv z hz]
  rfl

/-- The value of a character on a bundled conjugacy class. -/
def classValue
    (χ : IrreducibleCharacter G) (C : ConjClasses G) : ℂ :=
  ClassFunction.toConjClassesLinearMap χ.toClassFunction C

@[simp]
theorem classValue_mk
    (χ : IrreducibleCharacter G) (g : G) :
    χ.classValue (ConjClasses.mk g) = χ.values g :=
  rfl

/-- The value at the inverse of a representative of a bundled conjugacy
class. -/
def inverseClassValue
    (χ : IrreducibleCharacter G) : ConjClasses G → ℂ :=
  Quotient.lift
    (fun g : G => χ.values g⁻¹)
    (fun a b hab => by
      obtain ⟨c, hc⟩ := isConj_iff.mp hab
      have hc_inv :
          (c * a * c⁻¹)⁻¹ =
            c * a⁻¹ * c⁻¹ := by group
      calc
        χ.values a⁻¹ =
            χ.toClassFunction a⁻¹ := rfl
        _ =
            χ.toClassFunction
              (c * a⁻¹ * c⁻¹) :=
          (ClassFunction.conj_apply
            χ.toClassFunction a⁻¹ c).symm
        _ =
            χ.values b⁻¹ := by
          rw [← hc, hc_inv]
          rfl)

@[simp]
theorem inverseClassValue_mk
    (χ : IrreducibleCharacter G) (g : G) :
    χ.inverseClassValue (ConjClasses.mk g) =
      χ.values g⁻¹ :=
  rfl

theorem classValue_center_smul
    (χ : IrreducibleCharacter G)
    (z : Subgroup.center G) (C : ConjClasses G) :
    χ.classValue (z • C) =
      (χ.centralUnit z z.property : ℂ) *
        χ.classValue C := by
  refine Quotient.inductionOn C ?_
  intro g
  exact χ.values_center_mul z z.property g

theorem inverseClassValue_center_smul
    (χ : IrreducibleCharacter G)
    (z : Subgroup.center G) (C : ConjClasses G) :
    χ.inverseClassValue (z • C) =
      ((χ.centralUnit z z.property : ℂ)⁻¹) *
        χ.inverseClassValue C := by
  refine Quotient.inductionOn C ?_
  intro g
  exact χ.values_inv_center_mul z z.property g

/-- Central multiplication gives an equivalence between the carriers of
the corresponding conjugacy classes. -/
def centerMulCarrierEquiv
    (z : Subgroup.center G) (C : ConjClasses G) :
    C.carrier ≃ (z • C).carrier where
  toFun x := ⟨(z : G) * (x : G), by
    rw [ConjClasses.mem_carrier_iff_mk_eq]
    change
      z • ConjClasses.mk (x : G) = z • C
    have hx :
        ConjClasses.mk (x : G) = C :=
      ConjClasses.mem_carrier_iff_mk_eq.mp x.property
    rw [hx]⟩
  invFun x := ⟨(z : G)⁻¹ * (x : G), by
    rw [ConjClasses.mem_carrier_iff_mk_eq]
    have hx :
        ConjClasses.mk (x : G) = z • C :=
      ConjClasses.mem_carrier_iff_mk_eq.mp x.property
    have hzx :=
      congrArg (fun D : ConjClasses G => z⁻¹ • D) hx
    rw [inv_smul_smul] at hzx
    change
      ConjClasses.mk ((z : G)⁻¹ * (x : G)) = C
    exact hzx⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

theorem natCard_carrier_center_smul
    (z : Subgroup.center G) (C : ConjClasses G) :
    Nat.card (z • C).carrier = Nat.card C.carrier :=
  Nat.card_congr (centerMulCarrierEquiv z C).symm

/-- Conjugacy classes on which the character does not vanish. -/
def NonzeroConjClasses
    (χ : IrreducibleCharacter G) :=
  {C : ConjClasses G // χ.classValue C ≠ 0}

def centerSMulNonzeroConjClass
    (χ : IrreducibleCharacter G)
    (z : Subgroup.center G)
    (C : χ.NonzeroConjClasses) :
    χ.NonzeroConjClasses :=
  ⟨z • C.1, by
    rw [χ.classValue_center_smul]
    exact mul_ne_zero (Units.ne_zero _) C.2⟩

instance centerNonzeroConjClassesSMul
    (χ : IrreducibleCharacter G) :
    SMul (Subgroup.center G) χ.NonzeroConjClasses where
  smul := centerSMulNonzeroConjClass χ

instance centerNonzeroConjClassesMulAction
    (χ : IrreducibleCharacter G) :
    MulAction (Subgroup.center G) χ.NonzeroConjClasses where
  one_smul C := by
    apply Subtype.ext
    exact one_smul (Subgroup.center G) C.1
  mul_smul z w C := by
    apply Subtype.ext
    exact mul_smul z w C.1

theorem centralUnit_eq_one_of_smul_nonzeroConjClass_eq
    (χ : IrreducibleCharacter G)
    (z : Subgroup.center G)
    (C : χ.NonzeroConjClasses)
    (h : z • C = C) :
    χ.centralUnit z z.property = 1 := by
  apply Units.ext
  have hvalue :=
    congrArg
      (fun D : χ.NonzeroConjClasses =>
        χ.classValue D.1) h
  change
    χ.classValue (z • C.1) =
      χ.classValue C.1 at hvalue
  rw [χ.classValue_center_smul] at hvalue
  apply mul_right_cancel₀ C.2
  simpa using hvalue

theorem center_smul_nonzeroConjClass_eq_imp_eq_one
    (χ : IrreducibleCharacter G)
    (hfaithful : χ.IsFaithful)
    (z : Subgroup.center G)
    (C : χ.NonzeroConjClasses)
    (h : z • C = C) :
    z = 1 := by
  have hunit :
      χ.centralUnit z z.property = 1 :=
    χ.centralUnit_eq_one_of_smul_nonzeroConjClass_eq z C h
  apply Subtype.ext
  apply hfaithful
  have haction :=
    congrArg LinearEquiv.toLinearMap
      (χ.realizationAction_eq_centralUnit z z.property)
  calc
    χ.realization.ρ (z : G) =
        (CharacterTriple.scalarLinearEquiv
          ℂ χ.realization
          (χ.centralUnit z z.property)).toLinearMap := by
      simpa only [
        CharacterTriple.AssociatedExistence.realizationAction_toLinearMap]
        using haction
    _ =
        (CharacterTriple.scalarLinearEquiv
          ℂ χ.realization 1).toLinearMap := by
      rw [hunit]
    _ = χ.realization.ρ (1 : G) := by
      rw [map_one]
      ext v
      simp

theorem stabilizer_nonzeroConjClass_eq_bot
    (χ : IrreducibleCharacter G)
    (hfaithful : χ.IsFaithful)
    (C : χ.NonzeroConjClasses) :
    MulAction.stabilizer (Subgroup.center G) C = ⊥ := by
  ext z
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
  exact ⟨χ.center_smul_nonzeroConjClass_eq_imp_eq_one
    hfaithful z C, fun hz => by rw [hz, one_smul]⟩

section Finite

variable [Finite G]

noncomputable local instance : DecidableEq G := Classical.decEq G
noncomputable local instance (p : Prop) :
    Decidable p := Classical.propDecidable p
noncomputable local instance : Fintype G := Fintype.ofFinite G
noncomputable local instance (C : ConjClasses G) :
    Fintype C.carrier := Fintype.ofFinite _
noncomputable local instance :
    Fintype (Subgroup.center G) := Fintype.ofFinite _
noncomputable local instance (χ : IrreducibleCharacter G) :
    Fintype χ.NonzeroConjClasses := by
  classical
  apply Fintype.subtype
    (Finset.univ.filter
      (fun C : ConjClasses G => χ.classValue C ≠ 0))
  intro C
  simp
noncomputable local instance (χ : IrreducibleCharacter G) :
    Fintype
      (MulAction.orbitRel.Quotient
        (Subgroup.center G) χ.NonzeroConjClasses) :=
  Fintype.ofFinite _
noncomputable local instance
    (χ : IrreducibleCharacter G)
    (q : MulAction.orbitRel.Quotient
      (Subgroup.center G) χ.NonzeroConjClasses) :
    Fintype q.orbit := Fintype.ofFinite _

omit [Finite G] in
theorem classValue_eq_classRepresentative
    (χ : IrreducibleCharacter G) (C : ConjClasses G) :
    χ.classValue C =
      χ.values (classRepresentative C) := by
  calc
    χ.classValue C =
        χ.classValue
          (ConjClasses.mk (classRepresentative C)) := by
      rw [mk_classRepresentative]
    _ = χ.values (classRepresentative C) := rfl

omit [Finite G] in
theorem inverseClassValue_eq_classRepresentative
    (χ : IrreducibleCharacter G) (C : ConjClasses G) :
    χ.inverseClassValue C =
      χ.values (classRepresentative C)⁻¹ := by
  calc
    χ.inverseClassValue C =
        χ.inverseClassValue
          (ConjClasses.mk (classRepresentative C)) := by
      rw [mk_classRepresentative]
    _ = χ.values (classRepresentative C)⁻¹ := rfl

theorem classSumScalar_mul_degree_eq_card_mul_classValue
    (χ : IrreducibleCharacter G) (C : ConjClasses G) :
    classSumScalar χ C * (χ.degree : ℂ) =
      (Nat.card C.carrier : ℂ) * χ.classValue C := by
  rw [classSumScalar_mul_degree,
    classValue_eq_classRepresentative]

theorem classSumScalar_center_smul
    (χ : IrreducibleCharacter G)
    (z : Subgroup.center G) (C : ConjClasses G) :
    classSumScalar χ (z • C) =
      (χ.centralUnit z z.property : ℂ) *
        classSumScalar χ C := by
  apply mul_right_cancel₀
    (Nat.cast_ne_zero.mpr χ.degree_ne_zero)
  calc
    classSumScalar χ (z • C) * (χ.degree : ℂ) =
        (Nat.card (z • C).carrier : ℂ) *
          χ.classValue (z • C) :=
      classSumScalar_mul_degree_eq_card_mul_classValue χ (z • C)
    _ =
        (Nat.card C.carrier : ℂ) *
          ((χ.centralUnit z z.property : ℂ) *
            χ.classValue C) := by
      rw [natCard_carrier_center_smul,
        χ.classValue_center_smul]
    _ =
        (χ.centralUnit z z.property : ℂ) *
          ((Nat.card C.carrier : ℂ) *
            χ.classValue C) := by ring
    _ =
        (χ.centralUnit z z.property : ℂ) *
          (classSumScalar χ C * (χ.degree : ℂ)) := by
      rw [classSumScalar_mul_degree_eq_card_mul_classValue]
    _ =
        ((χ.centralUnit z z.property : ℂ) *
          classSumScalar χ C) * (χ.degree : ℂ) := by
      ring

/-- The algebraic-integer summand in the character-degree proof, now
viewed intrinsically on a conjugacy class. -/
def classDegreeTerm
    (χ : IrreducibleCharacter G) (C : ConjClasses G) : ℂ :=
  classSumScalar χ C * χ.inverseClassValue C

theorem isIntegral_classDegreeTerm
    (χ : IrreducibleCharacter G) (C : ConjClasses G) :
    IsIntegral ℤ (χ.classDegreeTerm C) := by
  simpa [classDegreeTerm,
    inverseClassValue_eq_classRepresentative] using
    (isIntegral_classSumScalar χ C).mul
      (χ.isIntegral_value (classRepresentative C)⁻¹)

theorem classDegreeTerm_center_smul
    (χ : IrreducibleCharacter G)
    (z : Subgroup.center G) (C : ConjClasses G) :
    χ.classDegreeTerm (z • C) =
      χ.classDegreeTerm C := by
  rw [classDegreeTerm, classSumScalar_center_smul,
    χ.inverseClassValue_center_smul, classDegreeTerm]
  have hu :
      (χ.centralUnit z z.property : ℂ) ≠ 0 :=
    Units.ne_zero _
  field_simp [hu]

theorem classDegreeTerm_eq_zero_of_classValue_eq_zero
    (χ : IrreducibleCharacter G) (C : ConjClasses G)
    (hC : χ.classValue C = 0) :
    χ.classDegreeTerm C = 0 := by
  have hscalar : classSumScalar χ C = 0 := by
    apply mul_right_cancel₀
      (Nat.cast_ne_zero.mpr χ.degree_ne_zero)
    rw [zero_mul,
      classSumScalar_mul_degree_eq_card_mul_classValue,
      hC, mul_zero]
  rw [classDegreeTerm, hscalar, zero_mul]

theorem sum_classDegreeTerm_eq_sum_nonzeroConjClasses
    (χ : IrreducibleCharacter G) :
    ∑ C : ConjClasses G, χ.classDegreeTerm C =
      ∑ C : χ.NonzeroConjClasses,
        χ.classDegreeTerm C.1 := by
  classical
  let s : Finset (ConjClasses G) :=
    Finset.univ.filter (fun C => χ.classValue C ≠ 0)
  have hfilter :
      (∑ C ∈ s, χ.classDegreeTerm C) =
        ∑ C : χ.NonzeroConjClasses,
          χ.classDegreeTerm C.1 := by
    apply Finset.sum_subtype s
    intro C
    simp [s]
  rw [← hfilter]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro C _ hC
  apply χ.classDegreeTerm_eq_zero_of_classValue_eq_zero
  simpa [s] using hC

theorem sum_nonzeroConjClasses_eq_center_card_nsmul_orbitSum
    (χ : IrreducibleCharacter G)
    (hfaithful : χ.IsFaithful) :
    (∑ C : χ.NonzeroConjClasses,
        χ.classDegreeTerm C.1) =
      Nat.card (Subgroup.center G) •
        ∑ q : MulAction.orbitRel.Quotient
            (Subgroup.center G) χ.NonzeroConjClasses,
          χ.classDegreeTerm q.out.1 := by
  let Q :=
    MulAction.orbitRel.Quotient
      (Subgroup.center G) χ.NonzeroConjClasses
  let e :=
    MulAction.selfEquivSigmaOrbits'
      (Subgroup.center G) χ.NonzeroConjClasses
  have hterm
      (q : Q) (x : q.orbit) :
      χ.classDegreeTerm x.1.1 =
        χ.classDegreeTerm q.out.1 := by
    have hxq :
        Quotient.mk'' (x :
          χ.NonzeroConjClasses) = q :=
      MulAction.orbitRel.Quotient.mem_orbit.mp x.property
    have houtq :
        Quotient.mk'' q.out = q :=
      Quotient.out_eq' q
    have hrel :
        (MulAction.orbitRel
          (Subgroup.center G)
          χ.NonzeroConjClasses)
            (x : χ.NonzeroConjClasses) q.out :=
      Quotient.exact (hxq.trans houtq.symm)
    rw [MulAction.orbitRel_apply] at hrel
    obtain ⟨z, hz⟩ := hrel
    rw [← hz]
    exact χ.classDegreeTerm_center_smul z q.out.1
  have hcard (q : Q) :
      Nat.card q.orbit =
        Nat.card (Subgroup.center G) := by
    calc
      Nat.card q.orbit =
          Nat.card
            (MulAction.orbit
              (Subgroup.center G) q.out) :=
        Nat.card_congr
          (Equiv.setCongr
            (MulAction.orbitRel.Quotient.orbit_eq_orbit_out
              q Quotient.out_eq'))
      _ =
          Nat.card
            ((Subgroup.center G) ⧸
              MulAction.stabilizer
                (Subgroup.center G) q.out) :=
        Nat.card_congr
          (MulAction.orbitEquivQuotientStabilizer
            (Subgroup.center G) q.out)
      _ =
          Nat.card
            ((Subgroup.center G) ⧸
              (⊥ : Subgroup (Subgroup.center G))) := by
        rw [χ.stabilizer_nonzeroConjClass_eq_bot
          hfaithful q.out]
      _ = Nat.card (Subgroup.center G) :=
        Nat.card_congr
          (QuotientGroup.quotientEquivSelf
            (Subgroup.center G))
  calc
    (∑ C : χ.NonzeroConjClasses,
        χ.classDegreeTerm C.1) =
        ∑ y : (Σ q : Q, q.orbit),
          χ.classDegreeTerm y.2.1.1 := by
      apply Fintype.sum_equiv e
      intro C
      rfl
    _ =
        ∑ q : Q, ∑ x : q.orbit,
          χ.classDegreeTerm x.1.1 :=
      Fintype.sum_sigma
        (fun y : (Σ q : Q, q.orbit) =>
          χ.classDegreeTerm y.2.1.1)
    _ =
        ∑ q : Q, ∑ _x : q.orbit,
          χ.classDegreeTerm q.out.1 := by
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro x _
      exact hterm q x
    _ =
        ∑ q : Q,
          Nat.card (Subgroup.center G) •
            χ.classDegreeTerm q.out.1 := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card, hcard q]
    _ =
        Nat.card (Subgroup.center G) •
          ∑ q : Q, χ.classDegreeTerm q.out.1 :=
      Finset.sum_nsmul Finset.univ
        (Nat.card (Subgroup.center G))
        (fun q : Q => χ.classDegreeTerm q.out.1)

theorem degree_mul_classDegreeTermSum_eq_card
    (χ : IrreducibleCharacter G) :
    (χ.degree : ℂ) *
        ∑ C : ConjClasses G, χ.classDegreeTerm C =
      (Nat.card G : ℂ) := by
  simpa [classDegreeTerm,
    inverseClassValue_eq_classRepresentative] using
    degree_mul_classScalarSum_eq_card χ

theorem isIntegral_centerOrbitDegreeWitness
    (χ : IrreducibleCharacter G) :
    IsIntegral ℤ
      (∑ q : MulAction.orbitRel.Quotient
          (Subgroup.center G) χ.NonzeroConjClasses,
        χ.classDegreeTerm q.out.1) := by
  apply IsIntegral.sum
  intro q _
  exact χ.isIntegral_classDegreeTerm q.out.1

/-- For a faithful irreducible character, its degree divides the index of
the group center. -/
theorem degree_dvd_center_index_of_isFaithful
    (χ : IrreducibleCharacter G)
    (hfaithful : χ.IsFaithful) :
    χ.degree ∣ (Subgroup.center G).index := by
  let T : ℂ :=
    ∑ q : MulAction.orbitRel.Quotient
        (Subgroup.center G) χ.NonzeroConjClasses,
      χ.classDegreeTerm q.out.1
  have hgrouped :
      (∑ C : ConjClasses G, χ.classDegreeTerm C) =
        (Nat.card (Subgroup.center G) : ℂ) * T := by
    rw [χ.sum_classDegreeTerm_eq_sum_nonzeroConjClasses,
      χ.sum_nonzeroConjClasses_eq_center_card_nsmul_orbitSum
        hfaithful]
    simp only [nsmul_eq_mul, T]
  have htotal :
      (χ.degree : ℂ) *
          (∑ C : ConjClasses G, χ.classDegreeTerm C) =
        (Nat.card G : ℂ) :=
    χ.degree_mul_classDegreeTermSum_eq_card
  have hcenterCard :
      (Nat.card (Subgroup.center G) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hdegreeT :
      (χ.degree : ℂ) * T =
        ((Subgroup.center G).index : ℂ) := by
    apply mul_right_cancel₀ hcenterCard
    calc
      ((χ.degree : ℂ) * T) *
            (Nat.card (Subgroup.center G) : ℂ) =
          (χ.degree : ℂ) *
            ((Nat.card (Subgroup.center G) : ℂ) * T) := by
        ring
      _ =
          (χ.degree : ℂ) *
            ∑ C : ConjClasses G,
              χ.classDegreeTerm C := by
        rw [← hgrouped]
      _ = (Nat.card G : ℂ) := htotal
      _ =
          ((Subgroup.center G).index : ℂ) *
            (Nat.card (Subgroup.center G) : ℂ) := by
        exact_mod_cast
          (Subgroup.center G).index_mul_card.symm
  have hdegree : (χ.degree : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr χ.degree_ne_zero
  have hTrat :
      ∃ q : ℚ, T = (q : ℂ) := by
    refine
      ⟨((Subgroup.center G).index : ℚ) /
          (χ.degree : ℚ), ?_⟩
    apply mul_left_cancel₀ hdegree
    rw [hdegreeT]
    push_cast
    field_simp [χ.degree_ne_zero]
  obtain ⟨n, hn⟩ :=
    ClassFunction.exists_int_eq_of_isIntegral_of_eq_rat
      (by
        simpa [T] using
          χ.isIntegral_centerOrbitDegreeWitness)
      hTrat
  have hcomplex :
      ((Subgroup.center G).index : ℂ) =
        (χ.degree : ℂ) * (n : ℂ) := by
    rw [← hdegreeT, hn]
  have hint :
      ((Subgroup.center G).index : ℤ) =
        (χ.degree : ℤ) * n := by
    exact_mod_cast hcomplex
  have hz :
      (χ.degree : ℤ) ∣
        ((Subgroup.center G).index : ℤ) :=
    ⟨n, hint⟩
  exact_mod_cast hz

end Finite

/-- The center of an irreducible character, intrinsically defined as the
preimage of the center after quotienting by the character kernel. -/
def characterCenter (χ : IrreducibleCharacter G) : Subgroup G :=
  (Subgroup.center (G ⧸ χ.kernel)).comap
    (QuotientGroup.mk' χ.kernel)

instance characterCenterNormal (χ : IrreducibleCharacter G) :
    χ.characterCenter.Normal :=
  Subgroup.Normal.comap
    (Subgroup.instNormalCenter)
    (QuotientGroup.mk' χ.kernel)

theorem kernel_le_characterCenter
    (χ : IrreducibleCharacter G) :
    χ.kernel ≤ χ.characterCenter := by
  intro g hg
  rw [characterCenter, Subgroup.mem_comap,
    Subgroup.mem_center_iff]
  intro q
  have hq :
      (QuotientGroup.mk' χ.kernel) g = 1 :=
    (QuotientGroup.eq_one_iff g).mpr hg
  rw [hq]
  simp

theorem center_le_characterCenter
    (χ : IrreducibleCharacter G) :
    Subgroup.center G ≤ χ.characterCenter := by
  intro z hz
  rw [characterCenter, Subgroup.mem_comap,
    Subgroup.mem_center_iff]
  intro q
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective χ.kernel q
  rw [← map_mul, ← map_mul]
  exact congrArg
    (QuotientGroup.mk' χ.kernel)
    (Subgroup.mem_center_iff.mp hz g)

theorem characterCenter_index
    (χ : IrreducibleCharacter G) :
    χ.characterCenter.index =
      (Subgroup.center (G ⧸ χ.kernel)).index := by
  exact
    (Subgroup.center (G ⧸ χ.kernel)).index_comap_of_surjective
      (QuotientGroup.mk'_surjective χ.kernel)

section FiniteCharacterCenter

variable [Finite G]

/-- The degree of an irreducible character divides the index of its
character center. -/
theorem degree_dvd_characterCenter_index
    (χ : IrreducibleCharacter G) :
    χ.degree ∣ χ.characterCenter.index := by
  rw [χ.characterCenter_index,
    ← χ.faithfulQuotientCharacter_degree]
  exact
    χ.faithfulQuotientCharacter.degree_dvd_center_index_of_isFaithful
      χ.faithfulQuotientCharacter_isFaithful

end FiniteCharacterCenter

end IrreducibleCharacter
end McKayConjecture
