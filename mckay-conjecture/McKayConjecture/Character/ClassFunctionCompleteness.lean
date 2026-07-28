/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Burnside
import McKayConjecture.Character.ClassFunctionGroupAlgebra
import McKayConjecture.Character.Construction
import McKayConjecture.Character.SignedIrreducibilityCriterion

/-!
# Completeness of irreducible complex characters

For a finite group, the irreducible complex characters form a basis of the
space of class functions.  The proof here is the standard semisimple
group-algebra argument:

* a class function orthogonal to every irreducible character determines a
  central group-algebra element whose trace on every simple module is zero;
* Schur's lemma makes its action on each simple module scalar, hence zero;
* Maschke semisimplicity says the regular module is spanned by its simple
  submodules, so the central element itself is zero.

The resulting Fourier expansion is then specialized to integral
coefficients for the cyclic Glauberman argument.
-/

noncomputable section

open scoped BigOperators MonoidAlgebra
open CategoryTheory

namespace McKayConjecture
namespace ClassFunction

variable {G : Type} [Group G] [Finite G]

/-- A class function whose pairing with every irreducible character
vanishes is zero. -/
theorem eq_zero_of_normalizedPairing_irreducible_eq_zero
    (f : ClassFunction G)
    (hpair :
      ∀ χ : IrreducibleCharacter G,
        normalizedPairing f χ.toClassFunction = 0) :
    f = 0 := by
  letI : Fintype G := Fintype.ofFinite G
  letI : NeZero (Nat.card G : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let R := MonoidAlgebra ℂ G
  letI : Algebra ℂ R := by
    dsimp [R]
    infer_instance
  have hsimple :
      ∀ (S : Submodule R R), IsSimpleModule R S →
        ∀ s : S, groupAlgebraElement f * (s : R) = 0 := by
    intro S hS
    letI : IsSimpleModule R S := hS
    letI : Module.Finite ℂ S :=
      Module.Finite.of_injective
        (S.subtype.restrictScalars ℂ)
        S.subtype_injective
    let ρ : Representation ℂ G S :=
      Representation.ofModule' (k := ℂ) (G := G) S
    have hAlg :
        Representation.asAlgebraHom ρ =
          Algebra.lsmul ℂ ℂ S := by
      simp [ρ, Representation.asAlgebraHom_def,
        Representation.ofModule']
    let e : ρ.asModule ≃ₗ[R] S :=
      { ρ.asModuleEquiv with
        map_smul' := by
          intro r x
          change
            ρ.asModuleEquiv (r • x) =
              r • ρ.asModuleEquiv x
          exact
            (ρ.asModuleEquiv_map_smul r x).trans
              (by rw [hAlg]; rfl) }
    letI : IsSimpleModule R ρ.asModule :=
      IsSimpleModule.congr e
    let V : FDRep ℂ G := FDRep.of ρ
    letI : Representation.IsIrreducible ρ :=
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr
        inferInstance
    letI : Simple V :=
      FDRep.simple_of_representation_isIrreducible ρ
    let χ : IrreducibleCharacter G :=
      IrreducibleCharacter.ofSimple V
    have htrace :
        LinearMap.trace ℂ V (groupAlgebraAction f V) = 0 := by
      rw [trace_groupAlgebraAction]
      have hcf :
          ofFDRep V = χ.toClassFunction := by
        apply ClassFunction.ext
        intro g
        rfl
      rw [hcf, hpair χ, mul_zero]
    obtain ⟨c, hc⟩ :=
      endomorphism_simple_eq_smul_id ℂ
        (groupAlgebraEndomorphism f V)
    have hcLinear :
        c • LinearMap.id =
          groupAlgebraAction f V := by
      simpa only [underlyingLinearMap_smul,
        underlyingLinearMap_id,
        underlyingLinearMap_groupAlgebraEndomorphism] using
        congrArg
          (underlyingLinearMap (G := G))
          hc
    have hcdim :
        c * (Module.finrank ℂ V : ℂ) = 0 := by
      calc
        c * (Module.finrank ℂ V : ℂ) =
            LinearMap.trace ℂ V (c • LinearMap.id) := by
              simp
        _ = LinearMap.trace ℂ V
              (groupAlgebraAction f V) := by
                rw [hcLinear]
        _ = 0 := htrace
    have hdim :
        (Module.finrank ℂ V : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr
        (IrreducibleCharacter.degree_pos χ).ne'
    have hc0 : c = 0 :=
      (mul_eq_zero.mp hcdim).resolve_right hdim
    intro s
    let v : V := s
    have hv :
        groupAlgebraAction f V v = 0 := by
      rw [← hcLinear, hc0]
      simp
    have hvAlg :
        Representation.asAlgebraHom ρ
            (groupAlgebraElement f) s = 0 := by
      simpa [groupAlgebraAction, V, v] using hv
    rw [hAlg] at hvAlg
    exact congrArg Subtype.val hvAlg
  let T : R →ₗ[R] R :=
    LinearMap.mulRight R (groupAlgebraElement f)
  have htop :
      (⊤ : Submodule R R) ≤ LinearMap.ker T := by
    rw [← IsSemisimpleModule.sSup_simples_eq_top R R]
    apply sSup_le
    intro S hS
    intro x hx
    rw [LinearMap.mem_ker]
    change x * groupAlgebraElement f = 0
    rw [(groupAlgebraElement_commute f x).eq.symm]
    exact hsimple S hS ⟨x, hx⟩
  have hzero : groupAlgebraElement f = 0 := by
    have h1 := htop (show (1 : R) ∈ (⊤ : Submodule R R) by simp)
    rw [LinearMap.mem_ker] at h1
    simpa [T] using h1
  exact (groupAlgebraElement_eq_zero_iff f).mp hzero

/-- If all Fourier coefficients of a class function are prescribed
integers, then it is the corresponding integral generalized character. -/
theorem eq_integerCharacterCombination_of_normalizedPairing_eq_int
    (f : ClassFunction G)
    (c : IrreducibleCharacter G → ℤ)
    (h :
      ∀ χ : IrreducibleCharacter G,
        normalizedPairing f χ.toClassFunction =
          (c χ : ℂ)) :
    f =
      IrreducibleCharacter.integerCharacterCombination c := by
  apply sub_eq_zero.mp
  apply
    eq_zero_of_normalizedPairing_irreducible_eq_zero
  intro χ
  rw [map_sub, LinearMap.sub_apply]
  change
    normalizedPairing f χ.toClassFunction -
      normalizedPairing
        (IrreducibleCharacter.integerCharacterCombination c)
        χ.toClassFunction = 0
  rw [h,
    IrreducibleCharacter.normalizedPairing_integerCharacterCombination_irreducible]
  exact sub_self _

/-- Pointwise integrality of all irreducible Fourier coefficients produces
an integral irreducible-character expansion. -/
theorem exists_integerCharacterCombination_of_pairings_integral
    (f : ClassFunction G)
    (h :
      ∀ χ : IrreducibleCharacter G,
        ∃ z : ℤ,
          normalizedPairing f χ.toClassFunction =
            (z : ℂ)) :
    ∃ c : IrreducibleCharacter G → ℤ,
      f =
        IrreducibleCharacter.integerCharacterCombination c := by
  choose c hc using h
  exact
    ⟨c,
      eq_integerCharacterCombination_of_normalizedPairing_eq_int
        f c hc⟩

end ClassFunction
end McKayConjecture
