/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ExternalTensor
import McKayConjecture.Character.Finiteness
import McKayConjecture.Character.GallagherCorrespondence
import McKayConjecture.Character.SimpleConstituent
import McKayConjecture.Character.Transport
import McKayConjecture.Character.Trivial

/-!
# Irreducible characters of a direct product

The external tensor product sends a pair of irreducible characters of `G`
and `H` to an irreducible character of `G × H`.  This file records its
character and degree formulas, proves that the resulting map is injective,
and restricts it to characters of `p'`-degree.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace IrreducibleCharacter

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- The external tensor product of two irreducible characters. -/
def externalTensor
    (χ : IrreducibleCharacter G) (ψ : IrreducibleCharacter H) :
    IrreducibleCharacter (G × H) := by
  letI : Simple (FDRep.externalTensor χ.realization ψ.realization) :=
    FDRep.externalTensor_simple χ.realization ψ.realization
  exact ofSimple (FDRep.externalTensor χ.realization ψ.realization)

@[simp]
theorem externalTensor_values
    (χ : IrreducibleCharacter G) (ψ : IrreducibleCharacter H)
    (g : G) (h : H) :
    (externalTensor χ ψ).values (g, h) =
      χ.values g * ψ.values h := by
  change
    (FDRep.externalTensor χ.realization ψ.realization).character (g, h) =
      χ.values g * ψ.values h
  rw [FDRep.externalTensor_character,
    χ.realization_character, ψ.realization_character]

@[simp]
theorem externalTensor_degree
    (χ : IrreducibleCharacter G) (ψ : IrreducibleCharacter H) :
    (externalTensor χ ψ).degree = χ.degree * ψ.degree := by
  change
    Module.finrank ℂ
        (FDRep.externalTensor χ.realization ψ.realization) =
      χ.degree * ψ.degree
  rw [FDRep.externalTensor_finrank,
    χ.realization_finrank, ψ.realization_finrank]

/-- The map from pairs of irreducible characters to irreducible characters
of the direct product. -/
def directProductMap :
    IrreducibleCharacter G × IrreducibleCharacter H →
      IrreducibleCharacter (G × H) :=
  fun χψ ↦ externalTensor χψ.1 χψ.2

@[simp]
theorem directProductMap_apply
    (χ : IrreducibleCharacter G) (ψ : IrreducibleCharacter H) :
    directProductMap (χ, ψ) = externalTensor χ ψ :=
  rfl

/-- Equality of external tensor products determines the first factor. -/
theorem externalTensor_left_injective [Finite G]
    {χ₁ χ₂ : IrreducibleCharacter G}
    {ψ₁ ψ₂ : IrreducibleCharacter H}
    (heq : externalTensor χ₁ ψ₁ = externalTensor χ₂ ψ₂) :
    χ₁ = χ₂ := by
  letI : Fintype G := Fintype.ofFinite G
  by_contra hχ
  have hvalues :
      (ψ₁.degree : ℂ) • χ₁.values =
        (ψ₂.degree : ℂ) • χ₂.values := by
    funext g
    change
      (ψ₁.degree : ℂ) * χ₁.values g =
        (ψ₂.degree : ℂ) * χ₂.values g
    simpa [mul_comm] using
      congrArg
        (fun ξ : IrreducibleCharacter (G × H) ↦
          ξ.values (g, 1)) heq
  have hpair :=
    congrArg χ₁.pairingFunctional hvalues
  rw [LinearMap.map_smul, LinearMap.map_smul,
    pairingFunctional_self,
    pairingFunctional_eq_zero_of_ne χ₂ χ₁ (Ne.symm hχ)] at hpair
  simp [ψ₁.degree_ne_zero] at hpair

/-- Equality of external tensor products determines the second factor. -/
theorem externalTensor_right_injective [Finite H]
    {χ₁ χ₂ : IrreducibleCharacter G}
    {ψ₁ ψ₂ : IrreducibleCharacter H}
    (heq : externalTensor χ₁ ψ₁ = externalTensor χ₂ ψ₂) :
    ψ₁ = ψ₂ := by
  letI : Fintype H := Fintype.ofFinite H
  by_contra hψ
  have hvalues :
      (χ₁.degree : ℂ) • ψ₁.values =
        (χ₂.degree : ℂ) • ψ₂.values := by
    funext h
    change
      (χ₁.degree : ℂ) * ψ₁.values h =
        (χ₂.degree : ℂ) * ψ₂.values h
    simpa using
      congrArg
        (fun ξ : IrreducibleCharacter (G × H) ↦
          ξ.values (1, h)) heq
  have hpair :=
    congrArg ψ₁.pairingFunctional hvalues
  rw [LinearMap.map_smul, LinearMap.map_smul,
    pairingFunctional_self,
    pairingFunctional_eq_zero_of_ne ψ₂ ψ₁ (Ne.symm hψ)] at hpair
  simp [χ₁.degree_ne_zero] at hpair

/-- The external tensor product map is injective for finite groups. -/
theorem directProductMap_injective [Finite G] [Finite H] :
    Function.Injective
      (directProductMap :
        IrreducibleCharacter G × IrreducibleCharacter H →
          IrreducibleCharacter (G × H)) := by
  rintro ⟨χ₁, ψ₁⟩ ⟨χ₂, ψ₂⟩ heq
  exact Prod.ext
    (externalTensor_left_injective heq)
    (externalTensor_right_injective heq)

/-- For a prime `p`, an external tensor product has `p'`-degree exactly when
both factors do. -/
theorem externalTensor_isPPrimeDegree_iff
    (p : ℕ) [Fact p.Prime]
    (χ : IrreducibleCharacter G) (ψ : IrreducibleCharacter H) :
    (externalTensor χ ψ).IsPPrimeDegree p ↔
      χ.IsPPrimeDegree p ∧ ψ.IsPPrimeDegree p := by
  rw [IsPPrimeDegree, externalTensor_degree,
    IsPPrimeDegree, IsPPrimeDegree]
  simpa only [not_or] using
    not_congr ((Fact.out : p.Prime).dvd_mul)

/-- External tensor product on irreducible characters of `p'`-degree. -/
def externalTensorPPrime
    (p : ℕ) [Fact p.Prime]
    (χ : PPrimeIrreducibleCharacter G p)
    (ψ : PPrimeIrreducibleCharacter H p) :
    PPrimeIrreducibleCharacter (G × H) p :=
  ⟨externalTensor χ.1 ψ.1,
    (externalTensor_isPPrimeDegree_iff p χ.1 ψ.1).2
      ⟨χ.2, ψ.2⟩⟩

@[simp]
theorem externalTensorPPrime_coe
    (p : ℕ) [Fact p.Prime]
    (χ : PPrimeIrreducibleCharacter G p)
    (ψ : PPrimeIrreducibleCharacter H p) :
    (externalTensorPPrime p χ ψ).1 =
      externalTensor χ.1 ψ.1 :=
  rfl

/-- The external tensor product map on `p'`-degree irreducible characters. -/
def directProductPPrimeMap
    (p : ℕ) [Fact p.Prime] :
    PPrimeIrreducibleCharacter G p ×
        PPrimeIrreducibleCharacter H p →
      PPrimeIrreducibleCharacter (G × H) p :=
  fun χψ ↦ externalTensorPPrime p χψ.1 χψ.2

/-- The external tensor product map remains injective after restricting to
characters of `p'`-degree. -/
theorem directProductPPrimeMap_injective
    [Finite G] [Finite H]
    (p : ℕ) [Fact p.Prime] :
    Function.Injective
      (directProductPPrimeMap (G := G) (H := H) p) := by
  rintro ⟨χ₁, ψ₁⟩ ⟨χ₂, ψ₂⟩ heq
  apply Prod.ext <;> apply Subtype.ext
  · exact externalTensor_left_injective
      (congrArg Subtype.val heq)
  · exact externalTensor_right_injective
      (congrArg Subtype.val heq)

/-! ### Exhaustivity in the carrier universe used by `FDRep` -/

section Exhaustivity

variable {G H : Type} [Finite G] [Finite H] [Group G] [Group H]

/-- The first direct factor as the kernel of the second projection. -/
abbrev directProductFirstFactor : Subgroup (G × H) :=
  (MonoidHom.snd G H).ker

/-- The first direct factor is canonically isomorphic to `G`. -/
def directProductFirstFactorEquiv :
    directProductFirstFactor (G := G) (H := H) ≃* G where
  toFun x := x.1.1
  invFun g := ⟨(g, 1), by rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hx :
          x.1 ∈
            (⊤ : Subgroup G).prod (⊥ : Subgroup H) := by
          simpa [directProductFirstFactor] using x.property
      exact
        (Subgroup.mem_bot.mp
          (Subgroup.mem_prod.mp hx).2).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The quotient by the first direct factor is canonically isomorphic to
the second factor. -/
def directProductQuotientEquiv :
    (G × H) ⧸ directProductFirstFactor (G := G) (H := H) ≃* H :=
  QuotientGroup.quotientKerEquivOfRightInverse
    (MonoidHom.snd G H) (fun h ↦ (1, h)) (fun _ ↦ rfl)

omit [Finite G] [Finite H] in
@[simp]
theorem directProductQuotientEquiv_mk
    (g : G) (h : H) :
    directProductQuotientEquiv
        (G := G) (H := H)
        (QuotientGroup.mk'
          (directProductFirstFactor (G := G) (H := H))
          (g, h)) =
      h :=
  rfl

/-- Every irreducible character of the first factor extends across the
direct product by making the second factor act trivially. -/
def directProductFirstFactorExtension
    (χ : IrreducibleCharacter
      (directProductFirstFactor (G := G) (H := H))) :
    IrreducibleCharacter (G × H) :=
  externalTensor
    (χ.comap
      (directProductFirstFactorEquiv (G := G) (H := H)).symm)
    (trivial H)

omit [Finite G] [Finite H] in
/-- The preceding external tensor product really restricts to the original
character of the first-factor subgroup. -/
theorem directProductFirstFactorExtension_isExtension
    (χ : IrreducibleCharacter
      (directProductFirstFactor (G := G) (H := H))) :
    IsExtensionAlong
      (directProductFirstFactor (G := G) (H := H)).subtype
      χ (directProductFirstFactorExtension χ) := by
  intro x
  rw [directProductFirstFactorExtension,
    externalTensor_values, comap_values, trivial_values, mul_one]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · have hx :
        x.1 ∈
          (⊤ : Subgroup G).prod (⊥ : Subgroup H) := by
        simpa [directProductFirstFactor] using x.property
    exact
      (Subgroup.mem_bot.mp
        (Subgroup.mem_prod.mp hx).2).symm

/-- Every irreducible character of a finite direct product is an external
tensor product.  The proof is Gallagher's correspondence for the first
direct factor. -/
theorem directProductMap_surjective :
    Function.Surjective
      (directProductMap :
        IrreducibleCharacter G × IrreducibleCharacter H →
          IrreducibleCharacter (G × H)) := by
  intro φ
  let N := directProductFirstFactor (G := G) (H := H)
  let χN : IrreducibleCharacter N :=
    normalSimpleConstituent φ N
  let χG : IrreducibleCharacter G :=
    χN.comap
      (directProductFirstFactorEquiv
        (G := G) (H := H)).symm
  let ψK : IrreducibleCharacter (G × H) :=
    directProductFirstFactorExtension χN
  have hψ :
      IsExtensionAlong N.subtype χN ψK :=
    directProductFirstFactorExtension_isExtension χN
  have hφ :
      CliffordCorrespondence.LiesOverAlong
        N.subtype χN φ :=
    normalSimpleConstituent_liesOver φ N
  let betaQ :
      IrreducibleCharacter ((G × H) ⧸ N) :=
    (gallagherCorrespondence hψ).symm ⟨φ, hφ⟩
  let ψH : IrreducibleCharacter H :=
    betaQ.comap
      (directProductQuotientEquiv
        (G := G) (H := H)).symm
  refine ⟨(χG, ψH), ?_⟩
  have hGallagher :
      gallagherTensorCharacter hψ betaQ = φ := by
    exact congrArg Subtype.val
      ((gallagherCorrespondence hψ).apply_symm_apply
        ⟨φ, hφ⟩)
  apply IrreducibleCharacter.ext
  funext x
  obtain ⟨g, h⟩ := x
  rw [directProductMap_apply, externalTensor_values]
  calc
    χG.values g * ψH.values h =
        ψK.values (g, h) *
          betaQ.values
            (QuotientGroup.mk' N (g, h)) := by
      have hquot :
          (directProductQuotientEquiv
              (G := G) (H := H)).symm h =
            QuotientGroup.mk' N (g, h) := by
        apply
          (directProductQuotientEquiv
            (G := G) (H := H)).injective
        simpa [N] using
          (directProductQuotientEquiv_mk
            (G := G) (H := H) g h).symm
      rw [show ψK =
          directProductFirstFactorExtension χN from rfl,
        directProductFirstFactorExtension,
        externalTensor_values, trivial_values, mul_one]
      change
        χG.values g *
            betaQ.values
              ((directProductQuotientEquiv
                (G := G) (H := H)).symm h) =
          χG.values g *
            betaQ.values
              (QuotientGroup.mk' N (g, h))
      rw [hquot]
    _ = (gallagherTensorCharacter hψ betaQ).values (g, h) := by
      rw [gallagherTensorCharacter_values]
    _ = φ.values (g, h) := by
      rw [hGallagher]

/-- Irreducible characters of a finite direct product are canonically
equivalent to pairs of irreducible characters of the factors. -/
def directProductEquiv :
    IrreducibleCharacter G × IrreducibleCharacter H ≃
      IrreducibleCharacter (G × H) :=
  Equiv.ofBijective directProductMap
    ⟨directProductMap_injective,
      directProductMap_surjective⟩

@[simp]
theorem directProductEquiv_apply
    (χ : IrreducibleCharacter G)
    (ψ : IrreducibleCharacter H) :
    directProductEquiv (χ, ψ) = externalTensor χ ψ :=
  rfl

/-- The external tensor product map on `p'`-degree irreducibles is
surjective. -/
theorem directProductPPrimeMap_surjective
    (p : ℕ) [Fact p.Prime] :
    Function.Surjective
      (directProductPPrimeMap
        (G := G) (H := H) p) := by
  intro φ
  obtain ⟨⟨χ, ψ⟩, hχψ⟩ :=
    directProductMap_surjective
      (G := G) (H := H) φ.1
  have hpairs :
      χ.IsPPrimeDegree p ∧ ψ.IsPPrimeDegree p := by
    apply
      (externalTensor_isPPrimeDegree_iff
        p χ ψ).mp
    have hext :
        externalTensor χ ψ = φ.1 := by
      simpa [directProductMap] using hχψ
    rw [hext]
    exact φ.2
  refine
    ⟨(⟨χ, hpairs.1⟩, ⟨ψ, hpairs.2⟩), ?_⟩
  apply Subtype.ext
  exact hχψ

/-- `p'`-degree irreducible characters of a finite direct product are
canonically equivalent to pairs of `p'`-degree irreducible characters of
the factors. -/
def directProductPPrimeEquiv
    (p : ℕ) [Fact p.Prime] :
    PPrimeIrreducibleCharacter G p ×
        PPrimeIrreducibleCharacter H p ≃
      PPrimeIrreducibleCharacter (G × H) p :=
  Equiv.ofBijective
    (directProductPPrimeMap (G := G) (H := H) p)
    ⟨directProductPPrimeMap_injective p,
      directProductPPrimeMap_surjective p⟩

@[simp]
theorem directProductPPrimeEquiv_apply
    (p : ℕ) [Fact p.Prime]
    (χ : PPrimeIrreducibleCharacter G p)
    (ψ : PPrimeIrreducibleCharacter H p) :
    directProductPPrimeEquiv p (χ, ψ) =
      externalTensorPPrime p χ ψ :=
  rfl

end Exhaustivity

end IrreducibleCharacter
end McKayConjecture
