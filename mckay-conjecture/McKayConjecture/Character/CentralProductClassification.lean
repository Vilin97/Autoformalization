/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DirectProductCorrespondence
import McKayConjecture.Character.QuotientDescent

/-!
# Classification of irreducible characters of an internal central product

For an internal central product `P`, irreducible characters of its image
subgroup are classified by pairs of irreducible characters of the two
factors whose external tensor character is trivial on the multiplication
kernel.

The classification is the composite of:

* the direct-product character equivalence;
* descent through the multiplication kernel; and
* transport across `P.quotientEquiv`.

The exhaustivity theorem for direct products and quotient descent currently
live in the carrier universe used by `FDRep`, so the classification section
keeps the boundary `G : Type` explicit.
-/

noncomputable section

namespace McKayConjecture
namespace InternalCentralProduct

open IrreducibleCharacter

variable {G : Type} [Group G] [Finite G]
variable (P : InternalCentralProduct G)

/-! ### Compatible pairs -/

/-- A pair of irreducible characters of the two central factors is
compatible when its external tensor character is trivial on the
multiplication kernel.

This uses representation-level triviality through
`IrreducibleCharacter.TrivialOn`; it is not merely a condition on character
values. -/
abbrev CompatibleCharacterPair :=
  {χψ :
      IrreducibleCharacter P.left ×
        IrreducibleCharacter P.right //
    (externalTensor χψ.1 χψ.2).TrivialOn P.kernel}

/-- Character-level compatibility is exactly the existing condition that
the chosen external tensor representation is trivial on the multiplication
kernel. -/
theorem kernelCompatible_iff_externalTensor_trivialOn
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right) :
    P.KernelCompatible χ ψ ↔
      (externalTensor χ ψ).TrivialOn P.kernel := by
  letI :
      CategoryTheory.Simple
        (FDRep.externalTensor χ.realization ψ.realization) :=
    FDRep.externalTensor_simple χ.realization ψ.realization
  change
    FDRep.IsTrivialOn
        (FDRep.externalTensor χ.realization ψ.realization)
        P.kernel ↔
      (externalTensor χ ψ).TrivialOn P.kernel
  exact
    (trivialOn_ofSimple_iff P.kernel
      (FDRep.externalTensor χ.realization ψ.realization)).symm

/-- The direct-product classification restricts to compatible pairs on
the source and kernel-trivial characters on the target. -/
def compatiblePairEquivKernelTrivial :
    CompatibleCharacterPair P ≃
      TrivialOnCharacters P.kernel :=
  (directProductEquiv
      (G := P.left) (H := P.right)).subtypeEquiv
    (fun χψ => by
      rw [directProductEquiv_apply])

@[simp]
theorem compatiblePairEquivKernelTrivial_apply_coe
    (χψ : CompatibleCharacterPair P) :
    (compatiblePairEquivKernelTrivial P χψ).1 =
      externalTensor χψ.1.1 χψ.1.2 :=
  rfl

@[simp]
theorem compatiblePairEquivKernelTrivial_symm_apply_externalTensor
    (χψ : CompatibleCharacterPair P) :
    (compatiblePairEquivKernelTrivial P).symm
        ⟨externalTensor χψ.1.1 χψ.1.2, χψ.2⟩ =
      χψ := by
  exact (compatiblePairEquivKernelTrivial P).symm_apply_apply χψ

/-- A compatible character pair supplies the representation-level kernel
condition required by the existing central-product character
construction. -/
theorem compatiblePair_kernelCompatible
    (χψ : CompatibleCharacterPair P) :
    P.KernelCompatible χψ.1.1 χψ.1.2 :=
  (P.kernelCompatible_iff_externalTensor_trivialOn
    χψ.1.1 χψ.1.2).2 χψ.2

/-! ### The classification equivalence -/

/-- Compatible pairs classify irreducible characters of the internal
central-product subgroup. -/
def characterClassificationEquiv :
    CompatibleCharacterPair P ≃
      IrreducibleCharacter P.subgroup :=
  (compatiblePairEquivKernelTrivial P).trans <|
    (quotientDescentEquiv P.kernel).symm.trans <|
      comapEquiv P.quotientEquiv.symm

@[simp]
theorem characterClassificationEquiv_apply
    (χψ : CompatibleCharacterPair P) :
    characterClassificationEquiv P χψ =
      ((quotientDescentEquiv P.kernel).symm
          (compatiblePairEquivKernelTrivial P χψ)).comap
        P.quotientEquiv.symm :=
  rfl

@[simp]
theorem characterClassificationEquiv_symm_apply
    (θ : IrreducibleCharacter P.subgroup) :
    (characterClassificationEquiv P).symm θ =
      (compatiblePairEquivKernelTrivial P).symm
        (quotientDescentEquiv P.kernel
          (θ.comap P.quotientEquiv)) :=
  rfl

@[simp]
theorem characterClassificationEquiv_values_multiplication
    (χψ : CompatibleCharacterPair P)
    (z : P.left × P.right) :
    (characterClassificationEquiv P χψ).values
        ⟨P.multiplication z, ⟨z, rfl⟩⟩ =
      χψ.1.1.values z.1 * χψ.1.2.values z.2 := by
  rw [characterClassificationEquiv_apply, comap_values]
  have hq :
      P.quotientEquiv.symm
          ⟨P.multiplication z, ⟨z, rfl⟩⟩ =
        QuotientGroup.mk' P.kernel z := by
    apply P.quotientEquiv.injective
    rw [P.quotientEquiv.apply_symm_apply, P.quotientEquiv_mk]
  rw [hq, quotientDescentEquiv_symm_values_mk,
    compatiblePairEquivKernelTrivial_apply_coe,
    externalTensor_values]

@[simp]
theorem characterClassificationEquiv_degree
    (χψ : CompatibleCharacterPair P) :
    (characterClassificationEquiv P χψ).degree =
      χψ.1.1.degree * χψ.1.2.degree := by
  rw [characterClassificationEquiv_apply, comap_degree,
    quotientDescentEquiv_symm_degree,
    compatiblePairEquivKernelTrivial_apply_coe,
    externalTensor_degree]

/-- The forward map of the classification is the central-product
character already constructed from a representation-level compatible
pair. -/
theorem characterClassificationEquiv_eq_character
    (χψ : CompatibleCharacterPair P) :
    characterClassificationEquiv P χψ =
      P.character χψ.1.1 χψ.1.2
        (P.compatiblePair_kernelCompatible χψ) := by
  apply P.character_unique
  exact P.characterClassificationEquiv_values_multiplication χψ

@[simp]
theorem characterClassificationEquiv_apply_symm_apply
    (θ : IrreducibleCharacter P.subgroup) :
    characterClassificationEquiv P
        ((characterClassificationEquiv P).symm θ) =
      θ :=
  (characterClassificationEquiv P).apply_symm_apply θ

@[simp]
theorem characterClassificationEquiv_symm_apply_apply
    (χψ : CompatibleCharacterPair P) :
    (characterClassificationEquiv P).symm
        (characterClassificationEquiv P χψ) =
      χψ :=
  (characterClassificationEquiv P).symm_apply_apply χψ

@[simp]
theorem characterClassificationEquiv_symm_externalTensor_values
    (θ : IrreducibleCharacter P.subgroup)
    (z : P.left × P.right) :
    (externalTensor
        ((characterClassificationEquiv P).symm θ).1.1
        ((characterClassificationEquiv P).symm θ).1.2).values z =
      θ.values ⟨P.multiplication z, ⟨z, rfl⟩⟩ := by
  rw [externalTensor_values]
  symm
  calc
    θ.values ⟨P.multiplication z, ⟨z, rfl⟩⟩ =
        (characterClassificationEquiv P
          ((characterClassificationEquiv P).symm θ)).values
            ⟨P.multiplication z, ⟨z, rfl⟩⟩ := by
      rw [characterClassificationEquiv_apply_symm_apply]
    _ =
        ((characterClassificationEquiv P).symm θ).1.1.values z.1 *
          ((characterClassificationEquiv P).symm θ).1.2.values z.2 :=
      P.characterClassificationEquiv_values_multiplication
        ((characterClassificationEquiv P).symm θ) z

@[simp]
theorem characterClassificationEquiv_symm_externalTensor_degree
    (θ : IrreducibleCharacter P.subgroup) :
    (externalTensor
        ((characterClassificationEquiv P).symm θ).1.1
        ((characterClassificationEquiv P).symm θ).1.2).degree =
      θ.degree := by
  rw [externalTensor_degree]
  symm
  calc
    θ.degree =
        (characterClassificationEquiv P
          ((characterClassificationEquiv P).symm θ)).degree := by
      rw [characterClassificationEquiv_apply_symm_apply]
    _ =
        ((characterClassificationEquiv P).symm θ).1.1.degree *
          ((characterClassificationEquiv P).symm θ).1.2.degree :=
      P.characterClassificationEquiv_degree
        ((characterClassificationEquiv P).symm θ)

/-! ### The `p'`-degree classification -/

/-- Compatible pairs of `p'`-degree irreducible characters of the two
central factors. -/
abbrev CompatiblePPrimeCharacterPair (p : ℕ) :=
  {χψ :
      PPrimeIrreducibleCharacter P.left p ×
        PPrimeIrreducibleCharacter P.right p //
    (externalTensor χψ.1.1 χψ.2.1).TrivialOn P.kernel}

/-- Forget the `p'`-degree certificates in a compatible pair. -/
def compatiblePPrimePairToCompatiblePair
    (p : ℕ) (χψ : CompatiblePPrimeCharacterPair P p) :
    CompatibleCharacterPair P :=
  ⟨(χψ.1.1.1, χψ.1.2.1), χψ.2⟩

/-- The `p'`-degree direct-product classification restricts to compatible
pairs and kernel-trivial `p'`-degree characters. -/
def compatiblePPrimePairEquivKernelTrivial
    (p : ℕ) [Fact p.Prime] :
    CompatiblePPrimeCharacterPair P p ≃
      PPrimeTrivialOnCharacters P.kernel p :=
  (directProductPPrimeEquiv
      (G := P.left) (H := P.right) p).subtypeEquiv
    (fun χψ => by
      rw [directProductPPrimeEquiv_apply,
        externalTensorPPrime_coe])

@[simp]
theorem compatiblePPrimePairEquivKernelTrivial_apply_coe
    (p : ℕ) [Fact p.Prime]
    (χψ : CompatiblePPrimeCharacterPair P p) :
    (compatiblePPrimePairEquivKernelTrivial P p χψ).1.1 =
      externalTensor χψ.1.1.1 χψ.1.2.1 :=
  rfl

/-- Compatible pairs of `p'`-degree characters classify the `p'`-degree
irreducible characters of the internal central-product subgroup.  The
primality hypothesis is exactly what makes prime-to-`p` degree
coordinatewise under degree multiplication. -/
def pPrimeCharacterClassificationEquiv
    (p : ℕ) [Fact p.Prime] :
    CompatiblePPrimeCharacterPair P p ≃
      PPrimeIrreducibleCharacter P.subgroup p :=
  (compatiblePPrimePairEquivKernelTrivial P p).trans <|
    (pPrimeQuotientDescentEquiv P.kernel p).symm.trans <|
      pPrimeComapEquiv p P.quotientEquiv.symm

@[simp]
theorem pPrimeCharacterClassificationEquiv_apply_coe
    (p : ℕ) [Fact p.Prime]
    (χψ : CompatiblePPrimeCharacterPair P p) :
    (pPrimeCharacterClassificationEquiv P p χψ).1 =
      characterClassificationEquiv P
        (compatiblePPrimePairToCompatiblePair P p χψ) :=
  rfl

@[simp]
theorem pPrimeCharacterClassificationEquiv_values_multiplication
    (p : ℕ) [Fact p.Prime]
    (χψ : CompatiblePPrimeCharacterPair P p)
    (z : P.left × P.right) :
    (pPrimeCharacterClassificationEquiv P p χψ).1.values
        ⟨P.multiplication z, ⟨z, rfl⟩⟩ =
      χψ.1.1.1.values z.1 * χψ.1.2.1.values z.2 := by
  rw [pPrimeCharacterClassificationEquiv_apply_coe]
  exact P.characterClassificationEquiv_values_multiplication
    (compatiblePPrimePairToCompatiblePair P p χψ) z

@[simp]
theorem pPrimeCharacterClassificationEquiv_degree
    (p : ℕ) [Fact p.Prime]
    (χψ : CompatiblePPrimeCharacterPair P p) :
    (pPrimeCharacterClassificationEquiv P p χψ).1.degree =
      χψ.1.1.1.degree * χψ.1.2.1.degree := by
  rw [pPrimeCharacterClassificationEquiv_apply_coe]
  exact P.characterClassificationEquiv_degree
    (compatiblePPrimePairToCompatiblePair P p χψ)

@[simp]
theorem pPrimeCharacterClassificationEquiv_apply_symm_apply
    (p : ℕ) [Fact p.Prime]
    (θ : PPrimeIrreducibleCharacter P.subgroup p) :
    pPrimeCharacterClassificationEquiv P p
        ((pPrimeCharacterClassificationEquiv P p).symm θ) =
      θ :=
  (pPrimeCharacterClassificationEquiv P p).apply_symm_apply θ

@[simp]
theorem pPrimeCharacterClassificationEquiv_symm_apply_apply
    (p : ℕ) [Fact p.Prime]
    (χψ : CompatiblePPrimeCharacterPair P p) :
    (pPrimeCharacterClassificationEquiv P p).symm
        (pPrimeCharacterClassificationEquiv P p χψ) =
      χψ :=
  (pPrimeCharacterClassificationEquiv P p).symm_apply_apply χψ

@[simp]
theorem pPrimeCharacterClassificationEquiv_symm_externalTensor_values
    (p : ℕ) [Fact p.Prime]
    (θ : PPrimeIrreducibleCharacter P.subgroup p)
    (z : P.left × P.right) :
    (externalTensor
        ((pPrimeCharacterClassificationEquiv P p).symm θ).1.1.1
        ((pPrimeCharacterClassificationEquiv P p).symm θ).1.2.1).values z =
      θ.1.values ⟨P.multiplication z, ⟨z, rfl⟩⟩ := by
  rw [externalTensor_values]
  symm
  calc
    θ.1.values ⟨P.multiplication z, ⟨z, rfl⟩⟩ =
        (pPrimeCharacterClassificationEquiv P p
          ((pPrimeCharacterClassificationEquiv P p).symm θ)).1.values
            ⟨P.multiplication z, ⟨z, rfl⟩⟩ := by
      rw [pPrimeCharacterClassificationEquiv_apply_symm_apply]
    _ =
        ((pPrimeCharacterClassificationEquiv P p).symm θ).1.1.1.values z.1 *
          ((pPrimeCharacterClassificationEquiv P p).symm θ).1.2.1.values z.2 :=
      P.pPrimeCharacterClassificationEquiv_values_multiplication p
        ((pPrimeCharacterClassificationEquiv P p).symm θ) z

@[simp]
theorem pPrimeCharacterClassificationEquiv_symm_externalTensor_degree
    (p : ℕ) [Fact p.Prime]
    (θ : PPrimeIrreducibleCharacter P.subgroup p) :
    (externalTensor
        ((pPrimeCharacterClassificationEquiv P p).symm θ).1.1.1
        ((pPrimeCharacterClassificationEquiv P p).symm θ).1.2.1).degree =
      θ.1.degree := by
  rw [externalTensor_degree]
  symm
  calc
    θ.1.degree =
        (pPrimeCharacterClassificationEquiv P p
          ((pPrimeCharacterClassificationEquiv P p).symm θ)).1.degree := by
      rw [pPrimeCharacterClassificationEquiv_apply_symm_apply]
    _ =
        ((pPrimeCharacterClassificationEquiv P p).symm θ).1.1.1.degree *
          ((pPrimeCharacterClassificationEquiv P p).symm θ).1.2.1.degree :=
      P.pPrimeCharacterClassificationEquiv_degree p
        ((pPrimeCharacterClassificationEquiv P p).symm θ)

end InternalCentralProduct
end McKayConjecture
