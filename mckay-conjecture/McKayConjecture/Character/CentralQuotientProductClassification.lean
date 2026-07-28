/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FiniteProductCorrespondence
import McKayConjecture.Character.QuotientDescent

/-!
# Characters of a surjective quotient of a finite product

Let `f : (∀ i, G i) →* H` be surjective, where the index type and all
factor groups are finite.  Irreducible characters of `H` are classified by
families of irreducible characters of the factors whose finite external
tensor character is trivial on `f.ker`.

The target `H` is automatically finite as a surjective image of the finite
indexed product, so a separate `[Finite H]` assumption would be redundant.

The classification is the composite of the finite-product character
equivalence, character descent through `f.ker`, and transport across the
first-isomorphism-theorem equivalence
`((∀ i, G i) ⧸ f.ker) ≃* H`.

The indexed-product exhaustivity theorem currently has a Type-0 boundary,
which is made explicit below.  No centrality assumption on `f.ker` is
needed for this more general quotient statement.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace IrreducibleCharacter

variable {ι : Type} [Fintype ι]
variable (G : ι → Type) [∀ i, Finite (G i)]
variable [∀ i, Group (G i)]
variable {H : Type} [Group H]
variable (f : (∀ i, G i) →* H)

/-! ### Kernel-compatible character families -/

/-- A family is compatible with `f` when its finite external tensor
character is trivial on `f.ker`.

This is the representation-level predicate `TrivialOn`, rather than a
condition merely on character values. -/
abbrev KernelCompatibleCharacterFamily :=
  {χ : ∀ i, IrreducibleCharacter (G i) //
    (finiteExternalTensor χ).TrivialOn f.ker}

/-- The finite-product character equivalence restricts to compatible
families and kernel-trivial product characters. -/
def compatibleFamilyEquivKernelTrivial :
    KernelCompatibleCharacterFamily G f ≃
      TrivialOnCharacters f.ker :=
  (finiteProductEquiv G).subtypeEquiv
    (fun χ => by
      rw [finiteProductEquiv_apply])

@[simp]
theorem compatibleFamilyEquivKernelTrivial_apply_coe
    (χ : KernelCompatibleCharacterFamily G f) :
    (compatibleFamilyEquivKernelTrivial G f χ).1 =
      finiteExternalTensor χ.1 :=
  finiteProductEquiv_apply χ.1

@[simp]
theorem compatibleFamilyEquivKernelTrivial_symm_apply_finiteExternalTensor
    (χ : KernelCompatibleCharacterFamily G f) :
    (compatibleFamilyEquivKernelTrivial G f).symm
        ⟨finiteExternalTensor χ.1, χ.2⟩ =
      χ := by
  have h :
      (⟨finiteExternalTensor χ.1, χ.2⟩ :
        TrivialOnCharacters f.ker) =
        compatibleFamilyEquivKernelTrivial G f χ := by
    apply Subtype.ext
    exact (compatibleFamilyEquivKernelTrivial_apply_coe G f χ).symm
  rw [h]
  exact (compatibleFamilyEquivKernelTrivial G f).symm_apply_apply χ

/-! ### The quotient classification -/

/-- The first-isomorphism-theorem equivalence associated to the
surjection `f`. -/
def surjectiveQuotientEquiv
    (hf : Function.Surjective f) :
    ((∀ i, G i) ⧸ f.ker) ≃* H :=
  QuotientGroup.quotientKerEquivOfSurjective f hf

omit [Fintype ι] [∀ i, Finite (G i)] in
@[simp]
theorem surjectiveQuotientEquiv_mk
    (hf : Function.Surjective f) (g : ∀ i, G i) :
    surjectiveQuotientEquiv G f hf
        (QuotientGroup.mk' f.ker g) =
      f g :=
  rfl

/-- Kernel-compatible irreducible-character families classify the
irreducible characters of the surjective target. -/
def quotientProductCharacterEquiv
    (hf : Function.Surjective f) :
    KernelCompatibleCharacterFamily G f ≃
      IrreducibleCharacter H :=
  (compatibleFamilyEquivKernelTrivial G f).trans <|
    (quotientDescentEquiv f.ker).symm.trans <|
      comapEquiv (surjectiveQuotientEquiv G f hf).symm

@[simp]
theorem quotientProductCharacterEquiv_apply
    (hf : Function.Surjective f)
    (χ : KernelCompatibleCharacterFamily G f) :
    quotientProductCharacterEquiv G f hf χ =
      ((quotientDescentEquiv f.ker).symm
          (compatibleFamilyEquivKernelTrivial G f χ)).comap
        (surjectiveQuotientEquiv G f hf).symm :=
  rfl

@[simp]
theorem quotientProductCharacterEquiv_symm_apply
    (hf : Function.Surjective f)
    (θ : IrreducibleCharacter H) :
    (quotientProductCharacterEquiv G f hf).symm θ =
      (compatibleFamilyEquivKernelTrivial G f).symm
        (quotientDescentEquiv f.ker
          (θ.comap (surjectiveQuotientEquiv G f hf))) :=
  rfl

@[simp]
theorem quotientProductCharacterEquiv_values_apply
    (hf : Function.Surjective f)
    (χ : KernelCompatibleCharacterFamily G f)
    (g : ∀ i, G i) :
    (quotientProductCharacterEquiv G f hf χ).values (f g) =
      ∏ i, (χ.1 i).values (g i) := by
  rw [quotientProductCharacterEquiv_apply, comap_values]
  have hq :
      (surjectiveQuotientEquiv G f hf).symm (f g) =
        QuotientGroup.mk' f.ker g := by
    apply (surjectiveQuotientEquiv G f hf).injective
    rw [(surjectiveQuotientEquiv G f hf).apply_symm_apply,
      surjectiveQuotientEquiv_mk]
  rw [hq, quotientDescentEquiv_symm_values_mk,
    compatibleFamilyEquivKernelTrivial_apply_coe,
    finiteExternalTensor_values]

@[simp]
theorem quotientProductCharacterEquiv_degree
    (hf : Function.Surjective f)
    (χ : KernelCompatibleCharacterFamily G f) :
    (quotientProductCharacterEquiv G f hf χ).degree =
      ∏ i, (χ.1 i).degree := by
  rw [quotientProductCharacterEquiv_apply, comap_degree,
    quotientDescentEquiv_symm_degree,
    compatibleFamilyEquivKernelTrivial_apply_coe,
    finiteExternalTensor_degree]

@[simp]
theorem quotientProductCharacterEquiv_apply_symm_apply
    (hf : Function.Surjective f)
    (θ : IrreducibleCharacter H) :
    quotientProductCharacterEquiv G f hf
        ((quotientProductCharacterEquiv G f hf).symm θ) =
      θ :=
  (quotientProductCharacterEquiv G f hf).apply_symm_apply θ

@[simp]
theorem quotientProductCharacterEquiv_symm_apply_apply
    (hf : Function.Surjective f)
    (χ : KernelCompatibleCharacterFamily G f) :
    (quotientProductCharacterEquiv G f hf).symm
        (quotientProductCharacterEquiv G f hf χ) =
      χ :=
  (quotientProductCharacterEquiv G f hf).symm_apply_apply χ

@[simp]
theorem quotientProductCharacterEquiv_symm_finiteExternalTensor_values
    (hf : Function.Surjective f)
    (θ : IrreducibleCharacter H)
    (g : ∀ i, G i) :
    (finiteExternalTensor
        ((quotientProductCharacterEquiv G f hf).symm θ).1).values g =
      θ.values (f g) := by
  rw [finiteExternalTensor_values]
  symm
  calc
    θ.values (f g) =
        (quotientProductCharacterEquiv G f hf
          ((quotientProductCharacterEquiv G f hf).symm θ)).values
            (f g) := by
      rw [quotientProductCharacterEquiv_apply_symm_apply]
    _ =
        ∏ i,
          (((quotientProductCharacterEquiv G f hf).symm θ).1 i).values
            (g i) :=
      quotientProductCharacterEquiv_values_apply G f hf
        ((quotientProductCharacterEquiv G f hf).symm θ) g

@[simp]
theorem quotientProductCharacterEquiv_symm_finiteExternalTensor_degree
    (hf : Function.Surjective f)
    (θ : IrreducibleCharacter H) :
    (finiteExternalTensor
        ((quotientProductCharacterEquiv G f hf).symm θ).1).degree =
      θ.degree := by
  rw [finiteExternalTensor_degree]
  symm
  calc
    θ.degree =
        (quotientProductCharacterEquiv G f hf
          ((quotientProductCharacterEquiv G f hf).symm θ)).degree := by
      rw [quotientProductCharacterEquiv_apply_symm_apply]
    _ =
        ∏ i,
          (((quotientProductCharacterEquiv G f hf).symm θ).1 i).degree :=
      quotientProductCharacterEquiv_degree G f hf
        ((quotientProductCharacterEquiv G f hf).symm θ)

/-! ### The `p'`-degree classification -/

/-- Kernel-compatible families of `p'`-degree irreducible characters. -/
abbrev KernelCompatiblePPrimeCharacterFamily (p : ℕ) :=
  {χ : ∀ i, PPrimeIrreducibleCharacter (G i) p //
    (finiteExternalTensor (fun i ↦ (χ i).1)).TrivialOn f.ker}

/-- Forget the `p'`-degree certificates in a kernel-compatible family. -/
def compatiblePPrimeFamilyToCompatibleFamily
    (p : ℕ) (χ : KernelCompatiblePPrimeCharacterFamily G f p) :
    KernelCompatibleCharacterFamily G f :=
  ⟨fun i ↦ (χ.1 i).1, χ.2⟩

/-- The finite-product `p'`-degree equivalence restricts to compatible
families and kernel-trivial product characters. -/
def compatiblePPrimeFamilyEquivKernelTrivial
    (p : ℕ) [Fact p.Prime] :
    KernelCompatiblePPrimeCharacterFamily G f p ≃
      PPrimeTrivialOnCharacters f.ker p :=
  (finiteProductPPrimeEquiv G p).subtypeEquiv
    (fun χ => by
      rw [finiteProductPPrimeEquiv_apply,
        finiteExternalTensorPPrime_coe])

@[simp]
theorem compatiblePPrimeFamilyEquivKernelTrivial_apply_coe
    (p : ℕ) [Fact p.Prime]
    (χ : KernelCompatiblePPrimeCharacterFamily G f p) :
    (compatiblePPrimeFamilyEquivKernelTrivial G f p χ).1.1 =
      finiteExternalTensor (fun i ↦ (χ.1 i).1) := by
  change
    (finiteProductPPrimeEquiv G p χ.1).1 =
      finiteExternalTensor (fun i ↦ (χ.1 i).1)
  exact congrArg Subtype.val
    (finiteProductPPrimeEquiv_apply p χ.1)

/-- The exact `p'`-degree restriction of quotient-product
classification.  Primality is precisely what makes prime-to-`p` degree of
a finite product equivalent to prime-to-`p` degree in every factor. -/
def pPrimeQuotientProductCharacterEquiv
    (hf : Function.Surjective f)
    (p : ℕ) [Fact p.Prime] :
    KernelCompatiblePPrimeCharacterFamily G f p ≃
      PPrimeIrreducibleCharacter H p :=
  (compatiblePPrimeFamilyEquivKernelTrivial G f p).trans <|
    (pPrimeQuotientDescentEquiv f.ker p).symm.trans <|
      pPrimeComapEquiv p (surjectiveQuotientEquiv G f hf).symm

@[simp]
theorem pPrimeQuotientProductCharacterEquiv_apply_coe
    (hf : Function.Surjective f)
    (p : ℕ) [Fact p.Prime]
    (χ : KernelCompatiblePPrimeCharacterFamily G f p) :
    (pPrimeQuotientProductCharacterEquiv G f hf p χ).1 =
      quotientProductCharacterEquiv G f hf
        (compatiblePPrimeFamilyToCompatibleFamily G f p χ) :=
  rfl

@[simp]
theorem pPrimeQuotientProductCharacterEquiv_values_apply
    (hf : Function.Surjective f)
    (p : ℕ) [Fact p.Prime]
    (χ : KernelCompatiblePPrimeCharacterFamily G f p)
    (g : ∀ i, G i) :
    (pPrimeQuotientProductCharacterEquiv G f hf p χ).1.values (f g) =
      ∏ i, (χ.1 i).1.values (g i) := by
  rw [pPrimeQuotientProductCharacterEquiv_apply_coe]
  exact quotientProductCharacterEquiv_values_apply G f hf
    (compatiblePPrimeFamilyToCompatibleFamily G f p χ) g

@[simp]
theorem pPrimeQuotientProductCharacterEquiv_degree
    (hf : Function.Surjective f)
    (p : ℕ) [Fact p.Prime]
    (χ : KernelCompatiblePPrimeCharacterFamily G f p) :
    (pPrimeQuotientProductCharacterEquiv G f hf p χ).1.degree =
      ∏ i, (χ.1 i).1.degree := by
  rw [pPrimeQuotientProductCharacterEquiv_apply_coe]
  exact quotientProductCharacterEquiv_degree G f hf
    (compatiblePPrimeFamilyToCompatibleFamily G f p χ)

@[simp]
theorem pPrimeQuotientProductCharacterEquiv_apply_symm_apply
    (hf : Function.Surjective f)
    (p : ℕ) [Fact p.Prime]
    (θ : PPrimeIrreducibleCharacter H p) :
    pPrimeQuotientProductCharacterEquiv G f hf p
        ((pPrimeQuotientProductCharacterEquiv G f hf p).symm θ) =
      θ :=
  (pPrimeQuotientProductCharacterEquiv G f hf p).apply_symm_apply θ

@[simp]
theorem pPrimeQuotientProductCharacterEquiv_symm_apply_apply
    (hf : Function.Surjective f)
    (p : ℕ) [Fact p.Prime]
    (χ : KernelCompatiblePPrimeCharacterFamily G f p) :
    (pPrimeQuotientProductCharacterEquiv G f hf p).symm
        (pPrimeQuotientProductCharacterEquiv G f hf p χ) =
      χ :=
  (pPrimeQuotientProductCharacterEquiv G f hf p).symm_apply_apply χ

@[simp]
theorem
    pPrimeQuotientProductCharacterEquiv_symm_finiteExternalTensor_values
    (hf : Function.Surjective f)
    (p : ℕ) [Fact p.Prime]
    (θ : PPrimeIrreducibleCharacter H p)
    (g : ∀ i, G i) :
    (finiteExternalTensor
        (fun i ↦
          (((pPrimeQuotientProductCharacterEquiv G f hf p).symm θ).1 i).1)).values g =
      θ.1.values (f g) := by
  rw [finiteExternalTensor_values]
  symm
  calc
    θ.1.values (f g) =
        (pPrimeQuotientProductCharacterEquiv G f hf p
          ((pPrimeQuotientProductCharacterEquiv G f hf p).symm θ)).1.values
            (f g) := by
      rw [pPrimeQuotientProductCharacterEquiv_apply_symm_apply]
    _ =
        ∏ i,
          ((((pPrimeQuotientProductCharacterEquiv G f hf p).symm θ).1 i).1).values
            (g i) :=
      pPrimeQuotientProductCharacterEquiv_values_apply G f hf p
        ((pPrimeQuotientProductCharacterEquiv G f hf p).symm θ) g

@[simp]
theorem
    pPrimeQuotientProductCharacterEquiv_symm_finiteExternalTensor_degree
    (hf : Function.Surjective f)
    (p : ℕ) [Fact p.Prime]
    (θ : PPrimeIrreducibleCharacter H p) :
    (finiteExternalTensor
        (fun i ↦
          (((pPrimeQuotientProductCharacterEquiv G f hf p).symm θ).1 i).1)).degree =
      θ.1.degree := by
  rw [finiteExternalTensor_degree]
  symm
  calc
    θ.1.degree =
        (pPrimeQuotientProductCharacterEquiv G f hf p
          ((pPrimeQuotientProductCharacterEquiv G f hf p).symm θ)).1.degree := by
      rw [pPrimeQuotientProductCharacterEquiv_apply_symm_apply]
    _ =
        ∏ i,
          ((((pPrimeQuotientProductCharacterEquiv G f hf p).symm θ).1 i).1).degree :=
      pPrimeQuotientProductCharacterEquiv_degree G f hf p
        ((pPrimeQuotientProductCharacterEquiv G f hf p).symm θ)

end IrreducibleCharacter
end McKayConjecture
