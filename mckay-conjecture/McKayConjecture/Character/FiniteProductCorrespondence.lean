/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DirectProductCorrespondence
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Fintype.Option

/-!
# Irreducible characters of finite indexed products

This file iterates the binary direct-product correspondence over a finite
index type.  Reindexing and the `Option` induction step use explicit group
isomorphisms, so the resulting forward map has the expected pointwise
product formula and product-of-degrees formula.

The forward external tensor construction is meaningful without assuming
that the factor groups are finite.  Exhaustivity currently inherits the
universe-zero restriction of the project's Gallagher correspondence, so
the equivalences below are stated for `ι : Type` and `G i : Type`.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

namespace McKayConjecture
namespace IrreducibleCharacter

universe u v

/-! ### Reindexing finite products -/

/-- Splitting a product indexed by `Option ι` into its new factor and the
old product, as a group isomorphism. -/
def piOptionMulEquivProd
    {ι : Type u} (G : Option ι → Type v)
    [∀ i, Group (G i)] :
    (∀ i, G i) ≃* G none × ∀ i, G (some i) where
  __ := Equiv.piOptionEquivProd
  map_mul' _ _ := rfl

/-- Reindex a dependent product of groups along an equivalence of index
types. -/
def piCongrLeftMulEquiv
    {α β : Type u} (G : β → Type v)
    [∀ i, Group (G i)] (e : α ≃ β) :
    (∀ i, G (e i)) ≃* ∀ j, G j where
  __ := Equiv.piCongrLeft G e
  map_mul' f g := by
    apply (Equiv.piCongrLeft G e).symm.injective
    funext i
    change
      (Equiv.piCongrLeft' G e.symm).symm (f * g) (e i) =
        (Equiv.piCongrLeft' G e.symm).symm f (e i) *
          (Equiv.piCongrLeft' G e.symm).symm g (e i)
    have hfg :=
      Equiv.piCongrLeft'_symm_apply_apply
        G e.symm (f * g) i
    have hf :=
      Equiv.piCongrLeft'_symm_apply_apply
        G e.symm f i
    have hg :=
      Equiv.piCongrLeft'_symm_apply_apply
        G e.symm g i
    simpa only [Equiv.symm_symm, Pi.mul_apply] using
      hfg.trans (congrArg₂ (· * ·) hf hg).symm

/-! ### The empty product -/

/-- A group with at most one element has only its trivial irreducible
character. -/
theorem eq_trivial_of_subsingleton
    {L : Type u} [Group L] [Subsingleton L]
    (χ : IrreducibleCharacter L) :
    χ = trivial L := by
  letI : IsMulCommutative L :=
    IsMulCommutative.of_comm
      (fun _ _ ↦ Subsingleton.elim _ _)
  have hirr :
      Representation.IsIrreducible χ.realization.ρ :=
    CliffordRestriction.isIrreducible_of_simple
      χ.realization
  have hdegree : χ.degree = 1 := by
    rw [← χ.realization_finrank]
    exact hirr.finrank_eq_one_of_isMulCommutative
  apply IrreducibleCharacter.ext
  funext g
  rw [Subsingleton.elim g 1, χ.value_one,
    hdegree, Nat.cast_one, trivial_values]

/-- Irreducible characters of a subsingleton group form a unique type. -/
instance instUniqueIrreducibleCharacterOfSubsingleton
    {L : Type u} [Group L] [Subsingleton L] :
    Unique (IrreducibleCharacter L) where
  default := trivial L
  uniq χ := eq_trivial_of_subsingleton χ

/-! ### Universe-polymorphic external tensor products -/

/-- An indexed external tensor character together with its exact formulas.
This construction does not require the factor groups to be finite. -/
structure FiniteExternalTensorData
    {ι : Type u} [Fintype ι]
    (G : ι → Type v) [∀ i, Group (G i)]
    (χ : ∀ i, IrreducibleCharacter (G i)) where
  /-- The irreducible external tensor character. -/
  character : IrreducibleCharacter (∀ i, G i)
  /-- Values multiply pointwise. -/
  values :
    ∀ g : ∀ i, G i,
      character.values g =
        ∏ i, (χ i).values (g i)
  /-- Degrees multiply. -/
  degree :
    character.degree = ∏ i, (χ i).degree

/-- Iterating the binary external tensor product constructs the indexed
external tensor character in arbitrary group and index universes. -/
theorem finiteExternalTensorData_nonempty
    (ι : Type u) [Fintype ι] :
    ∀ (G : ι → Type v) [∀ i, Group (G i)]
      (χ : ∀ i, IrreducibleCharacter (G i)),
      Nonempty (FiniteExternalTensorData G χ) := by
  refine Fintype.induction_empty_option
    (P := fun ι ↦
      ∀ (G : ι → Type v) [∀ i, Group (G i)]
        (χ : ∀ i, IrreducibleCharacter (G i)),
        Nonempty (FiniteExternalTensorData G χ))
    ?_ ?_ ?_ ι
  · intro α β _ e ih G instGroup χ
    letI : Fintype α :=
      Fintype.ofEquiv β e.symm
    let GA : α → Type v := fun a ↦ G (e a)
    letI : ∀ a, Group (GA a) :=
      fun a ↦ inferInstanceAs (Group (G (e a)))
    let χA : ∀ a, IrreducibleCharacter (GA a) :=
      (Equiv.piCongrLeft
        (fun b ↦ IrreducibleCharacter (G b)) e).symm χ
    obtain ⟨d⟩ := ih GA χA
    let reindexGroups :
        (∀ a, GA a) ≃* ∀ b, G b :=
      piCongrLeftMulEquiv G e
    refine ⟨{
      character := d.character.comap reindexGroups.symm
      values := ?_
      degree := ?_ }⟩
    · intro g
      rw [comap_values, d.values]
      simpa [χA, reindexGroups,
        piCongrLeftMulEquiv, GA] using
        (e.prod_comp
          (fun b ↦ (χ b).values (g b)))
    · rw [comap_degree, d.degree]
      simpa [χA, GA] using
        (e.prod_comp (fun b ↦ (χ b).degree))
  · intro G instGroup χ
    refine ⟨{
      character := trivial (∀ i, G i)
      values := ?_
      degree := ?_ }⟩
    · intro g
      simp
    · simp
  · intro α _ ih G instGroup χ
    letI : ∀ a, Group (G (some a)) :=
      fun a ↦ inferInstance
    obtain ⟨d⟩ :=
      ih (fun a ↦ G (some a))
        (fun a ↦ χ (some a))
    let splitGroups :
        (∀ i, G i) ≃*
          G none × ∀ a, G (some a) :=
      piOptionMulEquivProd G
    refine ⟨{
      character :=
        (externalTensor (χ none) d.character).comap
          splitGroups
      values := ?_
      degree := ?_ }⟩
    · intro g
      rw [comap_values, externalTensor_values,
        d.values, Fintype.prod_option]
      rfl
    · rw [comap_degree, externalTensor_degree,
        d.degree, Fintype.prod_option]

/-- The finite external tensor product of a family of irreducible
characters. -/
def finiteExternalTensor
    {ι : Type u} [Fintype ι]
    {G : ι → Type v} [∀ i, Group (G i)]
    (χ : ∀ i, IrreducibleCharacter (G i)) :
    IrreducibleCharacter (∀ i, G i) :=
  (finiteExternalTensorData_nonempty ι G χ).some.character

@[simp]
theorem finiteExternalTensor_values
    {ι : Type u} [Fintype ι]
    {G : ι → Type v} [∀ i, Group (G i)]
    (χ : ∀ i, IrreducibleCharacter (G i))
    (g : ∀ i, G i) :
    (finiteExternalTensor χ).values g =
      ∏ i, (χ i).values (g i) :=
  (finiteExternalTensorData_nonempty ι G χ).some.values g

@[simp]
theorem finiteExternalTensor_degree
    {ι : Type u} [Fintype ι]
    {G : ι → Type v} [∀ i, Group (G i)]
    (χ : ∀ i, IrreducibleCharacter (G i)) :
    (finiteExternalTensor χ).degree =
      ∏ i, (χ i).degree :=
  (finiteExternalTensorData_nonempty ι G χ).some.degree

/-! ### Equivalence data with its exact formulas -/

/-- An indexed-product character equivalence together with the formulas
that characterize its forward external tensor product. -/
structure FiniteProductEquivData
    {ι : Type} [Fintype ι]
    (G : ι → Type) [∀ i, Finite (G i)]
    [∀ i, Group (G i)] where
  /-- The character equivalence. -/
  equiv :
    (∀ i, IrreducibleCharacter (G i)) ≃
      IrreducibleCharacter (∀ i, G i)
  /-- Values multiply pointwise. -/
  values :
    ∀ (χ : ∀ i, IrreducibleCharacter (G i))
      (g : ∀ i, G i),
      (equiv χ).values g =
        ∏ i, (χ i).values (g i)
  /-- Degrees multiply. -/
  degree :
    ∀ χ : ∀ i, IrreducibleCharacter (G i),
      (equiv χ).degree = ∏ i, (χ i).degree

/-- Iterating the binary direct-product theorem constructs indexed-product
equivalence data for every finite index type. -/
theorem finiteProductEquivData_nonempty
    (ι : Type) [Fintype ι] :
    ∀ (G : ι → Type)
      [∀ i, Finite (G i)] [∀ i, Group (G i)],
      Nonempty (FiniteProductEquivData G) := by
  refine Fintype.induction_empty_option
    (P := fun ι ↦
      ∀ (G : ι → Type)
        [∀ i, Finite (G i)] [∀ i, Group (G i)],
        Nonempty (FiniteProductEquivData G))
    ?_ ?_ ?_ ι
  · intro α β _ e ih G instFinite instGroup
    letI : Fintype α :=
      Fintype.ofEquiv β e.symm
    let GA : α → Type := fun a ↦ G (e a)
    letI : ∀ a, Finite (GA a) :=
      fun a ↦ inferInstanceAs (Finite (G (e a)))
    letI : ∀ a, Group (GA a) :=
      fun a ↦ inferInstanceAs (Group (G (e a)))
    obtain ⟨d⟩ := ih GA
    let reindexCharacters :
        (∀ b, IrreducibleCharacter (G b)) ≃
          ∀ a, IrreducibleCharacter (GA a) :=
      (Equiv.piCongrLeft
        (fun b ↦ IrreducibleCharacter (G b)) e).symm
    let reindexGroups :
        (∀ a, GA a) ≃* ∀ b, G b :=
      piCongrLeftMulEquiv G e
    let E :
        (∀ b, IrreducibleCharacter (G b)) ≃
          IrreducibleCharacter (∀ b, G b) :=
      reindexCharacters.trans
        (d.equiv.trans
          (comapEquiv reindexGroups.symm))
    refine ⟨{
      equiv := E
      values := ?_
      degree := ?_ }⟩
    · intro χ g
      change
        ((d.equiv (reindexCharacters χ)).comap
            reindexGroups.symm).values g =
          ∏ b, (χ b).values (g b)
      rw [comap_values, d.values]
      simpa [reindexCharacters, reindexGroups,
        piCongrLeftMulEquiv, GA] using
        (e.prod_comp
          (fun b ↦ (χ b).values (g b)))
    · intro χ
      change
        ((d.equiv (reindexCharacters χ)).comap
            reindexGroups.symm).degree =
          ∏ b, (χ b).degree
      rw [comap_degree, d.degree]
      simpa [reindexCharacters, GA] using
        (e.prod_comp (fun b ↦ (χ b).degree))
  · intro G instFinite instGroup
    refine ⟨{
      equiv := Equiv.ofUnique _ _
      values := ?_
      degree := ?_ }⟩
    · intro χ g
      simp [eq_trivial_of_subsingleton]
    · intro χ
      simp [eq_trivial_of_subsingleton]
  · intro α _ ih G instFinite instGroup
    letI : ∀ a, Finite (G (some a)) :=
      fun a ↦ inferInstance
    letI : ∀ a, Group (G (some a)) :=
      fun a ↦ inferInstance
    obtain ⟨d⟩ :=
      ih (fun a ↦ G (some a))
    let splitCharacters :
        (∀ i, IrreducibleCharacter (G i)) ≃
          IrreducibleCharacter (G none) ×
            (∀ a, IrreducibleCharacter (G (some a))) :=
      Equiv.piOptionEquivProd
    let splitGroups :
        (∀ i, G i) ≃*
          G none × ∀ a, G (some a) :=
      piOptionMulEquivProd G
    let E :
        (∀ i, IrreducibleCharacter (G i)) ≃
          IrreducibleCharacter (∀ i, G i) :=
      splitCharacters.trans
        ((Equiv.prodCongr (Equiv.refl _) d.equiv).trans
          (directProductEquiv.trans
            (comapEquiv splitGroups)))
    refine ⟨{
      equiv := E
      values := ?_
      degree := ?_ }⟩
    · intro χ g
      change
        ((externalTensor (χ none)
            (d.equiv (fun a ↦ χ (some a)))).comap
              splitGroups).values g =
          ∏ i, (χ i).values (g i)
      rw [comap_values, externalTensor_values,
        d.values, Fintype.prod_option]
      rfl
    · intro χ
      change
        ((externalTensor (χ none)
            (d.equiv (fun a ↦ χ (some a)))).comap
              splitGroups).degree =
          ∏ i, (χ i).degree
      rw [comap_degree, externalTensor_degree,
        d.degree, Fintype.prod_option]

/-! ### The indexed-product equivalence -/

/-- Chosen indexed-product equivalence data.  Its construction is
noncomputable because irreducible characters are represented by chosen
simple representations. -/
def finiteProductEquivData
    {ι : Type} [Fintype ι]
    (G : ι → Type) [∀ i, Finite (G i)]
    [∀ i, Group (G i)] :
    FiniteProductEquivData G :=
  (finiteProductEquivData_nonempty ι G).some

/-- Irreducible characters of a finite indexed product are equivalent to
families of irreducible characters of its factors. -/
def finiteProductEquiv
    {ι : Type} [Fintype ι]
    (G : ι → Type) [∀ i, Finite (G i)]
    [∀ i, Group (G i)] :
    (∀ i, IrreducibleCharacter (G i)) ≃
      IrreducibleCharacter (∀ i, G i) :=
  (finiteProductEquivData G).equiv

@[simp]
theorem finiteProductEquiv_values
    {ι : Type} [Fintype ι]
    {G : ι → Type} [∀ i, Finite (G i)]
    [∀ i, Group (G i)]
    (χ : ∀ i, IrreducibleCharacter (G i))
    (g : ∀ i, G i) :
    (finiteProductEquiv G χ).values g =
      ∏ i, (χ i).values (g i) :=
  (finiteProductEquivData G).values χ g

@[simp]
theorem finiteProductEquiv_degree
    {ι : Type} [Fintype ι]
    {G : ι → Type} [∀ i, Finite (G i)]
    [∀ i, Group (G i)]
    (χ : ∀ i, IrreducibleCharacter (G i)) :
    (finiteProductEquiv G χ).degree =
      ∏ i, (χ i).degree :=
  (finiteProductEquivData G).degree χ

/-- The equivalence's forward map is the universe-polymorphic finite
external tensor product. -/
@[simp]
theorem finiteProductEquiv_apply
    {ι : Type} [Fintype ι]
    {G : ι → Type} [∀ i, Finite (G i)]
    [∀ i, Group (G i)]
    (χ : ∀ i, IrreducibleCharacter (G i)) :
    finiteProductEquiv G χ = finiteExternalTensor χ := by
  apply IrreducibleCharacter.ext
  funext g
  rw [finiteProductEquiv_values,
    finiteExternalTensor_values]

/-! ### Characters of `p'`-degree -/

/-- A finite external tensor product has `p'`-degree exactly when every
factor does. -/
theorem finiteExternalTensor_isPPrimeDegree_iff
    {ι : Type u} [Fintype ι]
    {G : ι → Type v} [∀ i, Group (G i)]
    (p : ℕ) [Fact p.Prime]
    (χ : ∀ i, IrreducibleCharacter (G i)) :
    (finiteExternalTensor χ).IsPPrimeDegree p ↔
      ∀ i, (χ i).IsPPrimeDegree p := by
  rw [IsPPrimeDegree, finiteExternalTensor_degree]
  simp only [IsPPrimeDegree]
  rw [(Fact.out : p.Prime).prime.dvd_finsetProd_iff]
  simp

/-- Finite external tensor product on irreducible characters of
`p'`-degree. -/
def finiteExternalTensorPPrime
    {ι : Type u} [Fintype ι]
    {G : ι → Type v} [∀ i, Group (G i)]
    (p : ℕ) [Fact p.Prime]
    (χ : ∀ i, PPrimeIrreducibleCharacter (G i) p) :
    PPrimeIrreducibleCharacter (∀ i, G i) p :=
  ⟨finiteExternalTensor (fun i ↦ (χ i).1),
    (finiteExternalTensor_isPPrimeDegree_iff
      p (fun i ↦ (χ i).1)).2
      (fun i ↦ (χ i).2)⟩

@[simp]
theorem finiteExternalTensorPPrime_coe
    {ι : Type u} [Fintype ι]
    {G : ι → Type v} [∀ i, Group (G i)]
    (p : ℕ) [Fact p.Prime]
    (χ : ∀ i, PPrimeIrreducibleCharacter (G i) p) :
    (finiteExternalTensorPPrime p χ).1 =
      finiteExternalTensor (fun i ↦ (χ i).1) :=
  rfl

/-- Families of `p'`-degree irreducible characters of finite groups are
equivalent to `p'`-degree irreducible characters of their indexed
product. -/
def finiteProductPPrimeEquiv
    {ι : Type} [Fintype ι]
    (G : ι → Type) [∀ i, Finite (G i)]
    [∀ i, Group (G i)]
    (p : ℕ) [Fact p.Prime] :
    (∀ i, PPrimeIrreducibleCharacter (G i) p) ≃
      PPrimeIrreducibleCharacter (∀ i, G i) p :=
  Equiv.subtypePiEquivPi.symm.trans
    ((finiteProductEquiv G).subtypeEquiv
      (p := fun χ ↦
        ∀ i, (χ i).IsPPrimeDegree p)
      (q := fun φ ↦ φ.IsPPrimeDegree p)
      (fun χ ↦ by
        rw [finiteProductEquiv_apply,
          finiteExternalTensor_isPPrimeDegree_iff]))

@[simp]
theorem finiteProductPPrimeEquiv_apply
    {ι : Type} [Fintype ι]
    {G : ι → Type} [∀ i, Finite (G i)]
    [∀ i, Group (G i)]
    (p : ℕ) [Fact p.Prime]
    (χ : ∀ i, PPrimeIrreducibleCharacter (G i) p) :
    finiteProductPPrimeEquiv G p χ =
      finiteExternalTensorPPrime p χ := by
  apply Subtype.ext
  exact finiteProductEquiv_apply
    (fun i ↦ (χ i).1)

@[simp]
theorem finiteProductPPrimeEquiv_values
    {ι : Type} [Fintype ι]
    {G : ι → Type} [∀ i, Finite (G i)]
    [∀ i, Group (G i)]
    (p : ℕ) [Fact p.Prime]
    (χ : ∀ i, PPrimeIrreducibleCharacter (G i) p)
    (g : ∀ i, G i) :
    (finiteProductPPrimeEquiv G p χ).1.values g =
      ∏ i, (χ i).1.values (g i) := by
  rw [finiteProductPPrimeEquiv_apply,
    finiteExternalTensorPPrime_coe,
    finiteExternalTensor_values]

@[simp]
theorem finiteProductPPrimeEquiv_degree
    {ι : Type} [Fintype ι]
    {G : ι → Type} [∀ i, Finite (G i)]
    [∀ i, Group (G i)]
    (p : ℕ) [Fact p.Prime]
    (χ : ∀ i, PPrimeIrreducibleCharacter (G i) p) :
    (finiteProductPPrimeEquiv G p χ).1.degree =
      ∏ i, (χ i).1.degree := by
  rw [finiteProductPPrimeEquiv_apply,
    finiteExternalTensorPPrime_coe,
    finiteExternalTensor_degree]

end IrreducibleCharacter
end McKayConjecture
