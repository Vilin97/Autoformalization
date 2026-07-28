/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalar
import McKayConjecture.Character.FiniteProductCorrespondence

/-!
# Compatibility across matched central kernels

Suppose two finite indexed products have central subgroups identified by a
coordinatewise embedding.  If each pair of coordinate characters has the
same normalized central character, expressed without division by the
cross-multiplied identity

`χ(e y) ψ(1) = ψ(y) χ(1)`,

then their finite external tensor characters are simultaneously trivial on
the two matched central subgroups.

This is the abstract character calculation used when a product of component
correspondences is descended through the central multiplication kernel of a
layer.
-/

noncomputable section

open scoped BigOperators

universe u v w

namespace McKayConjecture
namespace IrreducibleCharacter

variable {ι : Type u} [Fintype ι]
variable {G : ι → Type v} {H : ι → Type w}
variable [∀ i, Group (G i)] [∀ i, Group (H i)]
variable [∀ i, Finite (G i)] [∀ i, Finite (H i)]

omit [Fintype ι] [∀ i, Finite (G i)] in
/-- A central element of a dependent product has central coordinates. -/
theorem mem_center_coordinate
    (x : ∀ i, G i)
    (hx : x ∈ Subgroup.center (∀ i, G i))
    (i : ι) :
    x i ∈ Subgroup.center (G i) := by
  rw [Subgroup.center_pi] at hx
  exact hx i (Set.mem_univ i)

omit [∀ i, Finite (G i)] in
/-- A product of positive character degrees is nonzero after casting to
`ℂ`. -/
theorem prod_degree_cast_ne_zero
    (χ : ∀ i, IrreducibleCharacter (G i)) :
    (∏ i, ((χ i).degree : ℂ)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i _
  exact Nat.cast_ne_zero.mpr (χ i).degree_ne_zero

/-- Finite external tensor characters are simultaneously trivial on
coordinatewise matched central subgroups when their coordinate characters
have the same normalized central scalars.

The equivalence `eK` identifies the right kernel with the left kernel;
`hcomm` records that its underlying map is coordinatewise `e`. -/
theorem finiteExternalTensor_trivialOn_iff_of_matchedCentralCross
    (e : ∀ i, H i →* G i)
    (KG : Subgroup (∀ i, G i))
    (KH : Subgroup (∀ i, H i))
    (hKG : KG ≤ Subgroup.center (∀ i, G i))
    (hKH : KH ≤ Subgroup.center (∀ i, H i))
    (eK : KH ≃* KG)
    (hcomm : ∀ (z : KH) (i : ι),
      ((eK z : KG).1 i) = e i (z.1 i))
    (χ : ∀ i, IrreducibleCharacter (G i))
    (ψ : ∀ i, IrreducibleCharacter (H i))
    (hcross : ∀ (i : ι) (y : H i),
      e i y ∈ Subgroup.center (G i) →
        (χ i).values (e i y) *
            ((ψ i).degree : ℂ) =
          (ψ i).values y *
            ((χ i).degree : ℂ)) :
    (finiteExternalTensor χ).TrivialOn KG ↔
      (finiteExternalTensor ψ).TrivialOn KH := by
  rw [trivialOn_iff_values_eq_degree
      (finiteExternalTensor χ) KG hKG,
    trivialOn_iff_values_eq_degree
      (finiteExternalTensor ψ) KH hKH]
  constructor
  · intro hχ z
    have hχz := hχ (eK z)
    rw [finiteExternalTensor_values,
      finiteExternalTensor_degree] at hχz
    have hcrossProd :
        (∏ i, (χ i).values (e i (z.1 i))) *
            (∏ i, ((ψ i).degree : ℂ)) =
          (∏ i, (ψ i).values (z.1 i)) *
            (∏ i, ((χ i).degree : ℂ)) := by
      rw [← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      apply hcross i (z.1 i)
      rw [← hcomm z i]
      exact mem_center_coordinate
        (G := G) (eK z).1
        (hKG (eK z).2) i
    have hχz' :
        (∏ i, (χ i).values (e i (z.1 i))) =
          ∏ i, ((χ i).degree : ℂ) := by
      rw [Nat.cast_prod] at hχz
      simpa only [hcomm z] using hχz
    have hcancel :
        (∏ i, ((ψ i).degree : ℂ)) *
            (∏ i, ((χ i).degree : ℂ)) =
          (∏ i, (ψ i).values (z.1 i)) *
            (∏ i, ((χ i).degree : ℂ)) := by
      calc
        (∏ i, ((ψ i).degree : ℂ)) *
              (∏ i, ((χ i).degree : ℂ)) =
            (∏ i, ((χ i).degree : ℂ)) *
              (∏ i, ((ψ i).degree : ℂ)) :=
          mul_comm _ _
        _ =
            (∏ i, (χ i).values (e i (z.1 i))) *
              (∏ i, ((ψ i).degree : ℂ)) := by
          rw [hχz']
        _ =
            (∏ i, (ψ i).values (z.1 i)) *
              (∏ i, ((χ i).degree : ℂ)) :=
          hcrossProd
    rw [finiteExternalTensor_values,
      finiteExternalTensor_degree, Nat.cast_prod]
    exact
      (mul_right_cancel₀
        (prod_degree_cast_ne_zero χ) hcancel).symm
  · intro hψ z
    let y : KH := eK.symm z
    have hψy := hψ y
    rw [finiteExternalTensor_values,
      finiteExternalTensor_degree] at hψy
    have hcrossProd :
        (∏ i, (χ i).values (z.1 i)) *
            (∏ i, ((ψ i).degree : ℂ)) =
          (∏ i, (ψ i).values (y.1 i)) *
            (∏ i, ((χ i).degree : ℂ)) := by
      rw [← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      have hcoord :
          z.1 i = e i (y.1 i) := by
        simpa [y] using hcomm y i
      rw [hcoord]
      apply hcross i (y.1 i)
      rw [← hcoord]
      exact mem_center_coordinate
        (G := G) z.1 (hKG z.2) i
    have hψy' :
      (∏ i, (ψ i).values (y.1 i)) =
          ∏ i, ((ψ i).degree : ℂ) :=
      by
        rw [Nat.cast_prod] at hψy
        exact hψy
    have hcancel :
        (∏ i, (χ i).values (z.1 i)) *
            (∏ i, ((ψ i).degree : ℂ)) =
          (∏ i, ((χ i).degree : ℂ)) *
            (∏ i, ((ψ i).degree : ℂ)) := by
      calc
        (∏ i, (χ i).values (z.1 i)) *
              (∏ i, ((ψ i).degree : ℂ)) =
            (∏ i, (ψ i).values (y.1 i)) *
              (∏ i, ((χ i).degree : ℂ)) :=
          hcrossProd
        _ =
            (∏ i, ((ψ i).degree : ℂ)) *
              (∏ i, ((χ i).degree : ℂ)) := by
          rw [hψy']
        _ =
            (∏ i, ((χ i).degree : ℂ)) *
              (∏ i, ((ψ i).degree : ℂ)) :=
          mul_comm _ _
    rw [finiteExternalTensor_values,
      finiteExternalTensor_degree, Nat.cast_prod]
    exact
      mul_right_cancel₀
        (prod_degree_cast_ne_zero ψ)
        hcancel

end IrreducibleCharacter
end McKayConjecture
