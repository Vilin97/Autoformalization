/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NumericalReduction
import McKayConjecture.Proof.FiniteProduct

/-!
# Local correspondences for finite indexed products

A family of local McKay correspondences combines coordinatewise into a
local correspondence for the finite indexed product.  Its intermediate
subgroup is the product of the factor intermediate subgroups, and its
character correspondence is obtained by applying the finite external
tensor classification before and after the factor correspondences.
-/

noncomputable section

namespace McKayConjecture.InductiveMcKay

variable {ι : Type} [Fintype ι]
variable {G : ι → Type} [∀ i, Finite (G i)]
variable [∀ i, Group (G i)]
variable {p : ℕ} [Fact p.Prime]

namespace LocalCorrespondence

/-- The coordinatewise intermediate subgroup attached to a family of
local correspondences. -/
def productIntermediate
    {P : ∀ i, Sylow p (G i)}
    (d : ∀ i, LocalCorrespondence (P i)) :
    Subgroup (∀ i, G i) :=
  Subgroup.pi Set.univ fun i ↦ (d i).intermediate

omit [Fintype ι] [∀ i, Finite (G i)]
    [Fact p.Prime] in
@[simp]
theorem mem_productIntermediate
    {P : ∀ i, Sylow p (G i)}
    (d : ∀ i, LocalCorrespondence (P i))
    (x : ∀ i, G i) :
    x ∈ productIntermediate d ↔
      ∀ i, x i ∈ (d i).intermediate := by
  simp [productIntermediate, Subgroup.mem_pi]

/-- A finite indexed product of local McKay correspondences. -/
def finiteProduct
    (P : ∀ i, Sylow p (G i))
    (d : ∀ i, LocalCorrespondence (P i)) :
    LocalCorrespondence (GroupTheory.Sylow.pi P) where
  intermediate :=
    productIntermediate d
  normalizer_le := by
    change
      Subgroup.normalizer
          (Subgroup.pi Set.univ
            (fun i ↦ (P i : Subgroup (G i))) :
            Set (∀ i, G i)) ≤
        productIntermediate d
    rw [GroupTheory.Subgroup.normalizer_pi]
    intro x hx
    rw [Subgroup.mem_pi] at hx
    rw [mem_productIntermediate]
    intro i
    exact (d i).normalizer_le
      (hx i (Set.mem_univ i))
  proper_of_normalizer_ne_top := by
    classical
    intro hnormalizer
    have hfactor :
        ∃ i,
          Subgroup.normalizer
              (P i : Set (G i)) ≠
            ⊤ := by
      by_contra h
      have hall :
          ∀ i,
            Subgroup.normalizer
                (P i : Set (G i)) =
              ⊤ := by
        intro i
        by_contra hi
        exact h ⟨i, hi⟩
      apply hnormalizer
      change
        Subgroup.normalizer
            (Subgroup.pi Set.univ
              (fun i ↦ (P i : Subgroup (G i))) :
              Set (∀ i, G i)) =
          ⊤
      rw [GroupTheory.Subgroup.normalizer_pi]
      simpa [hall] using
        (Subgroup.pi_top
          (f := G) Set.univ)
    obtain ⟨i, hi⟩ := hfactor
    have hproper :
        (d i).intermediate < ⊤ :=
      (d i).proper_of_normalizer_ne_top hi
    rw [lt_top_iff_ne_top]
    intro htop
    apply hproper.ne
    rw [Subgroup.eq_top_iff']
    intro x
    have hx :
        Pi.mulSingle i x ∈
          productIntermediate d := by
      rw [htop]
      trivial
    rw [mem_productIntermediate] at hx
    simpa using hx i
  correspondence :=
    (IrreducibleCharacter.finiteProductPPrimeEquiv G p).symm
      |>.trans
        (Equiv.piCongrRight
          (fun i ↦ (d i).correspondence))
      |>.trans
        (IrreducibleCharacter.finiteProductPPrimeEquiv
          (fun i ↦ (d i).intermediate) p)
      |>.trans
        (IrreducibleCharacter.pPrimeComapEquiv p
          (GroupTheory.Subgroup.piMulEquiv
            (fun i ↦ (d i).intermediate)))

@[simp]
theorem finiteProduct_intermediate
    (P : ∀ i, Sylow p (G i))
    (d : ∀ i, LocalCorrespondence (P i)) :
    (finiteProduct P d).intermediate =
      productIntermediate d :=
  rfl

@[simp]
theorem finiteProduct_correspondence_apply
    (P : ∀ i, Sylow p (G i))
    (d : ∀ i, LocalCorrespondence (P i))
    (χ :
      PPrimeIrreducibleCharacter (∀ i, G i) p) :
    (finiteProduct P d).correspondence χ =
      IrreducibleCharacter.pPrimeComapEquiv p
        (GroupTheory.Subgroup.piMulEquiv
          (fun i ↦ (d i).intermediate))
        (IrreducibleCharacter.finiteProductPPrimeEquiv
          (fun i ↦ (d i).intermediate) p
          (fun i ↦
            (d i).correspondence
              ((IrreducibleCharacter.finiteProductPPrimeEquiv
                G p).symm χ i))) :=
  rfl

end LocalCorrespondence

end McKayConjecture.InductiveMcKay
