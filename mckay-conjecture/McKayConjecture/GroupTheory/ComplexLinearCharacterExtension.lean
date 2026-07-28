/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Extension of complex linear characters

The multiplicative group `ℂˣ` is divisible, hence its additive avatar is an
injective object in the category of abelian groups.  Consequently, a
character of a subgroup of an abelian group extends to the whole group.

We also record the useful relative form.  If `f : D → Q` maps a group into an
abelian quotient and `χ : D → ℂˣ` is trivial on `ker f`, then `χ` extends
along `f`.  Pulling the extension back along a quotient map produces an
ambient linear character which is trivial on the quotient kernel.
-/

noncomputable section

open CategoryTheory

universe u

namespace McKayConjecture
namespace GroupTheory

/-- The additive group underlying `ℂˣ` is divisible by positive natural
numbers. -/
@[instance_reducible]
private noncomputable def complexUnitsDivisibleByNat :
    DivisibleBy (Additive ℂˣ) ℕ :=
  divisibleByOfSMulRightSurj _ _ fun {n} hn x ↦ by
    obtain ⟨z, hz⟩ :=
      IsAlgClosed.exists_pow_nat_eq
        (x.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      intro h
      have hx0 : (x.toMul : ℂ) ≠ 0 := Units.ne_zero _
      apply hx0
      rw [← hz, h, zero_pow hn]
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    apply Units.ext
    exact hz

/-- The additive group underlying `ℂˣ` is divisible by the integers. -/
@[instance_reducible]
private noncomputable def complexUnitsDivisibleByInt :
    DivisibleBy (Additive ℂˣ) ℤ := by
  letI : DivisibleBy (Additive ℂˣ) ℕ :=
    complexUnitsDivisibleByNat
  exact AddGroup.divisibleByIntOfDivisibleByNat _

/-- A homomorphism from a subgroup of an abelian group to a divisible
abelian group extends to the ambient group. -/
theorem exists_monoidHom_extension_of_subgroup
    {G C : Type u} [CommGroup G] [CommGroup C]
    [DivisibleBy (Additive C) ℤ]
    (H : Subgroup G) (χ : H →* C) :
    ∃ χ' : G →* C, ∀ x : H, χ' x = χ x := by
  let inclusion : Additive H →+ Additive G :=
    H.subtype.toAdditive
  let f :
      AddCommGrpCat.of (Additive H) ⟶
        AddCommGrpCat.of (Additive G) :=
    AddCommGrpCat.ofHom inclusion
  let g :
      AddCommGrpCat.of (Additive H) ⟶
        AddCommGrpCat.of (Additive C) :=
    AddCommGrpCat.ofHom χ.toAdditive
  letI : Mono f :=
    (AddCommGrpCat.mono_iff_injective f).2 (by
      intro x y hxy
      exact Subtype.val_injective hxy)
  let extension :
      AddCommGrpCat.of (Additive G) ⟶
        AddCommGrpCat.of (Additive C) :=
    Injective.factorThru g f
  refine
    ⟨MonoidHom.toAdditive.symm extension.hom, ?_⟩
  intro x
  have hcomp : f ≫ extension = g :=
    Injective.comp_factorThru g f
  have hx :=
    congrArg (fun k ↦ k (Additive.ofMul x)) hcomp
  exact hx

/-- If `χ` kills the kernel of a map into an abelian group, then `χ`
extends along that map. -/
theorem exists_monoidHom_extension_along_of_ker_le
    {D G C : Type u}
    [Group D] [CommGroup G] [CommGroup C]
    [DivisibleBy (Additive C) ℤ]
    (f : D →* G) (χ : D →* C)
    (hker : f.ker ≤ χ.ker) :
    ∃ χ' : G →* C, χ'.comp f = χ := by
  let rangeCharacter : f.range →* C :=
    f.rangeRestrict.liftOfSurjective
      f.rangeRestrict_surjective
      ⟨χ, by
        rwa [MonoidHom.ker_rangeRestrict]⟩
  obtain ⟨χ', hχ'⟩ :=
    exists_monoidHom_extension_of_subgroup
      f.range rangeCharacter
  refine ⟨χ', ?_⟩
  apply MonoidHom.ext
  intro x
  change χ' (f x) = χ x
  rw [← f.coe_rangeRestrict x, hχ']
  simp [rangeCharacter]

/-- Complex linear characters satisfy the preceding extension theorem
without an extra divisibility hypothesis. -/
theorem exists_complexLinearCharacter_extension_along_of_ker_le
    {D G : Type}
    [Group D] [CommGroup G]
    (f : D →* G) (χ : D →* ℂˣ)
    (hker : f.ker ≤ χ.ker) :
    ∃ χ' : G →* ℂˣ, χ'.comp f = χ := by
  letI : DivisibleBy (Additive ℂˣ) ℤ :=
    complexUnitsDivisibleByInt
  exact
    exists_monoidHom_extension_along_of_ker_le
      f χ hker

/-- Pulling an extension back from an abelian quotient gives an ambient
character which is trivial on the quotient kernel. -/
theorem exists_complexLinearCharacter_extension_trivial_on_ker
    {D G Q : Type}
    [Group D] [Group G] [CommGroup Q]
    (ι : D →* G) (q : G →* Q)
    (χ : D →* ℂˣ)
    (hker : (q.comp ι).ker ≤ χ.ker) :
    ∃ χ' : G →* ℂˣ,
      (∀ x : q.ker, χ' (x : G) = 1) ∧
      χ'.comp ι = χ := by
  obtain ⟨χQ, hχQ⟩ :=
    exists_complexLinearCharacter_extension_along_of_ker_le
      (q.comp ι) χ hker
  refine ⟨χQ.comp q, ?_, ?_⟩
  · intro x
    change χQ (q (x : G)) = 1
    rw [MonoidHom.mem_ker.mp x.property, map_one]
  · rw [MonoidHom.comp_assoc, hχQ]

/-- A complex linear character of a subgroup extends to the ambient
group when it is trivial on the subgroup's intersection with the ambient
commutator subgroup. -/
theorem exists_complexLinearCharacter_extension_of_commutator
    {G : Type} [Group G]
    (H : Subgroup G) (χ : H →* ℂˣ)
    (hcomm :
      ∀ x : H, (x : G) ∈ commutator G → χ x = 1) :
    ∃ χ' : G →* ℂˣ,
      χ'.comp H.subtype = χ := by
  let f : H →* Abelianization G :=
    Abelianization.of.comp H.subtype
  have hker : f.ker ≤ χ.ker := by
    intro x hx
    have hfx : Abelianization.of (x : G) = 1 :=
      MonoidHom.mem_ker.mp hx
    have hxcomm : (x : G) ∈ commutator G := by
      rw [← Abelianization.ker_of G]
      exact MonoidHom.mem_ker.mpr hfx
    exact MonoidHom.mem_ker.mpr (hcomm x hxcomm)
  obtain ⟨χab, hχab⟩ :=
    exists_complexLinearCharacter_extension_along_of_ker_le
      f χ hker
  refine ⟨χab.comp Abelianization.of, ?_⟩
  rw [MonoidHom.comp_assoc]
  exact hχab

/-- The commutator-intersection criterion exactly characterizes
extendibility of a complex linear character from a subgroup. -/
theorem exists_complexLinearCharacter_extension_iff_commutator
    {G : Type} [Group G]
    (H : Subgroup G) (χ : H →* ℂˣ) :
    (∃ χ' : G →* ℂˣ,
        χ'.comp H.subtype = χ) ↔
      ∀ x : H, (x : G) ∈ commutator G → χ x = 1 := by
  constructor
  · rintro ⟨χ', hχ'⟩ x hx
    have hxker : (x : G) ∈ χ'.ker :=
      Abelianization.commutator_subset_ker χ' hx
    have hvalue : χ' (x : G) = 1 :=
      MonoidHom.mem_ker.mp hxker
    have hagree :=
      congrArg (fun k : H →* ℂˣ ↦ k x) hχ'
    exact hagree ▸ hvalue
  · exact
      exists_complexLinearCharacter_extension_of_commutator
        H χ

end GroupTheory
end McKayConjecture
