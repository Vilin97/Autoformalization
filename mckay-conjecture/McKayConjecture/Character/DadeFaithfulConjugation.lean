/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InteriorAlgebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Ring.Action.End

/-!
# Faithfulness of conjugation for Dade interior algebras

Let a `p`-group act on a central algebra over a field of
characteristic `p`, and suppose that the action is implemented by a
faithful homomorphism into the unit group.  Then the induced action on
the algebra is faithful.

Indeed, an implementing unit whose conjugation action is trivial lies
in the center, hence is a scalar.  Its order divides a power of `p`,
whereas a field of characteristic `p` has no nontrivial `p`-power roots
of unity.  Thus the scalar, the implementing unit, and finally the
original group element are all trivial.
-/

noncomputable section

namespace Representation

section ScalarTorsion

variable {p : ℕ} [Fact p.Prime]
variable {k : Type} [Field k] [CharP k p]

/-- A `p`-power root of unity in a field of characteristic `p` is one.

This does not require the field to be finite. -/
theorem eq_one_of_pow_char_pow_eq_one
    {x : k} {n : ℕ}
    (hx : x ^ (p ^ n) = 1) :
    x = 1 := by
  have hsub : (x - 1) ^ (p ^ n) = 0 := by
    rw [sub_pow_char_pow, hx, one_pow, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsub)

/-- The unit-group version of `eq_one_of_pow_char_pow_eq_one`. -/
theorem unit_eq_one_of_pow_char_pow_eq_one
    {x : kˣ} {n : ℕ}
    (hx : x ^ (p ^ n) = 1) :
    x = 1 := by
  apply Units.ext
  apply eq_one_of_pow_char_pow_eq_one (p := p)
  exact congrArg Units.val hx

end ScalarTorsion

namespace InteriorAction

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [CharP k p]
variable [Group P]
variable [Ring A] [Nontrivial A] [Algebra k A]
variable [MulSemiringAction P A]

/-- If one element of a `p`-group acts trivially by an injective
interior action on a central algebra in characteristic `p`, then that
element is trivial. -/
theorem eq_one_of_smul_eq_self
    (I : InteriorAction (P := P) (A := A))
    (hcentral : Algebra.IsCentral k A)
    (hP : IsPGroup p P)
    (hunit : Function.Injective I.unit)
    {g : P}
    (hg : ∀ a : A, g • a = a) :
    g = 1 := by
  letI : Algebra.IsCentral k A := hcentral
  have hcomm :
      ∀ a : A,
        (I.unit g : A) * a =
          a * (I.unit g : A) := by
    intro a
    have haction : (I.unit g : A) * a *
          (↑((I.unit g)⁻¹) : A) = a := by
      rw [← I.smul_eq]
      exact hg a
    have hright :=
      congrArg
        (fun x : A => x * (I.unit g : A))
        haction
    simpa only [mul_assoc, Units.inv_mul, mul_one] using hright
  have hcenter :
      (I.unit g : A) ∈ Subalgebra.center k A :=
    (Subalgebra.mem_center_iff (R := k)).2
      (fun a => (hcomm a).symm)
  have hbot :
      (I.unit g : A) ∈ (⊥ : Subalgebra k A) :=
    Algebra.IsCentral.out hcenter
  rw [Algebra.mem_bot] at hbot
  obtain ⟨c, hc_map⟩ := hbot
  have hc : (I.unit g : A) = algebraMap k A c :=
    hc_map.symm
  have hc_ne : c ≠ 0 := by
    intro hc_zero
    apply Units.ne_zero (I.unit g)
    rw [hc, hc_zero, map_zero]
  let z : kˣ := Units.mk0 c hc_ne
  let scalarUnit : kˣ →* Aˣ :=
    Units.map (algebraMap k A).toMonoidHom
  have hunit_scalar :
      I.unit g = scalarUnit z := by
    apply Units.ext
    exact hc
  obtain ⟨n, hgn⟩ := hP.exists_pow_pow_eq_one g
  have hscalar_pow :
      (scalarUnit z) ^ (p ^ n) = 1 := by
    rw [← hunit_scalar, ← map_pow, hgn, map_one]
  have hc_pow :
      (c : k) ^ (p ^ n) = 1 := by
    apply (algebraMap k A).injective
    have hcoe :=
      congrArg (fun u : Aˣ => (u : A)) hscalar_pow
    simpa [scalarUnit, z] using hcoe
  have hz : z = 1 := by
    apply Units.ext
    exact eq_one_of_pow_char_pow_eq_one (p := p) hc_pow
  apply hunit
  calc
    I.unit g = scalarUnit z := hunit_scalar
    _ = 1 := by rw [hz, map_one]
    _ = I.unit 1 := (map_one I.unit).symm

/-- The ring-automorphism action associated to a faithful interior
action of a `p`-group on a central algebra in characteristic `p` is
faithful. -/
theorem toRingAut_injective
    (I : InteriorAction (P := P) (A := A))
    (hcentral : Algebra.IsCentral k A)
    (hP : IsPGroup p P)
    (hunit : Function.Injective I.unit) :
    Function.Injective
      (MulSemiringAction.toRingAut P A) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply I.eq_one_of_smul_eq_self hcentral hP hunit
  intro a
  exact DFunLike.congr_fun hg a

variable [SMulCommClass P k A]

/-- The linear action associated to a faithful interior action of a
`p`-group on a central algebra in characteristic `p` is faithful. -/
theorem toModuleAut_injective
    (I : InteriorAction (P := P) (A := A))
    (hcentral : Algebra.IsCentral k A)
    (hP : IsPGroup p P)
    (hunit : Function.Injective I.unit) :
    Function.Injective
      (DistribMulAction.toModuleAut k A : P →* (A ≃ₗ[k] A)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply I.eq_one_of_smul_eq_self hcentral hP hunit
  intro a
  have ha := DFunLike.congr_fun hg a
  exact ha

end InteriorAction

namespace DadeAlgebra

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [CharP k p]
variable [Group P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A]

/-- A Dade interior algebra with injective implementing homomorphism
has a faithful associated action by ring automorphisms. -/
theorem toRingAut_injective
    (S : DadeAlgebra p k P A)
    (I : InteriorAction (P := P) (A := A))
    (hunit : Function.Injective I.unit) :
    Function.Injective
      (MulSemiringAction.toRingAut P A) := by
  letI : IsSimpleRing A := S.isSimple
  exact I.toRingAut_injective S.isCentral S.isPGroup hunit

variable [SMulCommClass P k A]

/-- A Dade interior algebra with injective implementing homomorphism
has a faithful associated linear action on its underlying algebra. -/
theorem toModuleAut_injective
    (S : DadeAlgebra p k P A)
    (I : InteriorAction (P := P) (A := A))
    (hunit : Function.Injective I.unit) :
    Function.Injective
      (DistribMulAction.toModuleAut k A : P →* (A ≃ₗ[k] A)) := by
  letI : IsSimpleRing A := S.isSimple
  exact I.toModuleAut_injective S.isCentral S.isPGroup hunit

end DadeAlgebra

end Representation
