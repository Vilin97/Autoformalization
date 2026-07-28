/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionPairing
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# The central group-algebra element of a class function

A complex class function `f` on a finite group determines the central
group-algebra element

`∑ g, f(g⁻¹) g`.

Its trace on a representation is the unnormalized Fourier pairing of `f`
with the character of that representation.  These elementary identities
are the group-algebra input for completeness of irreducible characters.
-/

noncomputable section

open scoped BigOperators MonoidAlgebra
open CategoryTheory

namespace McKayConjecture
namespace ClassFunction

universe u

variable {G : Type u} [Group G] [Finite G]

/-- A class function has the cyclic invariance `f (a b) = f (b a)`. -/
theorem mul_comm_apply (f : ClassFunction G) (a b : G) :
    f (a * b) = f (b * a) := by
  have h := ClassFunction.conj_apply f (b * a) a
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using h

/-- The central group-algebra element associated to `f`.  The inverse in
the coefficient makes its representation trace equal to the pairing
`∑ g, f(g) χ(g⁻¹)`. -/
def groupAlgebraElement (f : ClassFunction G) : MonoidAlgebra ℂ G := by
  letI : Fintype G := Fintype.ofFinite G
  exact ∑ g : G, MonoidAlgebra.single g (f g⁻¹)

@[simp]
theorem groupAlgebraElement_coeff
    (f : ClassFunction G) (x : G) :
    (groupAlgebraElement f).coeff x = f x⁻¹ := by
  letI : Fintype G := Fintype.ofFinite G
  classical
  rw [groupAlgebraElement]
  simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single]
  change (∑ g : G, Finsupp.single g (f g⁻¹)) x = f x⁻¹
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single x]
  · exact Finsupp.single_eq_same
  · intro g _hg hne
    exact Finsupp.single_eq_of_ne hne.symm
  · simp

/-- The associated group-algebra element commutes with every group basis
element. -/
theorem groupAlgebraElement_mul_single
    (f : ClassFunction G) (h : G) :
    groupAlgebraElement f * MonoidAlgebra.single h 1 =
      MonoidAlgebra.single h 1 * groupAlgebraElement f := by
  letI : Fintype G := Fintype.ofFinite G
  classical
  ext x
  simp only [MonoidAlgebra.coeff_mul_single_apply,
    MonoidAlgebra.coeff_single_mul_apply, one_mul, mul_one,
    groupAlgebraElement_coeff]
  simpa only [mul_inv_rev, inv_inv] using
    mul_comm_apply f h x⁻¹

/-- The associated group-algebra element is central. -/
theorem groupAlgebraElement_commute
    (f : ClassFunction G) (z : MonoidAlgebra ℂ G) :
    Commute (groupAlgebraElement f) z := by
  induction z using MonoidAlgebra.induction_on with
  | of h =>
      show
        groupAlgebraElement f * MonoidAlgebra.single h 1 =
          MonoidAlgebra.single h 1 * groupAlgebraElement f
      exact groupAlgebraElement_mul_single f h
  | add x y hx hy =>
      exact hx.add_right hy
  | smul c x hx =>
      exact hx.smul_right c

/-- The associated element belongs to the center of the group algebra. -/
theorem groupAlgebraElement_mem_center
    (f : ClassFunction G) :
    groupAlgebraElement f ∈
      Submonoid.center (MonoidAlgebra ℂ G) := by
  rw [Submonoid.mem_center_iff]
  intro z
  exact (groupAlgebraElement_commute f z).eq.symm

/-- The action of the central group-algebra element on a finite-dimensional
representation. -/
def groupAlgebraAction
    (f : ClassFunction G) (V : FDRep ℂ G) :
    V →ₗ[ℂ] V :=
  Representation.asAlgebraHom V.ρ
    (groupAlgebraElement f)

/-- The central group-algebra action, bundled as an endomorphism of the
representation. -/
def groupAlgebraEndomorphism
    (f : ClassFunction G) (V : FDRep ℂ G) :
    V ⟶ V := by
  let F : Representation.IntertwiningMap V.ρ V.ρ :=
    Representation.IntertwiningMap.centralAlgebraMul V.ρ
      (groupAlgebraElement_mem_center f)
  exact
    ⟨InducedCategory.homMk
        (ModuleCat.ofHom F.toLinearMap),
      fun g ↦ by
        ext x
        exact LinearMap.congr_fun (F.2 g) x⟩

/-- The underlying linear map of a morphism of finite-dimensional
representations. -/
def underlyingLinearMap {V W : FDRep ℂ G} (a : V ⟶ W) :
    V →ₗ[ℂ] W :=
  ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).map a.hom).hom

@[simp]
theorem underlyingLinearMap_apply
    {V W : FDRep ℂ G} (a : V ⟶ W) (v : V) :
    underlyingLinearMap a v = a v :=
  rfl

@[simp]
theorem underlyingLinearMap_id (V : FDRep ℂ G) :
    underlyingLinearMap (𝟙 V) = LinearMap.id := by
  ext v
  rfl

@[simp]
theorem underlyingLinearMap_smul
    (c : ℂ) {V W : FDRep ℂ G} (a : V ⟶ W) :
    underlyingLinearMap (c • a) =
      c • underlyingLinearMap a := by
  ext v
  rfl

@[simp]
theorem underlyingLinearMap_groupAlgebraEndomorphism
    (f : ClassFunction G) (V : FDRep ℂ G) :
    underlyingLinearMap (groupAlgebraEndomorphism f V) =
      groupAlgebraAction f V :=
  rfl

@[simp]
theorem groupAlgebraEndomorphism_apply
    (f : ClassFunction G) (V : FDRep ℂ G) (v : V) :
    groupAlgebraEndomorphism f V v =
      groupAlgebraAction f V v :=
  rfl

/-- The character of an arbitrary finite-dimensional representation,
bundled as a class function. -/
def ofFDRep (V : FDRep ℂ G) : ClassFunction G :=
  ⟨V.character, fun g h ↦ FDRep.char_conj V g h⟩

@[simp]
theorem ofFDRep_apply (V : FDRep ℂ G) (g : G) :
    ofFDRep V g = V.character g :=
  rfl

/-- The trace of the associated group-algebra action is the unnormalized
Fourier pairing with the representation character. -/
theorem trace_groupAlgebraAction
    (f : ClassFunction G) (V : FDRep ℂ G) :
    LinearMap.trace ℂ V (groupAlgebraAction f V) =
      (Nat.card G : ℂ) *
        normalizedPairing f (ofFDRep V) := by
  letI : Fintype G := Fintype.ofFinite G
  classical
  have hcard : (Nat.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [groupAlgebraAction, groupAlgebraElement]
  simp only [map_sum, Representation.asAlgebraHom_single,
    map_smul]
  change
    (∑ g : G,
        f g⁻¹ * LinearMap.trace ℂ V (V.ρ g)) =
      (Nat.card G : ℂ) *
        ((Nat.card G : ℂ)⁻¹ *
          ∑ g : G,
            f g * LinearMap.trace ℂ V (V.ρ g⁻¹))
  rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  simpa [Equiv.inv] using
    (Function.Bijective.sum_comp
      (Equiv.inv G).bijective
      (fun g : G ↦
        f g * LinearMap.trace ℂ V (V.ρ g⁻¹)))

/-- The coefficient map recovers the original class function, so the
group-algebra construction is injective. -/
theorem groupAlgebraElement_eq_zero_iff
    (f : ClassFunction G) :
    groupAlgebraElement f = 0 ↔ f = 0 := by
  constructor
  · intro h
    apply ClassFunction.ext
    intro x
    have hx := congrArg (fun z : MonoidAlgebra ℂ G ↦ z.coeff x⁻¹) h
    simpa using hx
  · rintro rfl
    letI : Fintype G := Fintype.ofFinite G
    simp [groupAlgebraElement]

end ClassFunction
end McKayConjecture
