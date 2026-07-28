/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.LinearAlgebra.Matrix.Trace
import McKayConjecture.Character.InductionCharacter

/-!
# Mackey decomposition

This file proves the Mackey restriction--induction decomposition for finite
groups.  The representation-level proof first works in the coinduced-function
model and then transports the result to mathlib's coinvariant model of
induction.
-/

noncomputable section

open CategoryTheory

universe u v w

namespace McKayConjecture

namespace Mackey

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- For `x : G`, the subgroup of `K` consisting of those `k` for which
`x k x⁻¹` belongs to `H`. -/
def intersection (H K : Subgroup G) (x : G) : Subgroup K where
  carrier := {a | x * (a : G) * x⁻¹ ∈ H}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change x * ((a * b : K) : G) * x⁻¹ ∈ H
    change x * (a : G) * x⁻¹ ∈ H at ha
    change x * (b : G) * x⁻¹ ∈ H at hb
    rw [show x * ((a * b : K) : G) * x⁻¹ =
      (x * (a : G) * x⁻¹) * (x * (b : G) * x⁻¹) by
        simp only [Subgroup.coe_mul]
        group]
    exact H.mul_mem ha hb
  inv_mem' := by
    intro a ha
    change x * ((a⁻¹ : K) : G) * x⁻¹ ∈ H
    change x * (a : G) * x⁻¹ ∈ H at ha
    rw [show x * ((a⁻¹ : K) : G) * x⁻¹ =
      (x * (a : G) * x⁻¹)⁻¹ by
        simp only [Subgroup.coe_inv]
        group]
    exact H.inv_mem ha

@[simp]
theorem mem_intersection_iff (H K : Subgroup G) (x : G) (a : K) :
    a ∈ intersection H K x ↔ x * (a : G) * x⁻¹ ∈ H :=
  Iff.rfl

/-- Conjugation by `x` maps the Mackey intersection into `H`. -/
def conjugationHom (H K : Subgroup G) (x : G) :
    intersection H K x →* H where
  toFun a := ⟨x * (a : G) * x⁻¹, a.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

@[simp]
theorem conjugationHom_coe (H K : Subgroup G) (x : G)
    (a : intersection H K x) :
    ((conjugationHom H K x a : H) : G) =
      x * (a : K) * x⁻¹ :=
  rfl

/-- The representation of the Mackey intersection obtained by restricting
`V` after conjugating by `x`. -/
abbrev conjugateRestriction (H K : Subgroup G) (x : G)
    (ρ : Representation k H V) :
    Representation k (intersection H K x) V :=
  ρ.comp (conjugationHom H K x)

/-- The carrier of the coinduced summand attached to a double coset. -/
abbrev coinducedSpace (H K : Subgroup G)
    (ρ : Representation k H V)
    (q : DoubleCoset.Quotient (H : Set G) K) :=
  Representation.coindV (intersection H K q.out).subtype
    (conjugateRestriction H K q.out ρ)

/-- The coinduced summand attached to a double coset in `H \ G / K`. -/
abbrev coinducedSummand (H K : Subgroup G)
    (ρ : Representation k H V)
    (q : DoubleCoset.Quotient (H : Set G) K) :
    Representation k K (coinducedSpace H K ρ q) :=
  Representation.coind (intersection H K q.out).subtype
    (conjugateRestriction H K q.out ρ)

/-- A wrapper around a dependent product with coherent additive and module
instances.  The wrapper avoids typeclass diamonds between the direct
`Pi.addCommMonoid` instance and the parent instance of `Pi.addCommGroup`,
which is important when taking traces. -/
structure PiSpace {ι : Type*} (M : ι → Type*) where
  get : (i : ι) → M i

namespace PiSpace

variable {ι : Type*} {M : ι → Type*}

@[ext]
theorem ext {x y : PiSpace M} (h : x.get = y.get) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- The underlying dependent function. -/
def equivFun : PiSpace M ≃ ((i : ι) → M i) where
  toFun := get
  invFun := fun f => ⟨f⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl

instance [(i : ι) → AddCommGroup (M i)] : AddCommGroup (PiSpace M) :=
  equivFun.addCommGroup

@[simp]
theorem get_zero [(i : ι) → AddCommGroup (M i)] (i : ι) :
    (0 : PiSpace M).get i = 0 :=
  rfl

@[simp]
theorem get_add [(i : ι) → AddCommGroup (M i)]
    (x y : PiSpace M) (i : ι) :
    (x + y).get i = x.get i + y.get i :=
  rfl

@[simp]
theorem get_neg [(i : ι) → AddCommGroup (M i)]
    (x : PiSpace M) (i : ι) :
    (-x).get i = -x.get i :=
  rfl

instance [(i : ι) → AddCommGroup (M i)]
    [(i : ι) → Module k (M i)] : SMul k (PiSpace M) :=
  ⟨fun c x => ⟨fun i => c • x.get i⟩⟩

@[simp]
theorem get_smul [(i : ι) → AddCommGroup (M i)]
    [(i : ι) → Module k (M i)] (c : k) (x : PiSpace M) (i : ι) :
    (c • x).get i = c • x.get i :=
  rfl

/-- `get` as an additive homomorphism. -/
def getAddMonoidHom [(i : ι) → AddCommGroup (M i)] :
    PiSpace M →+ ((i : ι) → M i) where
  toFun := get
  map_zero' := by funext i; rfl
  map_add' _ _ := by funext i; rfl

instance [(i : ι) → AddCommGroup (M i)]
    [(i : ι) → Module k (M i)] : Module k (PiSpace M) :=
  Function.Injective.module k getAddMonoidHom
    (fun x y h => by cases x; cases y; congr)
    (fun _ _ => rfl)

/-- The wrapper is linearly equivalent to the underlying dependent function
space. -/
def linearEquivFun [(i : ι) → AddCommGroup (M i)]
    [(i : ι) → Module k (M i)] :
    PiSpace M ≃ₗ[k] ((i : ι) → M i) where
  __ := equivFun
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

/-- Apply a family of endomorphisms componentwise. -/
def componentLinear [(i : ι) → AddCommGroup (M i)]
    [(i : ι) → Module k (M i)]
    (f : (i : ι) → M i →ₗ[k] M i) :
    PiSpace M →ₗ[k] PiSpace M where
  toFun x := ⟨fun i => f i (x.get i)⟩
  map_add' x y := by
    apply PiSpace.ext
    funext i
    exact (f i).map_add _ _
  map_smul' c x := by
    apply PiSpace.ext
    funext i
    exact (f i).map_smul c _

/-- Projection onto one component. -/
def proj [(i : ι) → AddCommGroup (M i)]
    [(i : ι) → Module k (M i)] (i : ι) :
    PiSpace M →ₗ[k] M i where
  toFun x := x.get i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Assemble a linear map from its components. -/
def mkLinear {U : Type*} [AddCommGroup U] [Module k U]
    [(i : ι) → AddCommGroup (M i)]
    [(i : ι) → Module k (M i)]
    (f : (i : ι) → U →ₗ[k] M i) :
    U →ₗ[k] PiSpace M where
  toFun x := ⟨fun i => f i x⟩
  map_add' x y := by
    apply PiSpace.ext
    funext i
    exact (f i).map_add x y
  map_smul' c x := by
    apply PiSpace.ext
    funext i
    exact (f i).map_smul c x

/-- Apply a family of linear equivalences componentwise. -/
def congrLinear {N : ι → Type*}
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module k (M i)]
    [(i : ι) → AddCommGroup (N i)] [(i : ι) → Module k (N i)]
    (e : (i : ι) → M i ≃ₗ[k] N i) :
    PiSpace M ≃ₗ[k] PiSpace N where
  toFun x := ⟨fun i => e i (x.get i)⟩
  invFun x := ⟨fun i => (e i).symm (x.get i)⟩
  left_inv x := by
    apply PiSpace.ext
    funext i
    simp
  right_inv x := by
    apply PiSpace.ext
    funext i
    simp
  map_add' x y := by
    apply PiSpace.ext
    funext i
    simp
  map_smul' c x := by
    apply PiSpace.ext
    funext i
    simp

end PiSpace

/-- The componentwise representation on a dependent product.  For a finite
indexing type this is canonically the ordinary direct sum. -/
def piRepresentation {L : Type*} [Monoid L]
    {ι : Type*} {M : ι → Type*}
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module k (M i)]
    (ρ : (i : ι) → Representation k L (M i)) :
    Representation k L (PiSpace M) where
  toFun g := PiSpace.componentLinear fun i => ρ i g
  map_one' := by
    apply LinearMap.ext
    intro f
    apply PiSpace.ext
    funext i
    simp [PiSpace.componentLinear]
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    apply PiSpace.ext
    funext i
    change ρ i (g * h) (f.get i) = ρ i g (ρ i h (f.get i))
    rw [map_mul]
    rfl

/-- The product of all coinduced Mackey summands. -/
abbrev coinducedSum (H K : Subgroup G) (ρ : Representation k H V) :=
  piRepresentation fun q => coinducedSummand H K ρ q

/-- Restrict a coinduced function to the right `K`-cosets contained in one
double coset, using its chosen representative. -/
def componentMap (H K : Subgroup G) (ρ : Representation k H V)
    (q : DoubleCoset.Quotient (H : Set G) K) :
    Representation.coindV H.subtype ρ →ₗ[k] coinducedSpace H K ρ q where
  toFun f :=
    ⟨fun a => f.1 (q.out * (a : G)), fun l a => by
      have harg :
          q.out *
              ((((intersection H K q.out).subtype l : K) : G) * (a : G)) =
            (H.subtype (conjugationHom H K q.out l) : G) *
              (q.out * (a : G)) := by
        change
          q.out * ((l : K) * (a : G)) =
            (q.out * (l : K) * q.out⁻¹) * (q.out * (a : G))
        group
      change
        f.1 (q.out *
            ((((intersection H K q.out).subtype l : K) * a : K) : G)) =
          ρ (conjugationHom H K q.out l)
            (f.1 (q.out * (a : G)))
      rw [Subgroup.coe_mul, harg]
      exact f.2 (conjugationHom H K q.out l)
        (q.out * (a : G))⟩
  map_add' f g := by
    ext a
    rfl
  map_smul' c f := by
    ext a
    rfl

@[simp]
theorem componentMap_apply (H K : Subgroup G)
    (ρ : Representation k H V)
    (q : DoubleCoset.Quotient (H : Set G) K)
    (f : Representation.coindV H.subtype ρ) (a : K) :
    (componentMap H K ρ q f).1 a =
      f.1 (q.out * (a : G)) :=
  rfl

/-- The canonical restriction map from a coinduced representation to the
product of its double-coset summands. -/
def coinductionToSummands (H K : Subgroup G)
    (ρ : Representation k H V) :
    Representation.IntertwiningMap
      ((Representation.coind H.subtype ρ).comp K.subtype)
      (coinducedSum H K ρ) where
  toLinearMap := PiSpace.mkLinear fun q => componentMap H K ρ q
  isIntertwining' a := by
    apply LinearMap.ext
    intro f
    apply PiSpace.ext
    funext q
    apply Subtype.ext
    funext b
    change
      f.1 ((q.out * (b : G)) * (a : G)) =
        f.1 (q.out * ((b * a : K) : G))
    simp [mul_assoc]

@[simp]
theorem coinductionToSummands_apply (H K : Subgroup G)
    (ρ : Representation k H V)
    (f : Representation.coindV H.subtype ρ)
    (q : DoubleCoset.Quotient (H : Set G) K) (a : K) :
    ((coinductionToSummands H K ρ f).get q).1 a =
      f.1 (q.out * (a : G)) :=
  rfl

/-- Every element has a factorization through the chosen representative of
its double coset. -/
theorem exists_factorPair (H K : Subgroup G) (y : G) :
    ∃ p : H × K,
      y = (p.1 : G) * (DoubleCoset.mk H K y).out * (p.2 : G) := by
  have hq :
      DoubleCoset.mk H K (DoubleCoset.mk H K y).out =
        DoubleCoset.mk H K y :=
    DoubleCoset.out_eq' H K _
  rcases (DoubleCoset.eq H K _ _).mp hq with
    ⟨h, hh, a, ha, hy⟩
  exact ⟨(⟨h, hh⟩, ⟨a, ha⟩), hy⟩

/-- A fixed factorization of an element through the chosen representative of
its double coset. -/
def factorPair (H K : Subgroup G) (y : G) : H × K :=
  Classical.choose (exists_factorPair H K y)

theorem factorPair_spec (H K : Subgroup G) (y : G) :
    y = ((factorPair H K y).1 : G) *
        (DoubleCoset.mk H K y).out *
        ((factorPair H K y).2 : G) :=
  Classical.choose_spec (exists_factorPair H K y)

/-- The value determined by a factorization `h x a` and a function in the
summand belonging to the double coset of `x`. -/
def factorValue {H K : Subgroup G} (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) K}
    (F : coinducedSpace H K ρ q) (h : H) (a : K) : V :=
  ρ h (F.1 a)

@[simp]
theorem factorValue_apply {H K : Subgroup G}
    (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) K}
    (F : coinducedSpace H K ρ q) (h : H) (a : K) :
    factorValue ρ F h a = ρ h (F.1 a) :=
  rfl

/-- `factorValue` is independent of the expression of an element as
`h q.out a`. -/
theorem factorValue_eq_of_eq (H K : Subgroup G)
    (ρ : Representation k H V)
    (q : DoubleCoset.Quotient (H : Set G) K)
    (F : coinducedSpace H K ρ q) (h h' : H) (a a' : K)
    (hy :
      (h : G) * q.out * (a : G) =
        (h' : G) * q.out * (a' : G)) :
    factorValue ρ F h a = factorValue ρ F h' a' := by
  let lK : K := a * a'⁻¹
  have hconj :
      q.out * (lK : G) * q.out⁻¹ =
        (((h⁻¹ * h' : H) : H) : G) := by
    change
      q.out * ((a : G) * (a' : G)⁻¹) * q.out⁻¹ =
        (h : G)⁻¹ * (h' : G)
    calc
      q.out * ((a : G) * (a' : G)⁻¹) * q.out⁻¹ =
          (h : G)⁻¹ * ((h : G) * q.out * (a : G)) *
            (a' : G)⁻¹ * q.out⁻¹ := by group
      _ = (h : G)⁻¹ * ((h' : G) * q.out * (a' : G)) *
            (a' : G)⁻¹ * q.out⁻¹ := by rw [hy]
      _ = (h : G)⁻¹ * (h' : G) := by group
  have hlK : lK ∈ intersection H K q.out := by
    change q.out * (lK : G) * q.out⁻¹ ∈ H
    rw [hconj]
    exact (h⁻¹ * h').2
  let l : intersection H K q.out := ⟨lK, hlK⟩
  have hla : (intersection H K q.out).subtype l * a' = a := by
    apply Subtype.ext
    simp [l, lK]
  have hF :
      F.1 a =
        ρ (conjugationHom H K q.out l) (F.1 a') := by
    rw [← hla]
    exact F.2 l a'
  have hs : h * conjugationHom H K q.out l = h' := by
    apply Subtype.ext
    change
      (h : G) * (q.out * (lK : G) * q.out⁻¹) =
        (h' : G)
    rw [hconj]
    simp
  change ρ h (F.1 a) = ρ h' (F.1 a')
  rw [hF, ← Module.End.mul_apply, ← map_mul, hs]

/-- Reassemble a global function from one coinduced function for each double
coset. -/
def assembleFunction (H K : Subgroup G) (ρ : Representation k H V)
    (F : (q : DoubleCoset.Quotient (H : Set G) K) →
      coinducedSpace H K ρ q) (y : G) : V :=
  factorValue ρ (F (DoubleCoset.mk H K y))
    (factorPair H K y).1 (factorPair H K y).2

/-- The reassembled value may be evaluated using any factorization through a
chosen double-coset representative. -/
theorem assembleFunction_eq_of_factorization (H K : Subgroup G)
    (ρ : Representation k H V)
    (F : (q : DoubleCoset.Quotient (H : Set G) K) →
      coinducedSpace H K ρ q)
    (y : G) (q : DoubleCoset.Quotient (H : Set G) K)
    (hq : DoubleCoset.mk H K y = q) (h : H) (a : K)
    (hy : y = (h : G) * q.out * (a : G)) :
    assembleFunction H K ρ F y = factorValue ρ (F q) h a := by
  subst q
  apply factorValue_eq_of_eq H K ρ (DoubleCoset.mk H K y)
  exact (factorPair_spec H K y).symm.trans hy

/-- Reassembly produces an `H`-equivariant function on `G`. -/
theorem assembleFunction_mem_coindV (H K : Subgroup G)
    (ρ : Representation k H V)
    (F : (q : DoubleCoset.Quotient (H : Set G) K) →
      coinducedSpace H K ρ q) :
    assembleFunction H K ρ F ∈ Representation.coindV H.subtype ρ := by
  intro h y
  let q := DoubleCoset.mk H K y
  let p := factorPair H K y
  have hq :
      DoubleCoset.mk H K ((h : G) * y) = q := by
    apply (DoubleCoset.eq H K _ _).2
    exact
      ⟨(h : G)⁻¹, H.inv_mem h.2, 1, K.one_mem, by
        simp⟩
  have hy : (h : G) * y =
      ((h * p.1 : H) : G) * q.out * (p.2 : G) := by
    change
      (h : G) * y =
        ((h * (factorPair H K y).1 : H) : G) *
          (DoubleCoset.mk H K y).out *
          ((factorPair H K y).2 : G)
    calc
      (h : G) * y =
          (h : G) * (((factorPair H K y).1 : G) *
            (DoubleCoset.mk H K y).out *
            ((factorPair H K y).2 : G)) := by
              exact congrArg (fun z : G => (h : G) * z)
                (factorPair_spec H K y)
      _ = ((h * (factorPair H K y).1 : H) : G) *
          (DoubleCoset.mk H K y).out *
          ((factorPair H K y).2 : G) := by
            simp only [Subgroup.coe_mul]
            group
  calc
    assembleFunction H K ρ F ((h : G) * y) =
        factorValue ρ (F q) (h * p.1) p.2 :=
      assembleFunction_eq_of_factorization H K ρ F
        ((h : G) * y) q hq (h * p.1) p.2 hy
    _ = ρ h (factorValue ρ (F q) p.1 p.2) := by
      simp only [factorValue, map_mul, Module.End.mul_apply]
    _ = ρ h (assembleFunction H K ρ F y) := by
      rfl

/-- The linear reassembly map from the family of Mackey summands to the
coinduced-function model. -/
def summandsToCoinduction (H K : Subgroup G)
    (ρ : Representation k H V) :
    PiSpace (fun q : DoubleCoset.Quotient (H : Set G) K =>
        coinducedSpace H K ρ q) →ₗ[k]
      Representation.coindV H.subtype ρ where
  toFun F := ⟨assembleFunction H K ρ F.get,
    assembleFunction_mem_coindV H K ρ F.get⟩
  map_add' F F' := by
    apply Subtype.ext
    funext y
    simp [assembleFunction, factorValue]
  map_smul' c F := by
    apply Subtype.ext
    funext y
    simp [assembleFunction, factorValue]

@[simp]
theorem summandsToCoinduction_apply (H K : Subgroup G)
    (ρ : Representation k H V)
    (F : PiSpace (fun q : DoubleCoset.Quotient (H : Set G) K =>
      coinducedSpace H K ρ q)) (y : G) :
    (summandsToCoinduction H K ρ F).1 y =
      assembleFunction H K ρ F.get y :=
  rfl

/-- Restriction followed by reassembly is the identity on the family of
double-coset summands. -/
theorem coinductionToSummands_summandsToCoinduction
    (H K : Subgroup G) (ρ : Representation k H V)
    (F : PiSpace (fun q : DoubleCoset.Quotient (H : Set G) K =>
      coinducedSpace H K ρ q)) :
    coinductionToSummands H K ρ
        (summandsToCoinduction H K ρ F) = F := by
  apply PiSpace.ext
  funext q
  apply Subtype.ext
  funext a
  let y : G := q.out * (a : G)
  have hq : DoubleCoset.mk H K y = q := by
    calc
      DoubleCoset.mk H K y =
          DoubleCoset.mk H K q.out := by
        symm
        apply (DoubleCoset.eq H K _ _).2
        exact ⟨1, H.one_mem, (a : G), a.2, by simp [y]⟩
      _ = q := DoubleCoset.out_eq' H K q
  have hy : y = ((1 : H) : G) * q.out * (a : G) := by
    simp [y]
  have hvalue :=
    assembleFunction_eq_of_factorization H K ρ F.get y q hq 1 a hy
  change assembleFunction H K ρ F.get y = (F.get q).1 a
  simpa [factorValue] using hvalue

/-- Reassembly followed by restriction is the identity on the global
coinduced function. -/
theorem summandsToCoinduction_coinductionToSummands
    (H K : Subgroup G) (ρ : Representation k H V)
    (f : Representation.coindV H.subtype ρ) :
    summandsToCoinduction H K ρ
        (coinductionToSummands H K ρ f) = f := by
  apply Subtype.ext
  funext y
  let q := DoubleCoset.mk H K y
  let p := factorPair H K y
  change
    ρ p.1 (f.1 (q.out * (p.2 : G))) = f.1 y
  rw [← f.2 p.1 (q.out * (p.2 : G))]
  apply congrArg f.1
  change
      ((factorPair H K y).1 : G) *
          ((DoubleCoset.mk H K y).out *
            ((factorPair H K y).2 : G)) = y
  simpa [mul_assoc] using (factorPair_spec H K y).symm

/-- The double-coset restriction map is bijective. -/
theorem coinductionToSummands_bijective (H K : Subgroup G)
    (ρ : Representation k H V) :
    Function.Bijective (coinductionToSummands H K ρ) := by
  constructor
  · intro f g hfg
    have h := congrArg (fun F => summandsToCoinduction H K ρ F) hfg
    simpa only [summandsToCoinduction_coinductionToSummands] using h
  · intro F
    exact
      ⟨summandsToCoinduction H K ρ F,
        coinductionToSummands_summandsToCoinduction H K ρ F⟩

/-- Mackey decomposition in the coinduced-function model. -/
def coinductionEquivSummands (H K : Subgroup G)
    (ρ : Representation k H V) :
    Representation.Equiv
      ((Representation.coind H.subtype ρ).comp K.subtype)
      (coinducedSum H K ρ) :=
  (coinductionToSummands H K ρ).ofBijective
    (coinductionToSummands_bijective H K ρ)

/-- Restrict an equivalence of representations along a monoid homomorphism. -/
def compEquiv {L : Type*} [Monoid L]
    {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    {ρ : Representation k G M} {σ : Representation k G N}
    (φ : L →* G) (e : Representation.Equiv ρ σ) :
    Representation.Equiv (ρ.comp φ) (σ.comp φ) :=
  Representation.Equiv.mk e.toLinearEquiv fun a => e.isIntertwining' (φ a)

/-- A componentwise equivalence induces an equivalence of the corresponding
dependent-product representations. -/
def piEquiv {L : Type*} [Monoid L] {ι : Type*}
    {M N : ι → Type*}
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module k (M i)]
    [(i : ι) → AddCommGroup (N i)] [(i : ι) → Module k (N i)]
    (ρ : (i : ι) → Representation k L (M i))
    (σ : (i : ι) → Representation k L (N i))
    (e : (i : ι) → Representation.Equiv (ρ i) (σ i)) :
    Representation.Equiv (piRepresentation ρ) (piRepresentation σ) :=
  Representation.Equiv.mk
    (PiSpace.congrLinear fun i => (e i).toLinearEquiv) fun g => by
      apply LinearMap.ext
      intro f
      apply PiSpace.ext
      funext i
      exact LinearMap.ext_iff.mp ((e i).isIntertwining' g) (f.get i)

/-- Intertwining maps into a dependent product are the dependent product of
the component intertwining-map spaces. -/
def intertwiningMapToPiEquiv {L : Type*} [Monoid L]
    {U : Type*} [AddCommGroup U] [Module k U]
    (τ : Representation k L U) {ι : Type*}
    {M : ι → Type*} [(i : ι) → AddCommGroup (M i)]
    [(i : ι) → Module k (M i)]
    (ρ : (i : ι) → Representation k L (M i)) :
    τ.IntertwiningMap (piRepresentation ρ) ≃ₗ[k]
      ((i : ι) → τ.IntertwiningMap (ρ i)) where
  toFun f i :=
    { toLinearMap := PiSpace.proj i ∘ₗ f.toLinearMap
      isIntertwining' := fun g => by
        ext x
        have hf := LinearMap.ext_iff.mp (f.isIntertwining' g) x
        change (f (τ g x)).get i = ρ i g ((f x).get i)
        exact congrArg (fun z => z.get i) hf }
  invFun F :=
    { toLinearMap := PiSpace.mkLinear fun i => (F i).toLinearMap
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro x
        apply PiSpace.ext
        funext i
        exact LinearMap.ext_iff.mp ((F i).isIntertwining' g) x }
  left_inv f := by
    ext x i
    rfl
  right_inv F := by
    funext i
    ext x
    rfl
  map_add' f g := by
    funext i
    ext x
    rfl
  map_smul' c f := by
    funext i
    ext x
    rfl

/-- Postcomposition by an equivalence of representations is a linear
equivalence on intertwining-map spaces. -/
def postcomposeEquiv {L : Type*} [Monoid L]
    {U M N : Type*}
    [AddCommGroup U] [Module k U]
    [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (τ : Representation k L U)
    {ρ : Representation k L M} {σ : Representation k L N}
    (e : Representation.Equiv ρ σ) :
    τ.IntertwiningMap ρ ≃ₗ[k] τ.IntertwiningMap σ where
  toFun f := e.toIntertwiningMap.comp f
  invFun f := e.symm.toIntertwiningMap.comp f
  left_inv f := by
    ext x
    exact e.toLinearEquiv.injective (by simp)
  right_inv f := by
    ext x
    simp
  map_add' f g := by
    ext x
    simp
  map_smul' c f := by
    ext x
    simp

section Trace

variable {F₀ : Type*} [Field F₀] {ι : Type*} [Fintype ι]
variable {M₀ : ι → Type*}
variable [(i : ι) → AddCommGroup (M₀ i)]
variable [(i : ι) → Module F₀ (M₀ i)]
variable [(i : ι) → Module.Finite F₀ (M₀ i)]

/-- The trace of a componentwise endomorphism of a finite dependent product
is the sum of the component traces. -/
theorem trace_pi (f : (i : ι) → M₀ i →ₗ[F₀] M₀ i) :
    LinearMap.trace F₀ ((i : ι) → M₀ i)
        (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) =
      ∑ i, LinearMap.trace F₀ (M₀ i) (f i) := by
  classical
  let b (i : ι) := Module.Free.chooseBasis F₀ (M₀ i)
  let B := Pi.basis b
  rw [LinearMap.trace_eq_matrix_trace F₀ B]
  simp_rw [LinearMap.trace_eq_matrix_trace F₀ (b _)]
  have hmatrix :
      LinearMap.toMatrix B B
          (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) =
        Matrix.blockDiagonal'
          (fun i => LinearMap.toMatrix (b i) (b i) (f i)) := by
    ext ⟨i, m⟩ ⟨j, n⟩
    simp only [LinearMap.toMatrix_apply', B, Pi.basis_apply,
      Pi.basis_repr, LinearMap.pi_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.coe_proj, Function.eval,
      Matrix.blockDiagonal'_apply]
    split_ifs with h
    · subst j
      simp
    · simp [h]
  rw [hmatrix, Matrix.trace_blockDiagonal']

/-- The trace formula transported to the coherent dependent-product
wrapper used by `piRepresentation`. -/
theorem trace_piSpace (f : (i : ι) → M₀ i →ₗ[F₀] M₀ i) :
    LinearMap.trace F₀ (PiSpace M₀) (PiSpace.componentLinear f) =
      ∑ i, LinearMap.trace F₀ (M₀ i) (f i) := by
  let e : PiSpace M₀ ≃ₗ[F₀] ((i : ι) → M₀ i) :=
    PiSpace.linearEquivFun
  have hconj :
      e.conj (PiSpace.componentLinear f) =
        LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i := by
    apply LinearMap.ext
    intro x
    funext i
    rfl
  calc
    LinearMap.trace F₀ (PiSpace M₀) (PiSpace.componentLinear f) =
        LinearMap.trace F₀ ((i : ι) → M₀ i)
          (e.conj (PiSpace.componentLinear f)) :=
      (LinearMap.trace_conj' (PiSpace.componentLinear f) e).symm
    _ = LinearMap.trace F₀ ((i : ι) → M₀ i)
          (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) := by
      rw [hconj]
    _ = ∑ i, LinearMap.trace F₀ (M₀ i) (f i) :=
      trace_pi f

/-- Character of a finite componentwise product representation. -/
theorem piRepresentation_character {L : Type*} [Monoid L]
    (ρ : (i : ι) → Representation F₀ L (M₀ i)) (g : L) :
    (piRepresentation ρ).character g =
      ∑ i, (ρ i).character g :=
  trace_piSpace fun i => ρ i g

end Trace

section FiniteInduction

variable {R X W : Type u} [Field R] [Group X] [Finite X]
variable [AddCommGroup W] [Module R W]

/-- The carrier of the induced Mackey summand. -/
abbrev inducedSpace (H K : Subgroup X) (ρ : Representation R H W)
    (q : DoubleCoset.Quotient (H : Set X) K) :=
  Representation.IndV (intersection H K q.out).subtype
    (conjugateRestriction H K q.out ρ)

/-- The induced Mackey summand associated to `q : H \ G / K`. -/
abbrev inducedSummand (H K : Subgroup X) (ρ : Representation R H W)
    (q : DoubleCoset.Quotient (H : Set X) K) :
    Representation R K (inducedSpace H K ρ q) :=
  Representation.ind (intersection H K q.out).subtype
    (conjugateRestriction H K q.out ρ)

/-- The dependent product of the induced Mackey summands.  Since the
double-coset set is finite, this is the finite direct sum. -/
abbrev inducedSum (H K : Subgroup X) (ρ : Representation R H W) :=
  piRepresentation fun q => inducedSummand H K ρ q

/-- Induction and coinduction from a subgroup of a finite group are
equivalent, in the unbundled representation API. -/
def indCoindEquiv (S : Subgroup X) (ρ : Representation R S W) :
    Representation.Equiv
      (Representation.ind S.subtype ρ)
      (Representation.coind S.subtype ρ) := by
  classical
  exact Representation.equivOfIso
    (Rep.indCoindIso (S := S) (Rep.of ρ))

/-- Each coinduced Mackey summand is equivalent to the corresponding induced
summand. -/
def coinducedSummandEquivInducedSummand
    (H K : Subgroup X) (ρ : Representation R H W)
    (q : DoubleCoset.Quotient (H : Set X) K) :
    Representation.Equiv
      (coinducedSummand H K ρ q)
      (inducedSummand H K ρ q) :=
  (indCoindEquiv (intersection H K q.out)
    (conjugateRestriction H K q.out ρ)).symm

/-- Replace coinduction by induction in every Mackey summand. -/
def coinducedSumEquivInducedSum
    (H K : Subgroup X) (ρ : Representation R H W) :
    Representation.Equiv
      (coinducedSum H K ρ)
      (inducedSum H K ρ) :=
  piEquiv
    (fun q => coinducedSummand H K ρ q)
    (fun q => inducedSummand H K ρ q)
    (coinducedSummandEquivInducedSummand H K ρ)

/-- Mackey decomposition with coinduced summands.  This is often the most
convenient form for evaluating maps componentwise. -/
def inductionEquivCoinducedSum (H K : Subgroup X)
    (ρ : Representation R H W) :
    Representation.Equiv
      ((Representation.ind H.subtype ρ).comp K.subtype)
      (coinducedSum H K ρ) :=
  (compEquiv K.subtype (indCoindEquiv H ρ)).trans
    (coinductionEquivSummands H K ρ)

/-- **Mackey decomposition.**  Restricting an induced representation from
`X` to `K` is equivalent to the finite direct sum, indexed by `H \ X / K`,
of the representations induced from
`K ∩ x⁻¹Hx` (in the convention encoded by `intersection`). -/
def inductionEquivInducedSum (H K : Subgroup X)
    (ρ : Representation R H W) :
    Representation.Equiv
      ((Representation.ind H.subtype ρ).comp K.subtype)
      (inducedSum H K ρ) :=
  (inductionEquivCoinducedSum H K ρ).trans
    (coinducedSumEquivInducedSum H K ρ)

/-- Exact Hom-space form of the Mackey decomposition: maps into the
restriction of an induced representation are the families of maps into its
coinduced double-coset summands. -/
def homIntoRestrictedInductionEquiv
    (H K : Subgroup X) (ρ : Representation R H W)
    {U : Type u} [AddCommGroup U] [Module R U]
    (τ : Representation R K U) :
    τ.IntertwiningMap
        ((Representation.ind H.subtype ρ).comp K.subtype) ≃ₗ[R]
      ((q : DoubleCoset.Quotient (H : Set X) K) →
        τ.IntertwiningMap (coinducedSummand H K ρ q)) :=
  (postcomposeEquiv τ (inductionEquivCoinducedSum H K ρ)).trans
    (intertwiningMapToPiEquiv τ
      (fun q => coinducedSummand H K ρ q))

end FiniteInduction

section FDRep

variable {F X : Type u} [Field F] [Group X] [Finite X]

/-- The conjugate-restricted finite-dimensional representation on a Mackey
intersection. -/
abbrev conjugateRestrictionFDRep (H K : Subgroup X) (x : X)
    (V : FDRep F H) : FDRep F (intersection H K x) :=
  FDRep.of (conjugateRestriction H K x V.ρ)

/-- An induced Mackey summand as a finite-dimensional representation of
`K`. -/
abbrev summand (H K : Subgroup X) (V : FDRep F H)
    (q : DoubleCoset.Quotient (H : Set X) K) : FDRep F K :=
  FDRep.ind (intersection H K q.out).subtype
    (conjugateRestrictionFDRep H K q.out V)

end FDRep

section CharacterFormula

variable {X : Type} [Group X] [Finite X]

local instance groupFintype : Fintype X :=
  Fintype.ofFinite X

local instance subgroupFintype (S : Subgroup X) : Fintype S :=
  Fintype.ofFinite S

local instance doubleCosetFintype (H K : Subgroup X) :
    Fintype (DoubleCoset.Quotient (H : Set X) K) := by
  classical
  exact Fintype.ofSurjective (DoubleCoset.mk H K)
    Quotient.mk''_surjective

local instance inducedSpaceFinite (H K : Subgroup X)
    (V : FDRep ℂ H)
    (q : DoubleCoset.Quotient (H : Set X) K) :
    Module.Finite ℂ (inducedSpace H K V.ρ q) := by
  change Module.Finite ℂ (summand H K V q)
  infer_instance

/-- Character form of Mackey decomposition, expressed as a sum of the
characters of its induced summands. -/
theorem character_eq_sum_inducedSummand (H K : Subgroup X)
    (V : FDRep ℂ H) (a : K) :
    Representation.character
        ((Representation.ind H.subtype V.ρ).comp K.subtype) a =
      ∑ q : DoubleCoset.Quotient (H : Set X) K,
        Representation.character (inducedSummand H K V.ρ q) a := by
  calc
    Representation.character
        ((Representation.ind H.subtype V.ρ).comp K.subtype) a =
        Representation.character (inducedSum H K V.ρ) a :=
      congrFun
        (Representation.char_iso
          (inductionEquivInducedSum H K V.ρ)) a
    _ = ∑ q : DoubleCoset.Quotient (H : Set X) K,
          Representation.character (inducedSummand H K V.ρ q) a :=
      by
        change
          Representation.character
              (piRepresentation
                (fun q => inducedSummand H K V.ρ q)) a =
            ∑ q : DoubleCoset.Quotient (H : Set X) K,
              Representation.character
                (inducedSummand H K V.ρ q) a
        exact piRepresentation_character
          (fun q => inducedSummand H K V.ρ q) a

/-- Finite-dimensional form of the Mackey character formula. -/
theorem character_eq_sum_summand (H K : Subgroup X)
    (V : FDRep ℂ H) (a : K) :
    (FDRep.res K.subtype (FDRep.ind H.subtype V)).character a =
      ∑ q : DoubleCoset.Quotient (H : Set X) K,
        (summand H K V q).character a :=
  character_eq_sum_inducedSummand H K V a

/-- Classical class-function form of the Mackey character formula.  Each
summand is evaluated by the ordinary induced-character formula proved in
`InductionCharacter`. -/
theorem character_eq_sum_induce (H K : Subgroup X)
    (V : FDRep ℂ H) (a : K) :
    (FDRep.res K.subtype (FDRep.ind H.subtype V)).character a =
      ∑ q : DoubleCoset.Quotient (H : Set X) K,
        ClassFunction.induce (intersection H K q.out)
          (conjugateRestrictionFDRep H K q.out V).characterClassFunction a := by
  rw [character_eq_sum_summand]
  apply Finset.sum_congr rfl
  intro q _
  exact InductionCharacter.ind_character_eq_induce
    (intersection H K q.out)
    (conjugateRestrictionFDRep H K q.out V) a

end CharacterFormula

end Mackey

end McKayConjecture
