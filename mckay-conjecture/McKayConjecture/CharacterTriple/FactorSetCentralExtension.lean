/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.MinimalAxioms
import McKayConjecture.CharacterTriple.FactorSet
import McKayConjecture.GroupTheory.UniversalCentralExtension

/-!
# The central extension attached to a factor set

A normalized factor set `α : FactorSet G A` defines a group on the set
`G × A`, with multiplication

`(g, a) * (h, b) = (g * h, α g h * a * b)`.

The cocycle identity is exactly the associativity condition for this
multiplication.  Projection to `G` is a central extension whose kernel is the
canonically embedded copy of `A`.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

variable {G : Type u} {A : Type v} [Group G] [CommGroup A]

/-- The underlying type of the central extension associated to a normalized
factor set.  It is a type synonym for `G × A`, allowing it to carry the
factor-set-twisted multiplication rather than the ordinary product
multiplication. -/
def CentralExtensionGroup
    (α : FactorSet G A) (_hα : α.IsNormalized) :=
  G × A

namespace CentralExtensionGroup

variable (α : FactorSet G A) (hα : α.IsNormalized)

/-- Construct an element of the factor-set central extension. -/
def mk (g : G) (a : A) : CentralExtensionGroup α hα :=
  (g, a)

/-- The base-group coordinate of an element of the factor-set extension. -/
def base (x : CentralExtensionGroup α hα) : G :=
  x.1

/-- The coefficient coordinate of an element of the factor-set extension. -/
def coefficient (x : CentralExtensionGroup α hα) : A :=
  x.2

@[ext]
theorem ext {x y : CentralExtensionGroup α hα}
    (hbase : base α hα x = base α hα y)
    (hcoefficient : coefficient α hα x = coefficient α hα y) :
    x = y := by
  exact Prod.ext hbase hcoefficient

instance : One (CentralExtensionGroup α hα) where
  one := mk α hα 1 1

instance : Mul (CentralExtensionGroup α hα) where
  mul x y :=
    mk α hα
      (base α hα x * base α hα y)
      (α (base α hα x) (base α hα y) *
        coefficient α hα x * coefficient α hα y)

instance : Inv (CentralExtensionGroup α hα) where
  inv x :=
    mk α hα
      (base α hα x)⁻¹
      ((α (base α hα x)⁻¹ (base α hα x) *
        coefficient α hα x)⁻¹)

@[simp]
theorem base_mk (g : G) (a : A) :
    base α hα (mk α hα g a) = g :=
  rfl

@[simp]
theorem coefficient_mk (g : G) (a : A) :
    coefficient α hα (mk α hα g a) = a :=
  rfl

@[simp]
theorem base_one :
    base α hα (1 : CentralExtensionGroup α hα) = 1 :=
  rfl

@[simp]
theorem coefficient_one :
    coefficient α hα (1 : CentralExtensionGroup α hα) = 1 :=
  rfl

@[simp]
theorem base_mul (x y : CentralExtensionGroup α hα) :
    base α hα (x * y) = base α hα x * base α hα y :=
  rfl

@[simp]
theorem coefficient_mul (x y : CentralExtensionGroup α hα) :
    coefficient α hα (x * y) =
      α (base α hα x) (base α hα y) *
        coefficient α hα x * coefficient α hα y :=
  rfl

@[simp]
theorem base_inv (x : CentralExtensionGroup α hα) :
    base α hα x⁻¹ = (base α hα x)⁻¹ :=
  rfl

@[simp]
theorem coefficient_inv (x : CentralExtensionGroup α hα) :
    coefficient α hα x⁻¹ =
      ((α (base α hα x)⁻¹ (base α hα x) *
        coefficient α hα x)⁻¹) :=
  rfl

instance instGroup : Group (CentralExtensionGroup α hα) :=
  Group.ofLeftAxioms
    (fun x y z ↦ by
      apply ext α hα
      · simp only [base_mul, mul_assoc]
      · simp only [coefficient_mul, base_mul]
        calc
          α (base α hα x * base α hα y) (base α hα z) *
                (α (base α hα x) (base α hα y) *
                  coefficient α hα x * coefficient α hα y) *
              coefficient α hα z =
              (α (base α hα x * base α hα y) (base α hα z) *
                α (base α hα x) (base α hα y)) *
                (coefficient α hα x * coefficient α hα y *
                  coefficient α hα z) := by
                    ac_rfl
          _ =
              (α (base α hα y) (base α hα z) *
                α (base α hα x)
                  (base α hα y * base α hα z)) *
                (coefficient α hα x * coefficient α hα y *
                  coefficient α hα z) := by
                    rw [α.cocycle]
          _ =
              α (base α hα x)
                  (base α hα y * base α hα z) *
                coefficient α hα x *
                (α (base α hα y) (base α hα z) *
                  coefficient α hα y * coefficient α hα z) := by
                    ac_rfl)
    (fun x ↦ by
      apply ext α hα
      · simp only [base_one, base_mul, one_mul]
      · simp only [coefficient_one, coefficient_mul, base_one, hα.1, one_mul])
    (fun x ↦ by
      apply ext α hα
      · simp only [base_inv, base_mul, inv_mul_cancel, base_one]
      · simp only [coefficient_inv, coefficient_mul, base_inv,
          coefficient_one]
        rw [mul_inv_rev]
        calc
          _ =
              (α (base α hα x)⁻¹ (base α hα x) *
                (α (base α hα x)⁻¹ (base α hα x))⁻¹) *
                ((coefficient α hα x)⁻¹ *
                  coefficient α hα x) := by
                    ac_rfl
          _ = 1 := by simp)

instance instFinite [Finite G] [Finite A] :
    Finite (CentralExtensionGroup α hα) := by
  change Finite (G × A)
  infer_instance

instance instFintype [Fintype G] [Fintype A] :
    Fintype (CentralExtensionGroup α hα) := by
  change Fintype (G × A)
  infer_instance

/-- The canonical projection of the factor-set extension onto its base group. -/
def projection : CentralExtensionGroup α hα →* G where
  toFun := base α hα
  map_one' := base_one α hα
  map_mul' := base_mul α hα

@[simp]
theorem projection_apply (x : CentralExtensionGroup α hα) :
    projection α hα x = base α hα x :=
  rfl

/-- Projection from the factor-set extension is surjective. -/
theorem projection_surjective :
    Function.Surjective (projection α hα) := by
  intro g
  exact ⟨mk α hα g 1, rfl⟩

/-- The canonical copy of the coefficient group in the factor-set extension. -/
def coefficientEmbedding : A →* CentralExtensionGroup α hα where
  toFun a := mk α hα 1 a
  map_one' := rfl
  map_mul' a b := by
    apply ext α hα
    · simp
    · simp [hα.1]

@[simp]
theorem coefficientEmbedding_apply (a : A) :
    coefficientEmbedding α hα a = mk α hα 1 a :=
  rfl

/-- The coefficient copy embeds injectively in the factor-set extension. -/
theorem coefficientEmbedding_injective :
    Function.Injective (coefficientEmbedding α hα) := by
  intro a b hab
  exact congrArg (coefficient α hα) hab

@[simp]
theorem projection_coefficientEmbedding (a : A) :
    projection α hα (coefficientEmbedding α hα a) = 1 :=
  rfl

/-- The kernel of projection is exactly the canonical coefficient copy. -/
theorem projection_ker_eq_coefficientEmbedding_range :
    (projection α hα).ker = (coefficientEmbedding α hα).range := by
  ext x
  constructor
  · intro hx
    change base α hα x = 1 at hx
    refine ⟨coefficient α hα x, ?_⟩
    apply ext α hα
    · simpa using hx.symm
    · rfl
  · rintro ⟨a, rfl⟩
    exact projection_coefficientEmbedding α hα a

/-- The canonical coefficient copy is central in the factor-set extension. -/
theorem coefficientEmbedding_range_le_center :
    (coefficientEmbedding α hα).range ≤
      Subgroup.center (CentralExtensionGroup α hα) := by
  rintro x ⟨a, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply ext α hα
  · simp
  · simp only [coefficientEmbedding_apply, base_mk,
      coefficient_mul, coefficient_mk, hα.1, hα.2, one_mul]
    exact mul_comm (coefficient α hα y) a

/-- The kernel of projection is central. -/
theorem projection_ker_le_center :
    (projection α hα).ker ≤
      Subgroup.center (CentralExtensionGroup α hα) := by
  rw [projection_ker_eq_coefficientEmbedding_range]
  exact coefficientEmbedding_range_le_center α hα

/-- The central extension associated to a normalized factor set. -/
def centralExtension :
    GroupTheory.CentralExtension (CentralExtensionGroup α hα) G where
  projection := projection α hα
  surjective := projection_surjective α hα
  ker_le_center := projection_ker_le_center α hα

end CentralExtensionGroup
end FactorSet
end CharacterTriple
end McKayConjecture
