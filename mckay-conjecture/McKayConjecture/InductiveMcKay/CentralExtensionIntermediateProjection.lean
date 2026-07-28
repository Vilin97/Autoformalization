/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralExtensionSylowNormalizer
import McKayConjecture.GroupTheory.SurjectiveImageProper
import McKayConjecture.InductiveMcKay.Condition

/-!
# Projecting local intermediate subgroups through central extensions

Let `E : A → Q` be a finite-source central extension, let `S` be a Sylow
subgroup of `Q`, and let `T` be its unique Sylow lift to `A`.  Any local
inductive-McKay datum at `T` supplies an intermediate subgroup containing
`N_A(T)`.  Its image under `E` therefore contains `N_Q(S)`.

The central kernel lies in every such intermediate: it lies in the center,
hence in `N_A(T)`.  Consequently the image intermediate is proper whenever
the original local datum certifies properness.  Finally, restricting `E` to
the intermediate and its image gives another central extension.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace InductiveMcKay
namespace LocalInductiveMcKayData

open GroupTheory

variable {A : Type u} {Q : Type v}
variable [Group A] [Group Q] [Finite A]
variable {p : ℕ}

/-- The image of a local intermediate subgroup under a group homomorphism. -/
def projectedIntermediate
    {T : Sylow p A}
    (d : LocalInductiveMcKayData T)
    (f : A →* Q) :
    Subgroup Q :=
  d.intermediate.map f

@[simp]
theorem mem_projectedIntermediate
    {T : Sylow p A}
    (d : LocalInductiveMcKayData T)
    (f : A →* Q) (q : Q) :
    q ∈ d.projectedIntermediate f ↔
      ∃ a : A, a ∈ d.intermediate ∧ f a = q :=
  Subgroup.mem_map

/-- The homomorphism from a local intermediate to its image. -/
def intermediateProjection
    {T : Sylow p A}
    (d : LocalInductiveMcKayData T)
    (f : A →* Q) :
    d.intermediate →* d.projectedIntermediate f :=
  f.subgroupMap d.intermediate

@[simp]
theorem intermediateProjection_apply_coe
    {T : Sylow p A}
    (d : LocalInductiveMcKayData T)
    (f : A →* Q) (a : d.intermediate) :
    ((d.intermediateProjection f a :
        d.projectedIntermediate f) : Q) =
      f (a : A) :=
  rfl

theorem intermediateProjection_surjective
    {T : Sylow p A}
    (d : LocalInductiveMcKayData T)
    (f : A →* Q) :
    Function.Surjective (d.intermediateProjection f) :=
  MonoidHom.subgroupMap_surjective f d.intermediate

@[simp]
theorem intermediateProjection_range
    {T : Sylow p A}
    (d : LocalInductiveMcKayData T)
    (f : A →* Q) :
    (d.intermediateProjection f).range = ⊤ :=
  MonoidHom.range_eq_top.mpr
    (d.intermediateProjection_surjective f)

@[simp]
theorem intermediateProjection_ker
    {T : Sylow p A}
    (d : LocalInductiveMcKayData T)
    (f : A →* Q) :
    (d.intermediateProjection f).ker =
      f.ker.subgroupOf d.intermediate :=
  by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
      Subtype.ext_iff]
    rfl

variable [Fact p.Prime]
variable (E : CentralExtension A Q) (S : Sylow p Q)
variable (d : LocalInductiveMcKayData (E.sylowLift S))

/-- The target Sylow normalizer lies in the projected local intermediate. -/
theorem normalizer_le_projectedIntermediate :
    Subgroup.normalizer (S : Set Q) ≤
      d.projectedIntermediate E.projection := by
  intro q hq
  let qNormalizer :
      Subgroup.normalizer (S : Set Q) :=
    ⟨q, hq⟩
  obtain ⟨aNormalizer, ha⟩ :=
    E.sylowNormalizerProjection_surjective
      S qNormalizer
  refine
    ⟨(aNormalizer : A),
      d.normalizer_le aNormalizer.property, ?_⟩
  exact congrArg Subtype.val ha

/-- In particular, the target Sylow subgroup lies in the projected
intermediate. -/
theorem sylow_le_projectedIntermediate :
    (S : Subgroup Q) ≤
      d.projectedIntermediate E.projection :=
  Subgroup.le_normalizer.trans
    (d.normalizer_le_projectedIntermediate E S)

/-- The central-extension kernel lies in every local intermediate at the
lifted Sylow subgroup. -/
theorem ker_le_intermediate :
    E.projection.ker ≤ d.intermediate :=
  (E.ker_le_sylowLift_normalizer S).trans
    d.normalizer_le

/-- Properness of the local intermediate descends through the central
extension. -/
theorem projectedIntermediate_lt_top_of_normalizer_ne_top
    (hnormalizer :
      Subgroup.normalizer
          (E.sylowLift S : Set A) ≠
        ⊤) :
    d.projectedIntermediate E.projection < ⊤ :=
  GroupTheory.map_lt_top_of_surjective_of_ker_le_of_lt_top
    E.projection E.surjective d.intermediate
    (d.ker_le_intermediate E S)
    (d.proper_of_normalizer_ne_top hnormalizer)

/-- The restricted intermediate projection still has central kernel. -/
theorem intermediateProjection_ker_le_center :
    (d.intermediateProjection E.projection).ker ≤
      Subgroup.center d.intermediate := by
  intro x hx
  have hxOne :
      E.projection (x : A) = 1 := by
    exact
      congrArg Subtype.val
        (MonoidHom.mem_ker.mp hx)
  have hxCenter :
      (x : A) ∈ Subgroup.center A :=
    E.ker_le_center
      (MonoidHom.mem_ker.mpr hxOne)
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact
    Subgroup.mem_center_iff.mp hxCenter (y : A)

/-- The central extension induced from the local intermediate onto its
projected intermediate. -/
def intermediateCentralExtension :
    CentralExtension
      d.intermediate
      (d.projectedIntermediate E.projection) where
  projection := d.intermediateProjection E.projection
  surjective :=
    d.intermediateProjection_surjective E.projection
  ker_le_center :=
    d.intermediateProjection_ker_le_center E S

@[simp]
theorem intermediateCentralExtension_projection :
    (d.intermediateCentralExtension E S).projection =
      d.intermediateProjection E.projection :=
  rfl

@[simp]
theorem intermediateCentralExtension_projection_apply_coe
    (a : d.intermediate) :
    (((d.intermediateCentralExtension E S).projection a :
        d.projectedIntermediate E.projection) : Q) =
      E.projection (a : A) :=
  rfl

@[simp]
theorem intermediateCentralExtension_projection_range :
    (d.intermediateCentralExtension E S).projection.range =
      ⊤ :=
  d.intermediateProjection_range E.projection

@[simp]
theorem intermediateCentralExtension_projection_ker :
    (d.intermediateCentralExtension E S).projection.ker =
      E.projection.ker.subgroupOf d.intermediate :=
  d.intermediateProjection_ker E.projection

/-- The target Sylow subgroup, regarded inside the projected intermediate. -/
def projectedSylow :
    Sylow p (d.projectedIntermediate E.projection) :=
  S.subtype (d.sylow_le_projectedIntermediate E S)

/-- The normalizer projection supplied by the induced intermediate central
extension.  Its source is the unique Sylow lift of `projectedSylow`. -/
def intermediateNormalizerProjection :
    Subgroup.normalizer
        ((d.intermediateCentralExtension E S).sylowLift
          (d.projectedSylow E S) :
          Set d.intermediate) →*
      Subgroup.normalizer
        (d.projectedSylow E S :
          Set (d.projectedIntermediate E.projection)) :=
  (d.intermediateCentralExtension E S).sylowNormalizerProjection
    (d.projectedSylow E S)

@[simp]
theorem intermediateNormalizerProjection_apply_coe
    (x :
      Subgroup.normalizer
        ((d.intermediateCentralExtension E S).sylowLift
          (d.projectedSylow E S) :
          Set d.intermediate)) :
    ((d.intermediateNormalizerProjection E S x :
        Subgroup.normalizer
          (d.projectedSylow E S :
            Set (d.projectedIntermediate E.projection))) :
      d.projectedIntermediate E.projection) =
        (d.intermediateCentralExtension E S).projection
          (x : d.intermediate) :=
  rfl

theorem intermediateNormalizerProjection_surjective :
    Function.Surjective
      (d.intermediateNormalizerProjection E S) :=
  (d.intermediateCentralExtension E S)
    |>.sylowNormalizerProjection_surjective
      (d.projectedSylow E S)

@[simp]
theorem intermediateNormalizerProjection_range :
    (d.intermediateNormalizerProjection E S).range =
      ⊤ :=
  MonoidHom.range_eq_top.mpr
    (d.intermediateNormalizerProjection_surjective E S)

@[simp]
theorem intermediateNormalizerProjection_ker :
    (d.intermediateNormalizerProjection E S).ker =
      (E.projection.ker.subgroupOf d.intermediate).subgroupOf
        (Subgroup.normalizer
          ((d.intermediateCentralExtension E S).sylowLift
            (d.projectedSylow E S) :
            Set d.intermediate)) := by
  calc
    (d.intermediateNormalizerProjection E S).ker =
        (d.intermediateCentralExtension E S).projection.ker.subgroupOf
          (Subgroup.normalizer
            ((d.intermediateCentralExtension E S).sylowLift
              (d.projectedSylow E S) :
              Set d.intermediate)) :=
      (d.intermediateCentralExtension E S)
        |>.sylowNormalizerProjection_ker
          (d.projectedSylow E S)
    _ =
        (E.projection.ker.subgroupOf d.intermediate).subgroupOf
          (Subgroup.normalizer
            ((d.intermediateCentralExtension E S).sylowLift
              (d.projectedSylow E S) :
              Set d.intermediate)) := by
      rw [d.intermediateCentralExtension_projection_ker E S]

end LocalInductiveMcKayData
end InductiveMcKay
end McKayConjecture
