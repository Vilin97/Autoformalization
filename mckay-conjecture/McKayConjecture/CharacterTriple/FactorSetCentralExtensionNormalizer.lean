/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCentralExtension
import McKayConjecture.GroupTheory.CentralExtensionSylowNormalizer

/-!
# Normalizers in a factor-set central extension

Let `α` be a normalized factor set on `G`, let `S` be a Sylow subgroup of
`G`, and identify a group `H` with `N_G(S)`.  The normalizer of the unique
Sylow lift of `S` in the concrete factor-set extension of `G` is canonically
isomorphic to the concrete extension defined by pulling `α` back to `H`.

The equivalence is coordinatewise: its base coordinate is transported through
`H ≃* N_G(S)`, and its coefficient coordinate is unchanged.  The final
lemmas record compatibility with the restricted base projection and the
canonical coefficient embedding.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

variable {G : Type u} {H : Type v} {C : Type w}
variable [Group G] [Group H] [CommGroup C]

/-- Pull a factor set back along a group homomorphism. -/
def comap (α : FactorSet G C) (f : H →* G) :
    FactorSet H C where
  toFun x y := α (f x) (f y)
  cocycle' x y z := by
    simpa only [map_mul] using
      α.cocycle (f x) (f y) (f z)

@[simp]
theorem comap_apply
    (α : FactorSet G C) (f : H →* G)
    (x y : H) :
    α.comap f x y = α (f x) (f y) :=
  rfl

/-- Pullback commutes with a gauge change; the scalar cochain is pulled
back along the same homomorphism. -/
theorem comap_gauge
    (α : FactorSet G C) (f : H →* G)
    (c : G → C) :
    (α.gauge c).comap f =
      (α.comap f).gauge (fun h ↦ c (f h)) := by
  ext x y
  simp only [comap_apply, gauge_apply, map_mul]

/-- Pullback preserves cohomology of factor sets. -/
theorem comap_cohomologous
    {α β : FactorSet G C}
    (h : α.Cohomologous β)
    (f : H →* G) :
    (α.comap f).Cohomologous
      (β.comap f) := by
  obtain ⟨c, rfl⟩ := h
  exact
    ⟨fun x ↦ c (f x),
      α.comap_gauge f c⟩

/-- Normalization is preserved by pullback. -/
theorem comap_isNormalized
    (α : FactorSet G C) (f : H →* G)
    (hα : α.IsNormalized) :
    (α.comap f).IsNormalized := by
  constructor
  · intro x
    simpa using hα.1 (f x)
  · intro x
    simpa using hα.2 (f x)

namespace CentralExtensionGroup

variable [Finite G] [Finite C]
variable {p : ℕ} [Fact p.Prime]

/-- The base homomorphism obtained from an identification
`H ≃* N_G(S)`. -/
def sylowNormalizerBaseHom
    (S : Sylow p G)
    (e : H ≃* Subgroup.normalizer (S : Set G)) :
    H →* G :=
  (Subgroup.normalizer (S : Set G)).subtype.comp
    e.toMonoidHom

omit [Finite G] [Fact p.Prime] in
@[simp]
theorem sylowNormalizerBaseHom_apply
    (S : Sylow p G)
    (e : H ≃* Subgroup.normalizer (S : Set G))
    (x : H) :
    sylowNormalizerBaseHom S e x =
      ((e x : Subgroup.normalizer (S : Set G)) : G) :=
  rfl

/-- The factor set on a group identified with the Sylow normalizer. -/
def sylowNormalizerFactorSet
    (α : FactorSet G C)
    (S : Sylow p G)
    (e : H ≃* Subgroup.normalizer (S : Set G)) :
    FactorSet H C :=
  α.comap (sylowNormalizerBaseHom S e)

omit [Finite G] [Finite C] [Fact p.Prime] in
/-- The pulled-back Sylow-normalizer factor set is normalized. -/
theorem sylowNormalizerFactorSet_isNormalized
    (α : FactorSet G C) (hα : α.IsNormalized)
    (S : Sylow p G)
    (e : H ≃* Subgroup.normalizer (S : Set G)) :
    (sylowNormalizerFactorSet α S e).IsNormalized :=
  α.comap_isNormalized
    (sylowNormalizerBaseHom S e) hα

/-- The concrete extension of a group identified with `N_G(S)`, using the
literal pullback of the original factor set. -/
abbrev SylowNormalizerComapCentralExtensionGroup
    (α : FactorSet G C) (hα : α.IsNormalized)
    (S : Sylow p G)
    (e : H ≃* Subgroup.normalizer (S : Set G)) :=
  CentralExtensionGroup
    (sylowNormalizerFactorSet α S e)
    (sylowNormalizerFactorSet_isNormalized
      α hα S e)

/-- The canonical coefficient copy, regarded inside the normalizer of the
unique Sylow lift. -/
def coefficientEmbeddingToSylowLiftNormalizer
    (α : FactorSet G C) (hα : α.IsNormalized)
    (S : Sylow p G) :
    C →*
      Subgroup.normalizer
        ((centralExtension α hα).sylowLift S :
          Set (CentralExtensionGroup α hα)) :=
  (coefficientEmbedding α hα).codRestrict
    (Subgroup.normalizer
      ((centralExtension α hα).sylowLift S :
        Set (CentralExtensionGroup α hα)))
    (by
      intro c
      apply
        (centralExtension α hα).ker_le_sylowLift_normalizer S
      exact
        MonoidHom.mem_ker.mpr
          (projection_coefficientEmbedding α hα c))

/-- The normalizer of the Sylow lift in the concrete extension of `α` is
canonically the concrete extension of the pullback of `α` to the base
Sylow normalizer. -/
def sylowLiftNormalizerEquivComap
    (α : FactorSet G C) (hα : α.IsNormalized)
    (S : Sylow p G)
    (e : H ≃* Subgroup.normalizer (S : Set G)) :
    Subgroup.normalizer
        ((centralExtension α hα).sylowLift S :
          Set (CentralExtensionGroup α hα)) ≃*
      SylowNormalizerComapCentralExtensionGroup
        α hα S e where
  toFun x :=
    mk
      (sylowNormalizerFactorSet α S e)
      (sylowNormalizerFactorSet_isNormalized
        α hα S e)
      (e.symm
        ⟨base α hα (x : CentralExtensionGroup α hα),
          (centralExtension α hα
            ).projection_mem_sylowNormalizer S x⟩)
      (coefficient α hα
        (x : CentralExtensionGroup α hα))
  invFun y :=
    ⟨mk α hα
        ((e
          (base
            (sylowNormalizerFactorSet α S e)
            (sylowNormalizerFactorSet_isNormalized
              α hα S e) y) :
            Subgroup.normalizer (S : Set G)) : G)
        (coefficient
          (sylowNormalizerFactorSet α S e)
          (sylowNormalizerFactorSet_isNormalized
            α hα S e) y),
      by
        apply
          GroupTheory.Sylow.mem_normalizer_of_mapSurjective_mem_normalizer_of_ker_le_center
            (centralExtension α hα).surjective
            (centralExtension α hα).ker_le_center
            ((centralExtension α hα).sylowLift S)
        rw [(centralExtension α hα).sylowLift_mapSurjective]
        exact
          (e
            (base
              (sylowNormalizerFactorSet α S e)
              (sylowNormalizerFactorSet_isNormalized
                α hα S e) y)).property⟩
  left_inv x := by
    apply Subtype.ext
    apply ext α hα
    · simp
    · rfl
  right_inv y := by
    apply ext
    · simp
    · rfl
  map_mul' x y := by
    apply ext
    · apply e.injective
      simp only [base_mk, base_mul, map_mul,
        e.apply_symm_apply]
      apply Subtype.ext
      rfl
    · change
        α (base α hα (x : CentralExtensionGroup α hα))
              (base α hα (y : CentralExtensionGroup α hα)) *
              coefficient α hα
                (x : CentralExtensionGroup α hα) *
            coefficient α hα
              (y : CentralExtensionGroup α hα) =
          α
              (((e
                (e.symm
                  ⟨base α hα
                      (x : CentralExtensionGroup α hα),
                    (centralExtension α hα
                      ).projection_mem_sylowNormalizer S x⟩) :
                  Subgroup.normalizer (S : Set G)) : G))
              (((e
                (e.symm
                  ⟨base α hα
                      (y : CentralExtensionGroup α hα),
                    (centralExtension α hα
                      ).projection_mem_sylowNormalizer S y⟩) :
                  Subgroup.normalizer (S : Set G)) : G)) *
                coefficient α hα
                  (x : CentralExtensionGroup α hα) *
              coefficient α hα
                (y : CentralExtensionGroup α hα)
      rw [e.apply_symm_apply, e.apply_symm_apply]

/-- Compatibility of the equivalence with the two base projections. -/
@[simp]
theorem sylowLiftNormalizerEquivComap_projection
    (α : FactorSet G C) (hα : α.IsNormalized)
    (S : Sylow p G)
    (e : H ≃* Subgroup.normalizer (S : Set G))
    (x :
      Subgroup.normalizer
        ((centralExtension α hα).sylowLift S :
          Set (CentralExtensionGroup α hα))) :
    e
        (projection
          (sylowNormalizerFactorSet α S e)
          (sylowNormalizerFactorSet_isNormalized
            α hα S e)
          (sylowLiftNormalizerEquivComap
            α hα S e x)) =
      (centralExtension α hα
        ).sylowNormalizerProjection S x := by
  apply Subtype.ext
  change
    ((e
      (e.symm
        ⟨base α hα
            (x : CentralExtensionGroup α hα),
          (centralExtension α hα
            ).projection_mem_sylowNormalizer S x⟩) :
        Subgroup.normalizer (S : Set G)) : G) =
      base α hα
        (x : CentralExtensionGroup α hα)
  rw [e.apply_symm_apply]

/-- The equivalence leaves the coefficient coordinate unchanged. -/
@[simp]
theorem sylowLiftNormalizerEquivComap_coefficient
    (α : FactorSet G C) (hα : α.IsNormalized)
    (S : Sylow p G)
    (e : H ≃* Subgroup.normalizer (S : Set G))
    (x :
      Subgroup.normalizer
        ((centralExtension α hα).sylowLift S :
          Set (CentralExtensionGroup α hα))) :
    coefficient
        (sylowNormalizerFactorSet α S e)
        (sylowNormalizerFactorSet_isNormalized
          α hα S e)
        (sylowLiftNormalizerEquivComap
          α hα S e x) =
      coefficient α hα
        (x : CentralExtensionGroup α hα) :=
  rfl

/-- The equivalence sends the original coefficient embedding, viewed in the
Sylow-lift normalizer, to the coefficient embedding of the restricted
extension. -/
@[simp]
theorem sylowLiftNormalizerEquivComap_coefficientEmbedding
    (α : FactorSet G C) (hα : α.IsNormalized)
    (S : Sylow p G)
    (e : H ≃* Subgroup.normalizer (S : Set G))
    (c : C) :
    sylowLiftNormalizerEquivComap α hα S e
        (coefficientEmbeddingToSylowLiftNormalizer
          α hα S c) =
      coefficientEmbedding
        (sylowNormalizerFactorSet α S e)
        (sylowNormalizerFactorSet_isNormalized
          α hα S e) c := by
  apply ext
  · simp [sylowLiftNormalizerEquivComap,
      coefficientEmbeddingToSylowLiftNormalizer]
  · rfl

end CentralExtensionGroup
end FactorSet
end CharacterTriple
end McKayConjecture
