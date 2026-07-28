/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveRepresentation

/-!
# Restriction and transport of projective representations

A projective representation pulls back along a group homomorphism.  Its factor
set is obtained by precomposition in both variables.  This elementary
operation is used repeatedly in central character-triple comparisons.
-/

noncomputable section

universe u v w x

namespace McKayConjecture.CharacterTriple
namespace ProjectiveRepresentation

variable {K : Type u} {V : Type v} {G : Type w} {H : Type x}
variable [Field K] [AddCommGroup V] [Module K V] [Group G] [Group H]

/-- Pull a projective representation back along a group homomorphism. -/
def comap (f : H →* G) (P : ProjectiveRepresentation K G V) :
    ProjectiveRepresentation K H V where
  operator h := P.operator (f h)
  factor h₁ h₂ := P.factor (f h₁) (f h₂)
  map_mul h₁ h₂ := by
    simpa using P.map_mul (f h₁) (f h₂)

@[simp]
theorem comap_operator (f : H →* G)
    (P : ProjectiveRepresentation K G V) (h : H) :
    (P.comap f).operator h = P.operator (f h) :=
  rfl

@[simp]
theorem comap_factor (f : H →* G)
    (P : ProjectiveRepresentation K G V) (h₁ h₂ : H) :
    (P.comap f).factor h₁ h₂ = P.factor (f h₁) (f h₂) :=
  rfl

@[simp]
theorem comap_id (P : ProjectiveRepresentation K G V) :
    P.comap (MonoidHom.id G) = P := by
  ext <;> rfl

@[simp]
theorem comap_comp {L : Type*} [Group L] (f : H →* G) (g : L →* H)
    (P : ProjectiveRepresentation K G V) :
    (P.comap f).comap g = P.comap (f.comp g) := by
  ext <;> rfl

/-- Pullback commutes with passing to the bundled factor set. -/
theorem comap_factorSet [Nontrivial V] (f : H →* G)
    (P : ProjectiveRepresentation K G V) :
    (P.comap f).factorSet =
      { toFun := fun h₁ h₂ ↦ P.factorSet (f h₁) (f h₂)
        cocycle' := fun g h k ↦ by
          simpa using P.factorSet.cocycle (f g) (f h) (f k) } := by
  ext
  rfl

/-- A normalized projective representation remains normalized after
pullback. -/
theorem comap_isNormalized (f : H →* G)
    (P : ProjectiveRepresentation K G V) (hP : P.IsNormalized) :
    (P.comap f).IsNormalized := by
  simpa [IsNormalized] using hP

end ProjectiveRepresentation
end McKayConjecture.CharacterTriple
