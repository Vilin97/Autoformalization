/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Induction
import McKayConjecture.Character.Restriction

/-!
# Restriction of class functions

Precomposition with a group homomorphism sends class functions to class
functions.  This is the character-level restriction map corresponding to
`FDRep.res`.
-/

noncomputable section

namespace McKayConjecture
namespace ClassFunction

variable {G H L : Type}
variable [Group G] [Group H] [Group L]

/-- Pull a class function back along a group homomorphism. -/
def comapLinearMap (φ : H →* G) :
    ClassFunction G →ₗ[ℂ] ClassFunction H where
  toFun f :=
    ⟨fun h ↦ f (φ h), by
      intro h x
      simpa only [map_mul, map_inv] using
        ClassFunction.conj_apply f (φ h) (φ x)⟩
  map_add' f k := by
    ext h
    rfl
  map_smul' c f := by
    ext h
    rfl

@[simp]
theorem comapLinearMap_apply
    (φ : H →* G) (f : ClassFunction G) (h : H) :
    comapLinearMap φ f h = f (φ h) :=
  rfl

@[simp]
theorem comapLinearMap_id
    (f : ClassFunction G) :
    comapLinearMap (MonoidHom.id G) f = f := by
  ext g
  rfl

@[simp]
theorem comapLinearMap_comp
    (φ : H →* G) (ψ : L →* H)
    (f : ClassFunction G) :
    comapLinearMap ψ (comapLinearMap φ f) =
      comapLinearMap (φ.comp ψ) f := by
  ext l
  rfl

/-- Character restriction agrees with class-function pullback. -/
@[simp]
theorem characterClassFunction_res
    (φ : H →* G) (V : FDRep ℂ G) :
    FDRep.characterClassFunction (FDRep.res φ V) =
      comapLinearMap φ (FDRep.characterClassFunction V) := by
  ext h
  rfl

end ClassFunction
end McKayConjecture
