/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordEquivalence

/-!
# Conjugating constituents of a normal restriction

If `N` is normal in `G`, the restriction of a `G`-representation to `N`
contains one conjugate of an irreducible `N`-character exactly when it
contains every conjugate.  This file proves the direction needed for
exhaustivity in the Clifford correspondence by explicitly transporting a
nonzero constituent map.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CliffordEquivalence

open CliffordCorrespondence

variable {G : Type} [Finite G] [Group G]
variable (N : Subgroup G) [N.Normal]

/-- The chosen realization of a conjugated character is isomorphic to the
corresponding twist of the original chosen realization. -/
def conjugateCharacterRealizationIso
    (a : G) (θ : IrreducibleCharacter N) :
    (IrreducibleCharacter.conjBy N a θ).realization ≅
      conjugateRealization N a θ := by
  letI : Simple (conjugateRealization N a θ) :=
    FDRep.simple_res_mulEquiv
      (MulAut.conjNormal (H := N) a).symm
      θ.realization
  apply Classical.choice
  apply FDRep.nonempty_iso_of_character_eq
  rw [(IrreducibleCharacter.conjBy N a θ).realization_character,
    conjugateRealization_character]

/-- Undo ambient conjugation on a constituent map.  The source of `f` is a
realization of `θᵃ`; the resulting map has source a realization of `θ`. -/
def unconjugatedRestrictionHom
    (a : G) (θ : IrreducibleCharacter N)
    (V : FDRep ℂ G)
    (f : (IrreducibleCharacter.conjBy N a θ).realization ⟶
      FDRep.resSubgroup N V) :
    θ.realization ⟶ FDRep.resSubgroup N V := by
  let i := conjugateCharacterRealizationIso N a θ
  let fTwisted :
      conjugateRealization N a θ ⟶
        FDRep.resSubgroup N V :=
    i.inv ≫ f
  let fL :
      conjugateRealization N a θ →ₗ[ℂ]
        FDRep.resSubgroup N V :=
    ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).map
      fTwisted.hom).hom
  let e := restrictionCarrierLinearEquiv N V
  let L : θ.realization →ₗ[ℂ] FDRep.resSubgroup N V :=
    e.symm.toLinearMap.comp
      ((V.ρ a⁻¹).comp
        (e.toLinearMap.comp fL))
  refine
    { hom := FGModuleCat.ofHom L
      comm := ?_ }
  intro n
  apply FGModuleCat.hom_ext
  ext v
  let m : N := MulAut.conjNormal a n
  have hf :
      e (fL (θ.realization.ρ n v)) =
        V.ρ (m : G) (e (fL v)) := by
    have hcomm :=
      ConcreteCategory.congr_hom (fTwisted.comm m) v
    change
      fL
          ((conjugateRealization N a θ).ρ m v) =
        (FDRep.resSubgroup N V).ρ m (fL v) at hcomm
    have htwist :
        (conjugateRealization N a θ).ρ m v =
          θ.realization.ρ n v := by
      change
        θ.realization.ρ
            ((MulAut.conjNormal a).symm m) v =
          θ.realization.ρ n v
      rw [show (MulAut.conjNormal a).symm m = n by
        simp [m]]
    rw [htwist] at hcomm
    exact congrArg e hcomm
  change
    e.symm
        (V.ρ a⁻¹
          (e (fL (θ.realization.ρ n v)))) =
      V.ρ (n : G)
        (e.symm (V.ρ a⁻¹ (e (fL v))))
  rw [hf]
  apply e.symm.injective
  change
    V.ρ a⁻¹ (V.ρ (m : G) (e (fL v))) =
      V.ρ (n : G) (V.ρ a⁻¹ (e (fL v)))
  rw [← Module.End.mul_apply, ← Module.End.mul_apply,
    ← map_mul, ← map_mul]
  congr 1
  dsimp [m]
  group

@[simp]
theorem unconjugatedRestrictionHom_apply
    (a : G) (θ : IrreducibleCharacter N)
    (V : FDRep ℂ G)
    (f : (IrreducibleCharacter.conjBy N a θ).realization ⟶
      FDRep.resSubgroup N V)
    (v : θ.realization) :
    unconjugatedRestrictionHom N a θ V f v =
      (restrictionCarrierLinearEquiv N V).symm
        (V.ρ a⁻¹
          (restrictionCarrierLinearEquiv N V
            (((conjugateCharacterRealizationIso N a θ).inv ≫ f) v))) :=
  rfl

/-- Undoing conjugation preserves nonzeroness of a constituent map. -/
theorem unconjugatedRestrictionHom_ne_zero
    (a : G) (θ : IrreducibleCharacter N)
    (V : FDRep ℂ G)
    (f : (IrreducibleCharacter.conjBy N a θ).realization ⟶
      FDRep.resSubgroup N V)
    (hf : f ≠ 0) :
    unconjugatedRestrictionHom N a θ V f ≠ 0 := by
  let i := conjugateCharacterRealizationIso N a θ
  let fTwisted :
      conjugateRealization N a θ ⟶
        FDRep.resSubgroup N V :=
    i.inv ≫ f
  have hfTwisted : fTwisted ≠ 0 := by
    intro hzero
    apply hf
    have h :=
      congrArg (fun z ↦ i.hom ≫ z) hzero
    simpa [fTwisted, Category.assoc] using h
  let e := restrictionCarrierLinearEquiv N V
  intro hzero
  apply hfTwisted
  apply ConcreteCategory.hom_ext
  intro v
  have hv₀ :=
    ConcreteCategory.congr_hom hzero
      (show θ.realization from v)
  have hv₀' :
      unconjugatedRestrictionHom N a θ V f
          (show θ.realization from v) = 0 := by
    change
      unconjugatedRestrictionHom N a θ V f
          (show θ.realization from v) = 0 at hv₀
    exact hv₀
  rw [unconjugatedRestrictionHom_apply] at hv₀'
  have hv :
      e.symm
          (V.ρ a⁻¹
            (e (fTwisted v))) = 0 := by
    simpa [fTwisted, e, i] using hv₀'
  have hv' :
      V.ρ a⁻¹ (e (fTwisted v)) = 0 := by
    apply e.symm.injective
    simpa using hv
  have hv'' : e (fTwisted v) = 0 := by
    exact (Representation.apply_bijective V.ρ a⁻¹).1
      (by simpa using hv')
  apply e.injective
  change fTwisted v = 0
  exact hv''

/-- If an ambient irreducible character lies over a conjugate of `θ`, then
it lies over `θ` itself. -/
theorem liesOverAlong_of_conjugate
    (a : G) (θ : IrreducibleCharacter N)
    (χ : IrreducibleCharacter G)
    (hχ : LiesOverAlong N.subtype
      (IrreducibleCharacter.conjBy N a θ) χ) :
    LiesOverAlong N.subtype θ χ := by
  rw [liesOverAlong_iff_exists_nonzero] at hχ ⊢
  obtain ⟨f, hf⟩ := hχ
  exact
    ⟨unconjugatedRestrictionHom N a θ χ.realization f,
      unconjugatedRestrictionHom_ne_zero
        N a θ χ.realization f hf⟩

/-- Orbit-lie-over is equivalent to lie-over for the chosen orbit
representative. -/
theorem liesOverOrbit_iff_liesOver
    (θ : IrreducibleCharacter N)
    (χ : IrreducibleCharacter G) :
    LiesOverOrbit N θ χ ↔
      LiesOverAlong N.subtype θ χ := by
  constructor
  · rintro ⟨a, ha⟩
    exact liesOverAlong_of_conjugate N a θ χ ha
  · exact liesOverOrbit_of_liesOver N θ

end CliffordEquivalence
end McKayConjecture
