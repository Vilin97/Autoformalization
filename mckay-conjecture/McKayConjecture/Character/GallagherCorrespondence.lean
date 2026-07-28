/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Gallagher
import McKayConjecture.Character.Tensor
import McKayConjecture.CharacterTriple.MultiplicityReconstruction
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# The full Gallagher correspondence

Let `H ⫳ K`, let `χ ∈ Irr(H)`, and let `ψ ∈ Irr(K)` extend `χ`.
Gallagher's theorem identifies the irreducible characters of `K/H` with
the irreducible characters of `K` lying over `χ`, by tensoring `ψ` with
an inflated quotient representation.

This file packages an extension as an associated (ordinary, hence
factor-one) projective representation.  The multiplicity-space construction
then supplies the inverse quotient representation and the evaluation
intertwiner.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Corollary 6.17.
* P. X. Gallagher, *Group characters and normal Hall subgroups*,
  Nagoya Math. J. 21 (1962), 223–230.
-/

noncomputable section

open CategoryTheory Limits
open scoped MonoidalCategory TensorProduct

universe u v

namespace McKayConjecture

namespace CharacterTriple
namespace ProjectiveRepresentation

variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- A factor-one projective representation is an ordinary linear action.

This converse to `ofLinearAction` is useful when the projective
representation arose indirectly, so its factor-one property is a theorem
rather than definitional. -/
def linearActionOfFactorOne
    (P : ProjectiveRepresentation ℂ G V)
    (hfactor : ∀ g h, P.factor g h = 1) :
    G →* (V ≃ₗ[ℂ] V) where
  toFun := P.operator
  map_one' := by
    have h := P.map_mul 1 1
    simp only [hfactor, map_one, one_mul] at h
    apply mul_left_cancel (a := P.operator 1)
    simpa using h
  map_mul' g h := by
    have hmul := P.map_mul g h
    simpa only [hfactor, map_one, one_mul] using hmul.symm

@[simp]
theorem linearActionOfFactorOne_apply
    (P : ProjectiveRepresentation ℂ G V)
    (hfactor : ∀ g h, P.factor g h = 1) (g : G) :
    P.linearActionOfFactorOne hfactor g = P.operator g :=
  rfl

end ProjectiveRepresentation
end CharacterTriple

namespace IrreducibleCharacter

open CharacterTriple

variable {K : Type u} [Finite K] [Group K]
variable {H : Subgroup K} [hH : H.Normal]
variable {χ : IrreducibleCharacter H}
variable {ψ : IrreducibleCharacter K}

local instance realizationNontrivial :
    Nontrivial ψ.realization :=
  CliffordRestriction.nontrivial_of_simple ψ.realization

/-! ### An extension as associated projective data -/

/-- The character triple determined by an extendible irreducible
normal-subgroup character. -/
def extensionCharacterTriple
    (hψ : IsExtensionAlong H.subtype χ ψ) :
    CharacterTriple K where
  normalSubgroup := H
  isNormal := hH
  character := χ
  isInvariant g h := by
    calc
      χ.values
          (conjugateNormalElement H hH g h) =
          ψ.values
            ((conjugateNormalElement H hH g h : H) : K) :=
        (hψ (conjugateNormalElement H hH g h)).symm
      _ = ψ.values (h : K) := by
        simpa [conjugateNormalElement] using
          (ClassFunction.conj_apply ψ.toClassFunction
            (h : K) g)
      _ = χ.values h := hψ h

/-- The chosen realization of `ψ`, regarded as an action by linear
automorphisms. -/
def extensionRealizationAction :
    K →* (ψ.realization ≃ₗ[ℂ] ψ.realization) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv
      ℂ ψ.realization).toMonoidHom.comp
    ψ.realization.ρ.toHomUnits

omit [Finite K] in
@[simp]
theorem extensionRealizationAction_toLinearMap (g : K) :
    (extensionRealizationAction (ψ := ψ) g :
      ψ.realization →ₗ[ℂ] ψ.realization) =
        ψ.realization.ρ g :=
  rfl

/-- The extension realization as a factor-one projective representation. -/
def extensionProjectiveRepresentation :
    ProjectiveRepresentation ℂ K ψ.realization :=
  ProjectiveRepresentation.ofLinearAction
    (extensionRealizationAction (ψ := ψ))

omit [Finite K] in
@[simp]
theorem extensionProjectiveRepresentation_operator (g : K) :
    (extensionProjectiveRepresentation (ψ := ψ)).operator g =
      extensionRealizationAction (ψ := ψ) g :=
  rfl

omit [Finite K] in
@[simp]
theorem extensionProjectiveRepresentation_factor (g k : K) :
    (extensionProjectiveRepresentation (ψ := ψ)).factor g k = 1 :=
  rfl

/-- The factor-one projective representation afforded by an extension is
associated with the corresponding character triple. -/
def extensionAssociatedProjectiveRepresentation
    (hψ : IsExtensionAlong H.subtype χ ψ) :
    AssociatedProjectiveRepresentation
      (extensionCharacterTriple hψ)
      ψ.realization
      (extensionProjectiveRepresentation (ψ := ψ)) := by
  let ρχ : Representation ℂ H χ.realization :=
    χ.realization.ρ
  let res : Representation ℂ H ψ.realization :=
    ψ.realization.ρ.comp H.subtype
  letI : Representation.IsIrreducible ρχ :=
    CliffordRestriction.isIrreducible_of_simple χ.realization
  have hchar : res.character = ρχ.character := by
    funext h
    calc
      res.character h =
          ψ.realization.character (h : K) := rfl
      _ = ψ.values (h : K) :=
        congrFun ψ.realization_character (h : K)
      _ = χ.values h := hψ h
      _ = χ.realization.character h :=
        (congrFun χ.realization_character h).symm
      _ = ρχ.character h := rfl
  let Phi :=
    Classical.choice
      (Representation.nonempty_equiv_of_character_eq_irreducible
        ρχ res hchar)
  letI : Representation.IsIrreducible res :=
    Representation.IsIrreducible.of_equiv Phi
  refine
    { restriction :=
        (extensionRealizationAction (ψ := ψ)).comp H.subtype
      restriction_apply := fun _ ↦ rfl
      restriction_simple := ?_
      restriction_character := ?_
      normal_mul := ?_
      mul_normal := ?_ }
  · change Simple (FDRep.of res)
    exact RepresentationTheory.simple_fdRep_of_isIrreducible res
  · funext h
    change ψ.realization.character (h : K) = χ.values h
    rw [ψ.realization_character]
    exact hψ h
  · intro h g
    exact
      map_mul
        (extensionRealizationAction (ψ := ψ))
        (h : K) g
  · intro g h
    exact
      map_mul
        (extensionRealizationAction (ψ := ψ))
        g (h : K)

/-! ### The quotient action on the multiplicity space -/

variable {W : Type}
variable [AddCommGroup W] [Module ℂ W]

/-- The multiplicity space of the chosen extension inside an ambient
representation. -/
abbrev extensionMultiplicitySpace
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (D : Representation ℂ K W) :=
  MultiplicityProjective.Space
    (extensionAssociatedProjectiveRepresentation hψ) D

/-- The ordinary ambient action on the multiplicity space.  Its projective
factor is one because the chosen extension is an ordinary representation. -/
def extensionMultiplicityAction
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (D : Representation ℂ K W) :
    K →* (extensionMultiplicitySpace hψ D ≃ₗ[ℂ]
      extensionMultiplicitySpace hψ D) :=
  (MultiplicityProjective.projective
      (extensionAssociatedProjectiveRepresentation hψ) D).linearActionOfFactorOne
    (by
      intro g k
      rw [MultiplicityProjective.projective_factor]
      simp)

@[simp]
theorem extensionMultiplicityAction_apply
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (D : Representation ℂ K W) (g : K) :
    extensionMultiplicityAction hψ D g =
      MultiplicityProjective.operator
        (extensionAssociatedProjectiveRepresentation hψ) D g :=
  rfl

/-- The multiplicity action is trivial on the normal subgroup. -/
@[simp]
theorem extensionMultiplicityAction_normal
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (D : Representation ℂ K W) (h : H) :
    extensionMultiplicityAction hψ D (h : K) = 1 := by
  let R := extensionAssociatedProjectiveRepresentation hψ
  change
    MultiplicityProjective.operator
        R D (h : K) =
      1
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro f
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change
    D (h : K)
        (f (((extensionProjectiveRepresentation (ψ := ψ)).operator
          (h : K)).symm v)) =
      f v
  have hf :=
    LinearMap.ext_iff.mp (f.isIntertwining' h)
      (((extensionProjectiveRepresentation (ψ := ψ)).operator
        (h : K)).symm v)
  change
    f (R.restriction h
        (((extensionProjectiveRepresentation (ψ := ψ)).operator
          (h : K)).symm v)) =
      D (h : K)
        (f (((extensionProjectiveRepresentation (ψ := ψ)).operator
          (h : K)).symm v)) at hf
  rw [← hf]
  change
    f ((extensionProjectiveRepresentation (ψ := ψ)).operator
        (h : K)
        (((extensionProjectiveRepresentation (ψ := ψ)).operator
          (h : K)).symm v)) =
      f v
  rw [LinearEquiv.apply_symm_apply]

/-- Descent of the multiplicity-space action from `K` to `K/H`. -/
def extensionMultiplicityQuotientAction
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (D : Representation ℂ K W) :
    K ⧸ H →* (extensionMultiplicitySpace hψ D ≃ₗ[ℂ]
      extensionMultiplicitySpace hψ D) :=
  QuotientGroup.lift H (extensionMultiplicityAction hψ D) (by
    intro g hg
    rw [MonoidHom.mem_ker]
    exact extensionMultiplicityAction_normal hψ D ⟨g, hg⟩)

@[simp]
theorem extensionMultiplicityQuotientAction_mk
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (D : Representation ℂ K W) (g : K) :
    extensionMultiplicityQuotientAction hψ D
        (QuotientGroup.mk' H g) =
      extensionMultiplicityAction hψ D g :=
  rfl

/-- The quotient representation carried by the multiplicity space. -/
abbrev extensionMultiplicityQuotientRepresentation
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (D : Representation ℂ K W) :
    Representation ℂ (K ⧸ H) (extensionMultiplicitySpace hψ D) :=
  linearRepresentationOfAction
    (extensionMultiplicityQuotientAction hψ D)

/-- Finite-dimensional packaging of the quotient multiplicity
representation. -/
abbrev extensionMultiplicityQuotientFDRep
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (D : FDRep ℂ K) :
    FDRep ℂ (K ⧸ H) :=
  FDRep.of
    (extensionMultiplicityQuotientRepresentation hψ D.ρ)

/-- In the factor-one extension case, the projective tensor reconstruction
action is definitionally the ordinary extension tensored with the inflated
quotient multiplicity action. -/
def extensionMultiplicityTensorEquiv
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (D : FDRep ℂ K) :
    Representation.Equiv
      (extensionTensorFDRep H ψ
        (extensionMultiplicityQuotientFDRep hψ D)).ρ
      (MultiplicityProjective.tensorRepresentation
        (extensionAssociatedProjectiveRepresentation hψ) D.ρ) := by
  apply Representation.Equiv.mk
    (LinearEquiv.refl ℂ
      (ψ.realization ⊗[ℂ]
        extensionMultiplicitySpace hψ D.ρ))
  intro g
  apply LinearMap.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro v f
    rfl
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-! ### Multiplicity of a tensor-inflated representation -/

/-- Tensoring the extension with a quotient irreducible of degree `n`
produces exactly `n` copies of the normal character upon restriction.  Thus
its multiplicity space has dimension `n`. -/
theorem extensionMultiplicitySpace_tensor_finrank
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    Module.finrank ℂ
        (extensionMultiplicitySpace hψ
          (extensionTensorFDRep H ψ beta.realization).ρ) =
      beta.degree := by
  let R := extensionAssociatedProjectiveRepresentation hψ
  let rho : Representation ℂ H ψ.realization :=
    R.fdRestriction.ρ
  let sigma : Representation ℂ H
      (extensionTensorFDRep H ψ beta.realization) :=
    (extensionTensorFDRep H ψ beta.realization).ρ.comp H.subtype
  letI : Fintype H := Fintype.ofFinite H
  letI : Simple R.fdRestriction :=
    R.restriction_simple
  letI : Representation.IsIrreducible rho :=
    CliffordRestriction.isIrreducible_of_simple R.fdRestriction
  letI : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hsigma :
      sigma.character =
        (beta.degree : ℂ) • rho.character := by
    funext h
    change
      (FDRep.res H.subtype
          (extensionTensorFDRep H ψ beta.realization)).character h =
        (beta.degree : ℂ) * R.fdRestriction.character h
    rw [extensionTensorFDRep_restrict_character hψ beta,
      R.fdRestriction_character]
    rfl
  have hself :=
    Representation.card_inv_mul_sum_char_mul_char_eq_finrank rho rho
  have hcross :=
    Representation.card_inv_mul_sum_char_mul_char_eq_finrank rho sigma
  have hend :
      Module.finrank ℂ (rho.IntertwiningMap rho) = 1 :=
    Representation.IsIrreducible.finrank_intertwiningMap_self rho
  rw [hsigma] at hcross
  simp only [Pi.smul_apply, smul_eq_mul] at hcross
  have hscaled :
      (↑(Nat.card H) : ℂ)⁻¹ *
          ∑ h : H,
            ((beta.degree : ℂ) * rho.character h) *
              rho.character h⁻¹ =
        (beta.degree : ℂ) *
          ((↑(Nat.card H) : ℂ)⁻¹ *
            ∑ h : H,
              rho.character h * rho.character h⁻¹) := by
    calc
      _ = (↑(Nat.card H) : ℂ)⁻¹ *
          ((beta.degree : ℂ) *
            ∑ h : H,
              rho.character h * rho.character h⁻¹) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        ring
      _ = _ := by ring
  change
    Module.finrank ℂ (rho.IntertwiningMap sigma) =
      beta.degree
  have hfin :
      (Module.finrank ℂ (rho.IntertwiningMap sigma) : ℂ) =
        (beta.degree : ℂ) := by
    rw [← hcross, hscaled, hself, hend]
    norm_num
  exact_mod_cast hfin

/-! ### The tensor unit in the multiplicity space -/

/-- A quotient vector `w` gives the normal-subgroup intertwiner
`v ↦ v ⊗ w`. -/
def extensionTensorMultiplicityUnitMap
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H))
    (w : beta.realization) :
    extensionMultiplicitySpace hψ
      (extensionTensorFDRep H ψ beta.realization).ρ where
  toLinearMap :=
    { toFun := fun v ↦ v ⊗ₜ[ℂ] w
      map_add' := fun v v' ↦
        TensorProduct.add_tmul v v' w
      map_smul' := fun c v ↦
        TensorProduct.smul_tmul' c v w }
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    let R := extensionAssociatedProjectiveRepresentation hψ
    have hquot :
        QuotientGroup.mk' H (h : K) = 1 :=
      (QuotientGroup.eq_one_iff (h : K)).2 h.property
    change
      R.restriction h v ⊗ₜ[ℂ] w =
        (extensionTensorFDRep H ψ beta.realization).ρ
          (h : K) (v ⊗ₜ[ℂ] w)
    change
      R.restriction h v ⊗ₜ[ℂ] w =
        TensorProduct.map
          (ψ.realization.ρ (h : K))
          (beta.realization.ρ
            (QuotientGroup.mk' H (h : K)))
          (v ⊗ₜ[ℂ] w)
    rw [TensorProduct.map_tmul, hquot, map_one,
      R.restriction_apply]
    rfl

@[simp]
theorem extensionTensorMultiplicityUnitMap_apply
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H))
    (w : beta.realization) (v : ψ.realization) :
    extensionTensorMultiplicityUnitMap hψ beta w v =
      v ⊗ₜ[ℂ] w :=
  rfl

/-- The tensor-unit construction is linear in the quotient vector. -/
def extensionTensorMultiplicityUnitLinearMap
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    beta.realization →ₗ[ℂ]
      extensionMultiplicitySpace hψ
        (extensionTensorFDRep H ψ beta.realization).ρ where
  toFun := extensionTensorMultiplicityUnitMap hψ beta
  map_add' w w' := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change
      v ⊗ₜ[ℂ] (w + w') =
        v ⊗ₜ[ℂ] w + v ⊗ₜ[ℂ] w'
    exact TensorProduct.tmul_add v w w'
  map_smul' c w := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change
      v ⊗ₜ[ℂ] (c • w) =
        c • (v ⊗ₜ[ℂ] w)
    exact TensorProduct.tmul_smul c v w

@[simp]
theorem extensionTensorMultiplicityUnitLinearMap_apply
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H))
    (w : beta.realization) (v : ψ.realization) :
    extensionTensorMultiplicityUnitLinearMap hψ beta w v =
      v ⊗ₜ[ℂ] w :=
  rfl

/-- The tensor-unit map is equivariant for the quotient multiplicity
action. -/
def extensionTensorMultiplicityUnit
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    Representation.IntertwiningMap beta.realization.ρ
      (extensionMultiplicityQuotientRepresentation hψ
        (extensionTensorFDRep H ψ beta.realization).ρ) where
  toLinearMap :=
    extensionTensorMultiplicityUnitLinearMap hψ beta
  isIntertwining' q := by
    obtain ⟨g, rfl⟩ :=
      QuotientGroup.mk'_surjective H q
    apply LinearMap.ext
    intro w
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change
      extensionTensorMultiplicityUnitMap hψ beta
          (beta.realization.ρ (QuotientGroup.mk' H g) w) v =
        MultiplicityProjective.operator
          (extensionAssociatedProjectiveRepresentation hψ)
          (extensionTensorFDRep H ψ beta.realization).ρ g
          (extensionTensorMultiplicityUnitMap hψ beta w) v
    rw [MultiplicityProjective.operator_apply,
      extensionTensorMultiplicityUnitMap_apply,
      extensionTensorMultiplicityUnitMap_apply]
    change
      v ⊗ₜ[ℂ]
          (beta.realization.ρ (QuotientGroup.mk' H g) w) =
        TensorProduct.map
          (ψ.realization.ρ g)
          (beta.realization.ρ (QuotientGroup.mk' H g))
          (((extensionProjectiveRepresentation (ψ := ψ)).operator g).symm v
            ⊗ₜ[ℂ] w)
    rw [TensorProduct.map_tmul]
    change
      v ⊗ₜ[ℂ]
          (beta.realization.ρ (QuotientGroup.mk' H g) w) =
        (extensionProjectiveRepresentation (ψ := ψ)).operator g
            (((extensionProjectiveRepresentation (ψ := ψ)).operator g).symm v)
          ⊗ₜ[ℂ]
          (beta.realization.ρ (QuotientGroup.mk' H g) w)
    rw [LinearEquiv.apply_symm_apply]

@[simp]
theorem extensionTensorMultiplicityUnit_apply
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H))
    (w : beta.realization) (v : ψ.realization) :
    extensionTensorMultiplicityUnit hψ beta w v =
      v ⊗ₜ[ℂ] w :=
  rfl

/-- The tensor-unit map is injective: evaluate a pure tensor against a
linear functional taking a chosen nonzero extension vector to one. -/
theorem extensionTensorMultiplicityUnit_injective
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    Function.Injective
      (extensionTensorMultiplicityUnit hψ beta) := by
  intro w w' hww'
  obtain ⟨v : ψ.realization, hv⟩ :=
    exists_ne (0 : ψ.realization)
  obtain ⟨ell, hell⟩ :=
    Module.Projective.exists_dual_eq_one ℂ hv
  have hpure :
      v ⊗ₜ[ℂ] w = v ⊗ₜ[ℂ] w' := by
    have happ :=
      congrArg
        (fun f :
          extensionMultiplicitySpace hψ
            (extensionTensorFDRep H ψ beta.realization).ρ ↦
          f v) hww'
    exact happ
  have htensor :
      v ⊗ₜ[ℂ] (w - w') = 0 := by
    rw [TensorProduct.tmul_sub, hpure, sub_self]
  have heval :=
    congrArg
      (fun x : ψ.realization ⊗[ℂ] beta.realization ↦
        (TensorProduct.lid ℂ beta.realization)
          (TensorProduct.map ell
            (LinearMap.id :
              beta.realization →ₗ[ℂ] beta.realization) x))
      htensor
  have hzero : w - w' = 0 := by
    simpa [TensorProduct.map_tmul, hell] using heval
  exact sub_eq_zero.mp hzero

/-- Linear equivalence between a quotient irreducible and the multiplicity
space of its tensor-inflation. -/
def extensionTensorMultiplicityLinearEquiv
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    beta.realization ≃ₗ[ℂ]
      extensionMultiplicitySpace hψ
        (extensionTensorFDRep H ψ beta.realization).ρ := by
  let f :=
    (extensionTensorMultiplicityUnit hψ beta).toLinearMap
  have hinj : Function.Injective f :=
    extensionTensorMultiplicityUnit_injective hψ beta
  have hfin :
      Module.finrank ℂ beta.realization =
        Module.finrank ℂ
          (extensionMultiplicitySpace hψ
            (extensionTensorFDRep H ψ beta.realization).ρ) := by
    rw [beta.realization_finrank,
      extensionMultiplicitySpace_tensor_finrank hψ beta]
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hfin).mp hinj
  exact LinearEquiv.ofBijective f ⟨hinj, hsurj⟩

/-- Equivariant form of `extensionTensorMultiplicityLinearEquiv`. -/
def extensionTensorMultiplicityEquiv
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    Representation.Equiv beta.realization.ρ
      (extensionMultiplicityQuotientRepresentation hψ
        (extensionTensorFDRep H ψ beta.realization).ρ) :=
  Representation.Equiv.mk
    (extensionTensorMultiplicityLinearEquiv hψ beta)
    (extensionTensorMultiplicityUnit hψ beta).isIntertwining'

/-- Postcomposition with a representation equivalence identifies
intertwining spaces with equivalent codomains. -/
def intertwiningMapCongrRight
    {L : Type u} [Monoid L]
    {X Y Z : Type}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {rho : Representation ℂ L X}
    {sigma : Representation ℂ L Y}
    {tau : Representation ℂ L Z}
    (e : Representation.Equiv sigma tau) :
    Representation.IntertwiningMap rho sigma ≃ₗ[ℂ]
      Representation.IntertwiningMap rho tau where
  toFun f := e.toIntertwiningMap.comp f
  invFun f := e.symm.toIntertwiningMap.comp f
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply (f x)
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact e.apply_symm_apply (f x)
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact e.map_add (f x) (g x)
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact e.map_smul c (f x)

/-- Conjugation by a representation equivalence identifies the two
endomorphism spaces. -/
def intertwiningMapEndCongr
    {L : Type u} [Monoid L]
    {X Y : Type}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {rho : Representation ℂ L X}
    {sigma : Representation ℂ L Y}
    (e : Representation.Equiv rho sigma) :
    Representation.IntertwiningMap rho rho ≃ₗ[ℂ]
      Representation.IntertwiningMap sigma sigma where
  toFun f :=
    e.toIntertwiningMap.comp
      (f.comp e.symm.toIntertwiningMap)
  invFun f :=
    e.symm.toIntertwiningMap.comp
      (f.comp e.toIntertwiningMap)
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    simp
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    simp
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact e.map_add (f (e.symm x)) (g (e.symm x))
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact e.map_smul c (f (e.symm x))

/-! ### Endomorphism cancellation and irreducibility -/

variable {U : Type}
variable [AddCommGroup U] [Module ℂ U]

/-- An ambient intertwiner acts on extension multiplicity spaces by
postcomposition.  This operation is equivariant for the descended quotient
actions. -/
def extensionMultiplicityPostcompose
    (hψ : IsExtensionAlong H.subtype χ ψ)
    {D : Representation ℂ K W}
    {E : Representation ℂ K U}
    (A : Representation.IntertwiningMap D E) :
    Representation.IntertwiningMap
      (extensionMultiplicityQuotientRepresentation hψ D)
      (extensionMultiplicityQuotientRepresentation hψ E) where
  toLinearMap :=
    { toFun := fun f ↦
        { toLinearMap := A.toLinearMap.comp f.toLinearMap
          isIntertwining' := fun h ↦ by
            apply LinearMap.ext
            intro v
            have hf :=
              LinearMap.ext_iff.mp
                (f.isIntertwining' h) v
            have hA :=
              LinearMap.ext_iff.mp
                (A.isIntertwining' (h : K)) (f v)
            exact (congrArg A hf).trans hA }
      map_add' := fun f f' ↦ by
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro v
        exact A.map_add (f v) (f' v)
      map_smul' := fun c f ↦ by
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro v
        exact A.map_smul c (f v) }
  isIntertwining' q := by
    obtain ⟨g, rfl⟩ :=
      QuotientGroup.mk'_surjective H q
    apply LinearMap.ext
    intro f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change
      A
          (D g
            (f
              (((extensionProjectiveRepresentation (ψ := ψ)).operator
                g).symm v))) =
        E g
          (A
            (f
              (((extensionProjectiveRepresentation (ψ := ψ)).operator
                g).symm v)))
    exact A.isIntertwining D E g _

@[simp]
theorem extensionMultiplicityPostcompose_apply
    (hψ : IsExtensionAlong H.subtype χ ψ)
    {D : Representation ℂ K W}
    {E : Representation ℂ K U}
    (A : Representation.IntertwiningMap D E)
    (f : extensionMultiplicitySpace hψ D) (v : ψ.realization) :
    extensionMultiplicityPostcompose hψ A f v =
      A (f v) :=
  rfl

/-- Postcomposition by an ambient representation equivalence is a linear
equivalence of multiplicity spaces. -/
def extensionMultiplicityPostcomposeLinearEquiv
    (hψ : IsExtensionAlong H.subtype χ ψ)
    {D : Representation ℂ K W}
    {E : Representation ℂ K U}
    (A : Representation.Equiv D E) :
    extensionMultiplicitySpace hψ D ≃ₗ[ℂ]
      extensionMultiplicitySpace hψ E where
  toFun := extensionMultiplicityPostcompose hψ A.toIntertwiningMap
  invFun :=
    extensionMultiplicityPostcompose hψ A.symm.toIntertwiningMap
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    exact A.symm_apply_apply (f v)
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    exact A.apply_symm_apply (f v)
  map_add' f g :=
    (extensionMultiplicityPostcompose hψ
      A.toIntertwiningMap).map_add f g
  map_smul' c f :=
    (extensionMultiplicityPostcompose hψ
      A.toIntertwiningMap).map_smul c f

/-- Equivariant form of
`extensionMultiplicityPostcomposeLinearEquiv`. -/
def extensionMultiplicityPostcomposeEquiv
    (hψ : IsExtensionAlong H.subtype χ ψ)
    {D : Representation ℂ K W}
    {E : Representation ℂ K U}
    (A : Representation.Equiv D E) :
    Representation.Equiv
      (extensionMultiplicityQuotientRepresentation hψ D)
      (extensionMultiplicityQuotientRepresentation hψ E) :=
  Representation.Equiv.mk
    (extensionMultiplicityPostcomposeLinearEquiv hψ A)
    (extensionMultiplicityPostcompose hψ
      A.toIntertwiningMap).isIntertwining'

/-- Currying an endomorphism of the tensor-inflated representation gives a
quotient intertwiner into its multiplicity representation. -/
def extensionTensorEndCurryLinearMap
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    Representation.IntertwiningMap
        (extensionTensorFDRep H ψ beta.realization).ρ
        (extensionTensorFDRep H ψ beta.realization).ρ →ₗ[ℂ]
      Representation.IntertwiningMap beta.realization.ρ
        (extensionMultiplicityQuotientRepresentation hψ
          (extensionTensorFDRep H ψ beta.realization).ρ) where
  toFun A :=
    (extensionMultiplicityPostcompose hψ A).comp
      (extensionTensorMultiplicityUnit hψ beta)
  map_add' A B := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change
      (A + B) (v ⊗ₜ[ℂ] w) =
        A (v ⊗ₜ[ℂ] w) + B (v ⊗ₜ[ℂ] w)
    rfl
  map_smul' c A := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change
      (c • A) (v ⊗ₜ[ℂ] w) =
        c • A (v ⊗ₜ[ℂ] w)
    rfl

@[simp]
theorem extensionTensorEndCurryLinearMap_apply
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H))
    (A : Representation.IntertwiningMap
      (extensionTensorFDRep H ψ beta.realization).ρ
      (extensionTensorFDRep H ψ beta.realization).ρ)
    (w : beta.realization) (v : ψ.realization) :
    extensionTensorEndCurryLinearMap hψ beta A w v =
      A (v ⊗ₜ[ℂ] w) :=
  rfl

/-- Currying is faithful because pure tensors span the tensor product. -/
theorem extensionTensorEndCurryLinearMap_injective
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    Function.Injective
      (extensionTensorEndCurryLinearMap hψ beta) := by
  intro A B hAB
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro v w
    have happ :=
      congrArg
        (fun F : Representation.IntertwiningMap beta.realization.ρ
          (extensionMultiplicityQuotientRepresentation hψ
            (extensionTensorFDRep H ψ beta.realization).ρ) ↦
          F w v) hAB
    exact happ
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The endomorphism space of a tensor-inflated quotient irreducible has
dimension one. -/
theorem extensionTensor_end_finrank
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    Module.finrank ℂ
        (Representation.IntertwiningMap
          (extensionTensorFDRep H ψ beta.realization).ρ
          (extensionTensorFDRep H ψ beta.realization).ρ) =
      1 := by
  let D := extensionTensorFDRep H ψ beta.realization
  let M :=
    extensionMultiplicityQuotientRepresentation hψ D.ρ
  letI : Representation.IsIrreducible beta.realization.ρ :=
    CliffordRestriction.isIrreducible_of_simple beta.realization
  have htarget :
      Module.finrank ℂ
          (Representation.IntertwiningMap beta.realization.ρ M) =
        1 := by
    calc
      Module.finrank ℂ
          (Representation.IntertwiningMap beta.realization.ρ M) =
          Module.finrank ℂ
            (Representation.IntertwiningMap beta.realization.ρ
              beta.realization.ρ) :=
        (intertwiningMapCongrRight
          (extensionTensorMultiplicityEquiv hψ beta).symm).finrank_eq
      _ = 1 :=
        Representation.IsIrreducible.finrank_intertwiningMap_self
          beta.realization.ρ
  have hle :
      Module.finrank ℂ
          (Representation.IntertwiningMap D.ρ D.ρ) ≤ 1 := by
    have h :=
      LinearMap.finrank_le_finrank_of_injective
        (extensionTensorEndCurryLinearMap_injective hψ beta)
    simpa [D, M, htarget] using h
  have hDpos : 0 < Module.finrank ℂ D := by
    rw [show D = extensionTensorFDRep H ψ beta.realization from rfl,
      extensionTensorFDRep_finrank,
      beta.realization_finrank]
    exact Nat.mul_pos ψ.degree_pos beta.degree_pos
  letI : Nontrivial D :=
    Module.nontrivial_of_finrank_pos hDpos
  have hid :
      Representation.IntertwiningMap.id D.ρ ≠ 0 := by
    intro heq
    obtain ⟨x : D, hx⟩ := exists_ne (0 : D)
    have happ :=
      congrArg
        (fun f : Representation.IntertwiningMap D.ρ D.ρ ↦
          f x) heq
    apply hx
    simpa using happ
  have hpos :
      0 < Module.finrank ℂ
        (Representation.IntertwiningMap D.ρ D.ρ) :=
    (Module.finrank_pos_iff_exists_ne_zero).2
      ⟨Representation.IntertwiningMap.id D.ρ, hid⟩
  change
    Module.finrank ℂ
        (Representation.IntertwiningMap D.ρ D.ρ) =
      1
  omega

/-- Universe-polymorphic endomorphism criterion for a finite-group
representation over `ℂ`.  This is the converse half of Schur's lemma,
using Maschke semisimplicity. -/
theorem fdRep_simple_of_end_finrank_eq_one
    {L : Type u} [Finite L] [Group L]
    (V : FDRep ℂ L)
    (h : Module.finrank ℂ (V ⟶ V) = 1) :
    Simple V := by
  letI : NeZero (Nat.card L : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  letI repInjective (X : Rep ℂ L) :
      CategoryTheory.Injective X := by
    rw [← Rep.equivalenceModuleMonoidAlgebra.map_injective_iff,
      ← Module.injective_iff_injective_object]
    exact Module.injective_of_isSemisimpleRing _ _
  letI fdRepInjective (X : FDRep ℂ L) :
      CategoryTheory.Injective X :=
    (forget₂ (FDRep ℂ L) (Rep ℂ L)).injective_of_map_injective
      inferInstance
  refine
    { mono_isIso_iff_nonzero := fun {W} f _ ↦
        ⟨fun hf habs ↦ ?_, fun hf ↦ ?_⟩ }
  · rw [habs, isIsoZero_iff_source_target_isZero] at hf
    obtain ⟨g, hg⟩ : ∃ g : V ⟶ V, g ≠ 0 :=
      (Module.finrank_pos_iff_exists_ne_zero).mp (by
        rw [h]
        norm_num)
    exact hg (hf.2.eq_zero_of_src g)
  · suffices Epi f by
      exact isIso_of_mono_of_epi f
    suffices Epi (Abelian.image.ι f) by
      rw [← Abelian.image.fac f]
      exact epi_comp _ _
    rw [← Abelian.image.fac f] at hf
    set i := Abelian.image.ι f
    set phi := CategoryTheory.Injective.factorThru (𝟙 _) i
    have hphi_i : phi ≫ i ≠ 0 := by
      intro habs
      have hi_phi : 𝟙 _ = i ≫ phi :=
        (CategoryTheory.Injective.comp_factorThru (𝟙 _) i).symm
      apply_fun (· ≫ i) at hi_phi
      simp_all
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c • _ = 𝟙 V :=
      (finrank_eq_one_iff_of_nonzero' _ hphi_i).mp h (𝟙 V)
    refine Preadditive.epi_of_cancel_zero _ (fun g hg ↦ ?_)
    apply_fun (· ≫ g) at hc
    simpa [hg] using hc.symm

/-- Simplicity is transported along an equivalence of the underlying
unbundled representations. -/
theorem fdRep_simple_of_representation_equiv
    {L : Type u} [Finite L] [Group L]
    (V W : FDRep ℂ L) [Simple W]
    (e : Representation.Equiv V.ρ W.ρ) :
    Simple V := by
  letI : Representation.IsIrreducible W.ρ :=
    CliffordRestriction.isIrreducible_of_simple W
  have hIntertwining :
      Module.finrank ℂ
          (Representation.IntertwiningMap V.ρ V.ρ) =
        1 := by
    calc
      _ = Module.finrank ℂ
          (Representation.IntertwiningMap W.ρ W.ρ) :=
        (intertwiningMapEndCongr e).finrank_eq
      _ = 1 :=
        Representation.IsIrreducible.finrank_intertwiningMap_self
          W.ρ
  let homEquiv :
      (V ⟶ V) ≃ₗ[ℂ]
        Representation.IntertwiningMap V.ρ V.ρ :=
    (FDRep.forget₂HomLinearEquiv V V).symm |>.trans
      (Rep.homLinearEquiv _ _)
  apply fdRep_simple_of_end_finrank_eq_one V
  calc
    Module.finrank ℂ (V ⟶ V) =
        Module.finrank ℂ
          (Representation.IntertwiningMap V.ρ V.ρ) :=
      homEquiv.finrank_eq
    _ = 1 := hIntertwining

/-- Inflation carries quotient intertwiners to ambient intertwiners. -/
def inflateIntertwiningMap
    {V₁ V₂ : FDRep ℂ (K ⧸ H)}
    (f : Representation.IntertwiningMap V₁.ρ V₂.ρ) :
    Representation.IntertwiningMap
      (inflateFDRep H V₁).ρ
      (inflateFDRep H V₂).ρ where
  toLinearMap := f.toLinearMap
  isIntertwining' g :=
    f.isIntertwining'
      (QuotientGroup.mk' H g)

/-- Tensoring a quotient endomorphism with the identity of the extension
gives an ambient endomorphism. -/
def extensionTensorQuotientEndLinearMap
    (Wq : FDRep ℂ (K ⧸ H)) :
    Representation.IntertwiningMap Wq.ρ Wq.ρ →ₗ[ℂ]
      Representation.IntertwiningMap
        (extensionTensorFDRep H ψ Wq).ρ
        (extensionTensorFDRep H ψ Wq).ρ where
  toFun f :=
    { toLinearMap :=
        TensorProduct.map
          (LinearMap.id :
            ψ.realization →ₗ[ℂ] ψ.realization)
          (inflateIntertwiningMap
            (H := H) f).toLinearMap
      isIntertwining' := fun g ↦ by
        apply LinearMap.ext
        intro x
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp
        · intro v w
          change
            TensorProduct.map
                (LinearMap.id :
                  ψ.realization →ₗ[ℂ] ψ.realization)
                (inflateIntertwiningMap
                  (H := H) f).toLinearMap
                (TensorProduct.map
                  (ψ.realization.ρ g)
                  ((inflateFDRep H Wq).ρ g)
                  (v ⊗ₜ[ℂ] w)) =
              TensorProduct.map
                (ψ.realization.ρ g)
                ((inflateFDRep H Wq).ρ g)
                (TensorProduct.map
                  (LinearMap.id :
                    ψ.realization →ₗ[ℂ] ψ.realization)
                  (inflateIntertwiningMap
                    (H := H) f).toLinearMap
                  (v ⊗ₜ[ℂ] w))
          rw [TensorProduct.map_tmul,
            TensorProduct.map_tmul,
            TensorProduct.map_tmul,
            TensorProduct.map_tmul]
          change
            ψ.realization.ρ g v ⊗ₜ[ℂ]
                inflateIntertwiningMap (H := H) f
                  ((inflateFDRep H Wq).ρ g w) =
              ψ.realization.ρ g v ⊗ₜ[ℂ]
                (inflateFDRep H Wq).ρ g
                  (inflateIntertwiningMap (H := H) f w)
          rw [(inflateIntertwiningMap
            (H := H) f).isIntertwining
              (inflateFDRep H Wq).ρ
              (inflateFDRep H Wq).ρ]
        · intro x y hx hy
          simpa only [map_add] using congrArg₂ (· + ·) hx hy }
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    exact
      TensorProduct.map_add_right
        (LinearMap.id :
          ψ.realization →ₗ[ℂ] ψ.realization)
        (inflateIntertwiningMap (H := H) f).toLinearMap
        (inflateIntertwiningMap (H := H) g).toLinearMap
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    exact
      TensorProduct.map_smul_right
        c
        (LinearMap.id :
          ψ.realization →ₗ[ℂ] ψ.realization)
        (inflateIntertwiningMap (H := H) f).toLinearMap

omit [Finite K] in
@[simp]
theorem extensionTensorQuotientEndLinearMap_tmul
    (Wq : FDRep ℂ (K ⧸ H))
    (f : Representation.IntertwiningMap Wq.ρ Wq.ρ)
    (v : ψ.realization) (w : Wq) :
    extensionTensorQuotientEndLinearMap (H := H) (ψ := ψ) Wq f
        (v ⊗ₜ[ℂ] w) =
      v ⊗ₜ[ℂ] f w :=
  rfl

omit [Finite K] in
/-- Tensoring with the nonzero extension realization is faithful on
quotient endomorphisms. -/
theorem extensionTensorQuotientEndLinearMap_injective
    (Wq : FDRep ℂ (K ⧸ H)) :
    Function.Injective
      (extensionTensorQuotientEndLinearMap
        (H := H) (ψ := ψ) Wq) := by
  intro f g hfg
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro w
  obtain ⟨v : ψ.realization, hv⟩ :=
    exists_ne (0 : ψ.realization)
  obtain ⟨ell, hell⟩ :=
    Module.Projective.exists_dual_eq_one ℂ hv
  have hpure :
      v ⊗ₜ[ℂ] f w = v ⊗ₜ[ℂ] g w := by
    have happ :=
      congrArg
        (fun A : Representation.IntertwiningMap
          (extensionTensorFDRep H ψ Wq).ρ
          (extensionTensorFDRep H ψ Wq).ρ ↦
          A (v ⊗ₜ[ℂ] w)) hfg
    exact happ
  have heval :=
    congrArg
      (fun x : ψ.realization ⊗[ℂ] Wq ↦
        (TensorProduct.lid ℂ Wq)
          (TensorProduct.map ell
            (LinearMap.id : Wq →ₗ[ℂ] Wq) x))
      hpure
  simpa [TensorProduct.map_tmul, hell] using heval

/-- If tensoring a nonzero quotient representation with the extension is
simple, then the quotient representation itself is simple. -/
theorem quotientFDRep_simple_of_extensionTensor_simple
    (_hψ : IsExtensionAlong H.subtype χ ψ)
    (Wq : FDRep ℂ (K ⧸ H))
    [Nontrivial Wq]
    [Simple (extensionTensorFDRep H ψ Wq)] :
    Simple Wq := by
  let F := extensionTensorFDRep H ψ Wq
  letI : Representation.IsIrreducible F.ρ :=
    CliffordRestriction.isIrreducible_of_simple F
  have hFend :
      Module.finrank ℂ
          (Representation.IntertwiningMap F.ρ F.ρ) =
        1 :=
    Representation.IsIrreducible.finrank_intertwiningMap_self
      F.ρ
  have hle :
      Module.finrank ℂ
          (Representation.IntertwiningMap Wq.ρ Wq.ρ) ≤
        1 := by
    have h :=
      LinearMap.finrank_le_finrank_of_injective
        (extensionTensorQuotientEndLinearMap_injective
          (H := H) (ψ := ψ) Wq)
    simpa [F, hFend] using h
  have hid :
      Representation.IntertwiningMap.id Wq.ρ ≠ 0 := by
    intro heq
    obtain ⟨w : Wq, hw⟩ := exists_ne (0 : Wq)
    have happ :=
      congrArg
        (fun f : Representation.IntertwiningMap Wq.ρ Wq.ρ ↦
          f w) heq
    apply hw
    simpa using happ
  have hpos :
      0 < Module.finrank ℂ
        (Representation.IntertwiningMap Wq.ρ Wq.ρ) :=
    (Module.finrank_pos_iff_exists_ne_zero).2
      ⟨Representation.IntertwiningMap.id Wq.ρ, hid⟩
  have hEnd :
      Module.finrank ℂ
          (Representation.IntertwiningMap Wq.ρ Wq.ρ) =
        1 := by
    omega
  let homEquiv :
      (Wq ⟶ Wq) ≃ₗ[ℂ]
        Representation.IntertwiningMap Wq.ρ Wq.ρ :=
    (FDRep.forget₂HomLinearEquiv Wq Wq).symm |>.trans
      (Rep.homLinearEquiv _ _)
  apply fdRep_simple_of_end_finrank_eq_one Wq
  calc
    Module.finrank ℂ (Wq ⟶ Wq) =
        Module.finrank ℂ
          (Representation.IntertwiningMap Wq.ρ Wq.ρ) :=
      homEquiv.finrank_eq
    _ = 1 := hEnd

/-- Gallagher's tensor product is irreducible for every irreducible
quotient character, with no degree-one hypothesis. -/
theorem extensionTensorFDRep_simple
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    Simple (extensionTensorFDRep H ψ beta.realization) := by
  let D := extensionTensorFDRep H ψ beta.realization
  let e :
      (D ⟶ D) ≃ₗ[ℂ]
        Representation.IntertwiningMap D.ρ D.ρ :=
    (FDRep.forget₂HomLinearEquiv D D).symm |>.trans
      (Rep.homLinearEquiv _ _)
  apply fdRep_simple_of_end_finrank_eq_one D
  calc
    Module.finrank ℂ (D ⟶ D) =
        Module.finrank ℂ
          (Representation.IntertwiningMap D.ρ D.ρ) :=
      e.finrank_eq
    _ = 1 :=
      extensionTensor_end_finrank hψ beta

/-! ### The forward Gallagher map -/

/-- The irreducible character obtained by tensoring the chosen extension
with an inflated irreducible quotient character. -/
def gallagherTensorCharacter
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    IrreducibleCharacter K := by
  letI : Simple (extensionTensorFDRep H ψ beta.realization) :=
    extensionTensorFDRep_simple hψ beta
  exact ofSimple (extensionTensorFDRep H ψ beta.realization)

@[simp]
theorem gallagherTensorCharacter_values
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) (g : K) :
    (gallagherTensorCharacter hψ beta).values g =
      ψ.values g *
        beta.values (QuotientGroup.mk' H g) := by
  rw [gallagherTensorCharacter,
    ofSimple_values_apply,
    extensionTensorFDRep_character,
    beta.realization_character]

@[simp]
theorem gallagherTensorCharacter_degree
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    (gallagherTensorCharacter hψ beta).degree =
      ψ.degree * beta.degree := by
  rw [gallagherTensorCharacter,
    ofSimple_degree,
    extensionTensorFDRep_finrank,
    beta.realization_finrank]

/-- If the target character is a natural-number scalar multiple of an
irreducible source character, the intertwining multiplicity is that natural
number. -/
theorem finrank_intertwiningMap_of_character_eq_nat_smul
    {L : Type u} [Finite L] [Group L]
    {X Y : Type}
    [AddCommGroup X] [Module ℂ X] [Module.Finite ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [Module.Finite ℂ Y]
    (rho : Representation ℂ L X)
    (sigma : Representation ℂ L Y)
    [Representation.IsIrreducible rho]
    (n : ℕ)
    (hchar : sigma.character = (n : ℂ) • rho.character) :
    Module.finrank ℂ (rho.IntertwiningMap sigma) = n := by
  letI : Fintype L := Fintype.ofFinite L
  letI : Invertible (Nat.card L : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hself :=
    Representation.card_inv_mul_sum_char_mul_char_eq_finrank rho rho
  have hcross :=
    Representation.card_inv_mul_sum_char_mul_char_eq_finrank rho sigma
  have hend :
      Module.finrank ℂ (rho.IntertwiningMap rho) = 1 :=
    Representation.IsIrreducible.finrank_intertwiningMap_self rho
  rw [hchar] at hcross
  simp only [Pi.smul_apply, smul_eq_mul] at hcross
  have hscaled :
      (↑(Nat.card L) : ℂ)⁻¹ *
          ∑ x : L,
            ((n : ℂ) * rho.character x) *
              rho.character x⁻¹ =
        (n : ℂ) *
          ((↑(Nat.card L) : ℂ)⁻¹ *
            ∑ x : L,
              rho.character x * rho.character x⁻¹) := by
    calc
      _ = (↑(Nat.card L) : ℂ)⁻¹ *
          ((n : ℂ) *
            ∑ x : L,
              rho.character x * rho.character x⁻¹) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by ring
  have hfin :
      (Module.finrank ℂ (rho.IntertwiningMap sigma) : ℂ) =
        (n : ℂ) := by
    rw [← hcross, hscaled, hself, hend]
    norm_num
  exact_mod_cast hfin

section TypeZeroCorrespondence

variable {K₀ : Type} [Finite K₀] [Group K₀]
variable {H₀ : Subgroup K₀} [hH₀ : H₀.Normal]
variable {χ₀ : IrreducibleCharacter H₀}
variable {ψ₀ : IrreducibleCharacter K₀}

/-- The tensor character lies over the original normal-subgroup
irreducible. -/
theorem gallagherTensorCharacter_liesOver
    (hψ : IsExtensionAlong H₀.subtype χ₀ ψ₀)
    (beta : IrreducibleCharacter (K₀ ⧸ H₀)) :
    CliffordCorrespondence.LiesOverAlong H₀.subtype χ₀
      (gallagherTensorCharacter hψ beta) := by
  let phi := gallagherTensorCharacter hψ beta
  let rho : Representation ℂ H₀ χ₀.realization :=
    χ₀.realization.ρ
  let sigma : Representation ℂ H₀ phi.realization :=
    phi.realization.ρ.comp H₀.subtype
  letI : Representation.IsIrreducible rho :=
    CliffordRestriction.isIrreducible_of_simple χ₀.realization
  have hchar :
      sigma.character =
        (beta.degree : ℂ) • rho.character := by
    funext h
    have hquot :
        QuotientGroup.mk' H₀ (h : K₀) = 1 :=
      (QuotientGroup.eq_one_iff (h : K₀)).2 h.property
    have hext :
        ψ₀.values (h : K₀) = χ₀.values h :=
      hψ h
    change
      phi.realization.character (h : K₀) =
        (beta.degree : ℂ) * χ₀.realization.character h
    rw [phi.realization_character,
      show phi = gallagherTensorCharacter hψ beta from rfl,
      gallagherTensorCharacter_values,
      hext, hquot, beta.value_one,
      χ₀.realization_character]
    ring
  have hfin :
      Module.finrank ℂ (rho.IntertwiningMap sigma) =
        beta.degree :=
    finrank_intertwiningMap_of_character_eq_nat_smul
      rho sigma beta.degree hchar
  rw [CliffordCorrespondence.LiesOverAlong,
    CliffordCorrespondence.restrictionMultiplicity]
  let e :
      (χ₀.realization ⟶
          FDRep.res H₀.subtype phi.realization) ≃ₗ[ℂ]
        rho.IntertwiningMap sigma :=
    (FDRep.forget₂HomLinearEquiv
      χ₀.realization
      (FDRep.res H₀.subtype phi.realization)).symm |>.trans
      (Rep.homLinearEquiv _ _)
  rw [e.finrank_eq, hfin]
  exact beta.degree_pos

/-- The forward map into the irreducible characters lying over `χ`. -/
def gallagherForward
    (hψ : IsExtensionAlong H₀.subtype χ₀ ψ₀) :
    IrreducibleCharacter (K₀ ⧸ H₀) →
      CliffordCorrespondence.IrreducibleCharactersOverAlong
        H₀.subtype χ₀ :=
  fun beta ↦
    ⟨gallagherTensorCharacter hψ beta,
      gallagherTensorCharacter_liesOver hψ beta⟩

/-- Distinct quotient irreducibles give distinct Gallagher tensor
characters. -/
theorem gallagherForward_injective
    (hψ : IsExtensionAlong H₀.subtype χ₀ ψ₀) :
    Function.Injective (gallagherForward hψ) := by
  intro beta gamma hfg
  let D_beta :=
    extensionTensorFDRep H₀ ψ₀ beta.realization
  let D_gamma :=
    extensionTensorFDRep H₀ ψ₀ gamma.realization
  letI : Simple D_beta :=
    extensionTensorFDRep_simple hψ beta
  letI : Simple D_gamma :=
    extensionTensorFDRep_simple hψ gamma
  letI : Representation.IsIrreducible D_beta.ρ :=
    CliffordRestriction.isIrreducible_of_simple D_beta
  have hGallagher :
      gallagherTensorCharacter hψ beta =
        gallagherTensorCharacter hψ gamma :=
    congrArg (fun z ↦ z.1) hfg
  have hDchar :
      D_beta.character = D_gamma.character := by
    have hvalues :=
      congrArg
        (fun delta : IrreducibleCharacter K₀ ↦ delta.values)
        hGallagher
    simpa [D_beta, D_gamma,
      gallagherTensorCharacter] using hvalues
  let eD : Representation.Equiv D_beta.ρ D_gamma.ρ :=
    Classical.choice
      (Representation.nonempty_equiv_of_character_eq_irreducible
        D_beta.ρ D_gamma.ρ hDchar.symm)
  let eM :=
    extensionMultiplicityPostcomposeEquiv hψ eD
  let e_beta_gamma :
      Representation.Equiv beta.realization.ρ
        gamma.realization.ρ :=
    (extensionTensorMultiplicityEquiv hψ beta).trans
      (eM.trans
        (extensionTensorMultiplicityEquiv hψ gamma).symm)
  apply IrreducibleCharacter.ext
  rw [← beta.realization_character,
    ← gamma.realization_character]
  exact Representation.char_iso e_beta_gamma

/-! ### The inverse map and exhaustivity -/

/-- Evaluation reconstructs a lying-over irreducible from its quotient
multiplicity representation. -/
def extensionMultiplicityEvaluationEquiv
    (hψ : IsExtensionAlong H₀.subtype χ₀ ψ₀)
    (phi : IrreducibleCharacter K₀)
    (hphi : CliffordCorrespondence.LiesOverAlong
      H₀.subtype χ₀ phi) :
    Representation.Equiv
      (extensionTensorFDRep H₀ ψ₀
        (extensionMultiplicityQuotientFDRep
          hψ phi.realization)).ρ
      phi.realization.ρ :=
  (extensionMultiplicityTensorEquiv
    hψ phi.realization).trans
      (MultiplicityProjective.evaluationRepresentationEquivOfLiesOver
        (extensionAssociatedProjectiveRepresentation hψ)
        phi hphi)

/-- The quotient multiplicity representation of a lying-over irreducible is
itself simple. -/
theorem extensionMultiplicityQuotientFDRep_simple
    (hψ : IsExtensionAlong H₀.subtype χ₀ ψ₀)
    (phi : IrreducibleCharacter K₀)
    (hphi : CliffordCorrespondence.LiesOverAlong
      H₀.subtype χ₀ phi) :
    Simple
      (extensionMultiplicityQuotientFDRep
        hψ phi.realization) := by
  let R :=
    extensionAssociatedProjectiveRepresentation hψ
  let M :=
    extensionMultiplicityQuotientFDRep hψ phi.realization
  let F :=
    extensionTensorFDRep H₀ ψ₀ M
  letI : Nontrivial M :=
    MultiplicityProjective.space_nontrivial_of_liesOver
      R phi hphi
  letI : Simple F :=
    fdRep_simple_of_representation_equiv
      F phi.realization
      (extensionMultiplicityEvaluationEquiv hψ phi hphi)
  exact
    quotientFDRep_simple_of_extensionTensor_simple
      hψ M

/-- The inverse Gallagher character is afforded by the quotient
multiplicity representation. -/
def gallagherInverse
    (hψ : IsExtensionAlong H₀.subtype χ₀ ψ₀) :
    CliffordCorrespondence.IrreducibleCharactersOverAlong
        H₀.subtype χ₀ →
      IrreducibleCharacter (K₀ ⧸ H₀) :=
  fun phi ↦ by
    letI : Simple
        (extensionMultiplicityQuotientFDRep
          hψ phi.1.realization) :=
      extensionMultiplicityQuotientFDRep_simple
        hψ phi.1 phi.2
    exact
      ofSimple
        (extensionMultiplicityQuotientFDRep
          hψ phi.1.realization)

/-- Evaluation proves that tensoring the inverse multiplicity character
recovers the original lying-over character. -/
theorem gallagherForward_inverse
    (hψ : IsExtensionAlong H₀.subtype χ₀ ψ₀)
    (phi :
      CliffordCorrespondence.IrreducibleCharactersOverAlong
        H₀.subtype χ₀) :
    gallagherForward hψ (gallagherInverse hψ phi) = phi := by
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext g
  let M :=
    extensionMultiplicityQuotientFDRep
      hψ phi.1.realization
  let R :=
    extensionAssociatedProjectiveRepresentation hψ
  letI : Simple M :=
    extensionMultiplicityQuotientFDRep_simple
      hψ phi.1 phi.2
  change
    (gallagherTensorCharacter hψ
      (gallagherInverse hψ phi)).values g =
      phi.1.values g
  rw [gallagherTensorCharacter_values]
  rw [show gallagherInverse hψ phi = ofSimple M from rfl,
    ofSimple_values_apply]
  calc
    ψ₀.values g *
          M.character (QuotientGroup.mk' H₀ g) =
        (extensionTensorFDRep H₀ ψ₀ M).character g := by
      rw [extensionTensorFDRep_character]
    _ =
        (MultiplicityProjective.tensorRepresentation
          R phi.1.realization.ρ).character g := by
      exact congrFun
        (Representation.char_iso
          (extensionMultiplicityTensorEquiv
            hψ phi.1.realization)) g
    _ = phi.1.values g :=
      congrFun
        (MultiplicityProjective.tensorRepresentation_character_eq_of_liesOver
          R phi.1 phi.2) g

/-- The inverse also recovers every quotient irreducible, by injectivity of
the forward tensor map. -/
theorem gallagherInverse_forward
    (hψ : IsExtensionAlong H₀.subtype χ₀ ψ₀)
    (beta : IrreducibleCharacter (K₀ ⧸ H₀)) :
    gallagherInverse hψ (gallagherForward hψ beta) = beta := by
  apply gallagherForward_injective hψ
  exact gallagherForward_inverse hψ
    (gallagherForward hψ beta)

/-- **Gallagher correspondence.**  Tensoring an extension of `χ₀` with
inflated irreducible characters of `K₀/H₀` classifies exactly the
irreducible characters of `K₀` lying over `χ₀`. -/
def gallagherCorrespondence
    (hψ : IsExtensionAlong H₀.subtype χ₀ ψ₀) :
    IrreducibleCharacter (K₀ ⧸ H₀) ≃
      CliffordCorrespondence.IrreducibleCharactersOverAlong
        H₀.subtype χ₀ where
  toFun := gallagherForward hψ
  invFun := gallagherInverse hψ
  left_inv := gallagherInverse_forward hψ
  right_inv := gallagherForward_inverse hψ

end TypeZeroCorrespondence

end IrreducibleCharacter
end McKayConjecture
