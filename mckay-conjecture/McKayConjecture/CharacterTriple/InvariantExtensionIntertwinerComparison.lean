/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GallagherCorrespondence
import McKayConjecture.CharacterTriple.AssociatedExistence
import McKayConjecture.CharacterTriple.ProjectiveOperatorUniqueness

/-!
# Comparing invariant-character intertwiners with extension operators

Let `Γ` act on a group `N`, and suppose an invariant irreducible character
of `N` extends to a larger group `A`.  If a homomorphism `Γ → A`
implements the prescribed action on `N`, the honest operators afforded by
the extension can be transported back to the canonical realization of the
`N`-character.  Schur uniqueness then compares each transported honest
operator with the canonical intertwiner by a unique nonzero scalar.

The chosen scalar is packaged as a cochain on `Γ`.  This is the
construction used for the two sides of the DGN kernel Hom-action; their
ratio, rather than either scalar separately, is the selected-summand
parameter.
-/

noncomputable section

open CategoryTheory

universe u v w

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedExistence

variable {N : Type u} [Group N] [Finite N]
variable {Γ : Type v} [Group Γ] [Finite Γ]
variable {A : Type w} [Group A]
variable (alpha : Γ →* MulAut N)
variable (chi : IrreducibleCharacter N)
variable (hchi : IsInvariant alpha chi)
variable (i : N →* A)
variable (psi : IrreducibleCharacter A)
variable (hpsi :
  IrreducibleCharacter.IsExtensionAlong i chi psi)
variable (j : Γ →* A)
variable (hconj :
  ∀ (gamma : Γ) (n : N),
    j gamma * i n * (j gamma)⁻¹ =
      i (alpha gamma n))

/-- A fixed equivalence between the canonical realization of the normal
character and the restriction of the chosen extension realization. -/
def extensionRestrictionEquiv :
    Representation.Equiv
      chi.realization.ρ
      (psi.realization.ρ.comp i) := by
  let rho : Representation ℂ N chi.realization :=
    chi.realization.ρ
  let sigma : Representation ℂ N psi.realization :=
    psi.realization.ρ.comp i
  letI : Representation.IsIrreducible rho :=
    CliffordRestriction.isIrreducible_of_simple
      chi.realization
  have hchar : sigma.character = rho.character := by
    funext n
    change
      psi.realization.character (i n) =
        chi.realization.character n
    rw [psi.realization_character,
      chi.realization_character]
    exact hpsi n
  exact
    Classical.choice
      (IrreducibleCharacter.Representation.nonempty_equiv_of_character_eq_irreducible
        rho sigma hchar)

/-- The honest extension operator, transported to the canonical
realization of the invariant normal character. -/
def transportedExtensionOperator
    (gamma : Γ) :
    chi.realization ≃ₗ[ℂ] chi.realization :=
  ((extensionRestrictionEquiv
      chi i psi hpsi).toLinearEquiv.trans
    (realizationAction psi (j gamma))).trans
      (extensionRestrictionEquiv
        chi i psi hpsi).toLinearEquiv.symm

/-- The transported honest extension operators form an ordinary
representation on the canonical normal-character realization. -/
def transportedExtensionRepresentation :
    Representation ℂ Γ chi.realization where
  toFun gamma :=
    (transportedExtensionOperator
      chi i psi hpsi j gamma).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro v
    change
      (extensionRestrictionEquiv
        chi i psi hpsi).symm
          (realizationAction psi (j 1)
            (extensionRestrictionEquiv
              chi i psi hpsi v)) =
        v
    rw [map_one, map_one]
    exact
      (extensionRestrictionEquiv
        chi i psi hpsi).symm_apply_apply v
  map_mul' gamma delta := by
    apply LinearMap.ext
    intro v
    change
      (extensionRestrictionEquiv
        chi i psi hpsi).symm
          (realizationAction psi (j (gamma * delta))
            (extensionRestrictionEquiv
              chi i psi hpsi v)) =
        (extensionRestrictionEquiv
          chi i psi hpsi).symm
            (realizationAction psi (j gamma)
              (extensionRestrictionEquiv
                chi i psi hpsi
                ((extensionRestrictionEquiv
                  chi i psi hpsi).symm
                    (realizationAction psi (j delta)
                      (extensionRestrictionEquiv
                        chi i psi hpsi v)))))
    apply congrArg
      (extensionRestrictionEquiv
        chi i psi hpsi).symm
    rw [(extensionRestrictionEquiv
      chi i psi hpsi).apply_symm_apply]
    rw [map_mul, map_mul]
    rfl

/-- Finite-dimensional categorical packaging of the transported honest
extension representation. -/
abbrev transportedExtensionFDRep :
    FDRep ℂ Γ :=
  FDRep.of
    (transportedExtensionRepresentation
      chi i psi hpsi j)

@[simp]
theorem transportedExtensionOperator_apply
    (gamma : Γ) (v : chi.realization) :
    transportedExtensionOperator
        chi i psi hpsi j gamma v =
      (extensionRestrictionEquiv
        chi i psi hpsi).symm
        (realizationAction psi (j gamma)
      (extensionRestrictionEquiv
            chi i psi hpsi v)) :=
  rfl

/-- Transporting the extension action back to the normal-character
realization does not change the representation: the chosen restriction
equivalence intertwines it with the extension realization restricted
along the acting homomorphism. -/
def transportedExtensionRepresentationEquiv :
    Representation.Equiv
      (transportedExtensionRepresentation
        chi i psi hpsi j)
      (psi.realization.ρ.comp j) := by
  apply Representation.Equiv.mk
    (extensionRestrictionEquiv
      chi i psi hpsi).toLinearEquiv
  intro gamma
  apply LinearMap.ext
  intro v
  change
    extensionRestrictionEquiv chi i psi hpsi
        (transportedExtensionOperator
          chi i psi hpsi j gamma v) =
      realizationAction psi (j gamma)
        (extensionRestrictionEquiv
          chi i psi hpsi v)
  rw [transportedExtensionOperator_apply,
    (extensionRestrictionEquiv
      chi i psi hpsi).apply_symm_apply]

/-- Rewrite the target character of the chosen extension-restriction
equivalence along an equality, while retaining the original transported
extension representation on the source.  Keeping the two characters as
independent arguments makes the dependent transport explicit and avoids
unfolding implementation details of character realizations. -/
def extensionRestrictionEquivOfEq
    (psi' : IrreducibleCharacter A)
    (hpsi' : psi = psi') :
    Representation.Equiv
      chi.realization.ρ
      (psi'.realization.ρ.comp i) := by
  subst psi'
  exact extensionRestrictionEquiv chi i psi hpsi

/-- The equality-transported extension equivalence still intertwines every
operator of the original transported extension representation. -/
theorem extensionRestrictionEquivOfEq_transported_apply
    (psi' : IrreducibleCharacter A)
    (hpsi' : psi = psi')
    (gamma : Γ)
    (v : chi.realization) :
    extensionRestrictionEquivOfEq
        chi i psi hpsi psi' hpsi'
        ((transportedExtensionRepresentation
          chi i psi hpsi j) gamma v) =
      psi'.realization.ρ (j gamma)
        (extensionRestrictionEquivOfEq
          chi i psi hpsi psi' hpsi' v) := by
  subst psi'
  exact
    LinearMap.congr_fun
      ((transportedExtensionRepresentationEquiv
        chi i psi hpsi j).isIntertwining' gamma) v

/-- Categorical finite-dimensional form of
`transportedExtensionRepresentationEquiv`. -/
def transportedExtensionFDRepIso :
    transportedExtensionFDRep chi i psi hpsi j ≅
      FDRep.res j psi.realization := by
  let E :=
    transportedExtensionRepresentationEquiv
      chi i psi hpsi j
  exact
    Action.mkIso
      E.toLinearEquiv.toFGModuleCatIso
      (fun gamma ↦ by
        apply ConcreteCategory.hom_ext
        intro v
        exact LinearMap.congr_fun
          (E.isIntertwining' gamma) v)

/-- When the acting element comes from the normal subgroup itself, the
transported extension operator is exactly the original normal
representation operator. -/
theorem transportedExtensionOperator_eq_realizationAction_of_eq
    (gamma : Γ) (n : N)
    (hgamma : j gamma = i n) :
    transportedExtensionOperator
        chi i psi hpsi j gamma =
      realizationAction chi n := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro v
  apply
    (extensionRestrictionEquiv
      chi i psi hpsi).toLinearEquiv.injective
  change
    extensionRestrictionEquiv chi i psi hpsi
        (transportedExtensionOperator
          chi i psi hpsi j gamma v) =
      extensionRestrictionEquiv chi i psi hpsi
        (realizationAction chi n v)
  rw [transportedExtensionOperator_apply,
    (extensionRestrictionEquiv
      chi i psi hpsi).apply_symm_apply,
    hgamma]
  exact
    (LinearMap.congr_fun
      ((extensionRestrictionEquiv
        chi i psi hpsi).isIntertwining' n) v).symm

include hconj in
/-- The transported honest operator implements exactly the prescribed
automorphism of the normal representation. -/
theorem transportedExtensionOperator_covariance
    (gamma : Γ) (n : N) :
    transportedExtensionOperator
          chi i psi hpsi j gamma *
        realizationAction chi n =
      realizationAction chi (alpha gamma n) *
        transportedExtensionOperator
          chi i psi hpsi j gamma := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro v
  apply
    (extensionRestrictionEquiv
      chi i psi hpsi).toLinearEquiv.injective
  have hE :
      extensionRestrictionEquiv chi i psi hpsi
          (realizationAction chi n v) =
        realizationAction psi (i n)
          (extensionRestrictionEquiv
            chi i psi hpsi v) := by
    exact
      LinearMap.congr_fun
        ((extensionRestrictionEquiv
          chi i psi hpsi).isIntertwining' n) v
  have hEalpha :
      extensionRestrictionEquiv chi i psi hpsi
          (realizationAction chi (alpha gamma n)
            (transportedExtensionOperator
              chi i psi hpsi j gamma v)) =
        realizationAction psi (i (alpha gamma n))
          (extensionRestrictionEquiv
            chi i psi hpsi
            (transportedExtensionOperator
              chi i psi hpsi j gamma v)) := by
    exact
      LinearMap.congr_fun
        ((extensionRestrictionEquiv
          chi i psi hpsi).isIntertwining'
            (alpha gamma n))
        (transportedExtensionOperator
          chi i psi hpsi j gamma v)
  change
    extensionRestrictionEquiv chi i psi hpsi
        (transportedExtensionOperator
          chi i psi hpsi j gamma
          (realizationAction chi n v)) =
      extensionRestrictionEquiv chi i psi hpsi
        (realizationAction chi (alpha gamma n)
          (transportedExtensionOperator
            chi i psi hpsi j gamma v))
  rw [transportedExtensionOperator_apply,
    (extensionRestrictionEquiv
      chi i psi hpsi).apply_symm_apply,
    hE]
  rw [hEalpha, transportedExtensionOperator_apply,
    (extensionRestrictionEquiv
      chi i psi hpsi).apply_symm_apply]
  have hgroup :
    j gamma * i n =
        (j gamma * i n * (j gamma)⁻¹) * j gamma := by
      group
  rw [hconj] at hgroup
  have hop :
      realizationAction psi (j gamma) *
          realizationAction psi (i n) =
        realizationAction psi (i (alpha gamma n)) *
          realizationAction psi (j gamma) := by
    rw [← map_mul, ← map_mul, hgroup]
  exact
    DFunLike.congr_fun hop
      (extensionRestrictionEquiv
        chi i psi hpsi v)

/-- Two invertible operators implementing the same automorphism of an
irreducible representation differ by a nonzero scalar.  This version
allows one of the operators to be a canonical intertwiner chosen in a
larger acting group, which is essential when comparing on a subgroup. -/
theorem exists_scalar_of_covariance
    (beta : MulAut N)
    (T F : chi.realization ≃ₗ[ℂ] chi.realization)
    (hT :
      ∀ n : N,
        T * realizationAction chi n =
          realizationAction chi (beta n) * T)
    (hF :
      ∀ n : N,
        F * realizationAction chi n =
          realizationAction chi (beta n) * F) :
    ∃ c : ℂˣ, ∀ v : chi.realization,
      F v = (c : ℂ) • T v := by
  let comparison : chi.realization ≃ₗ[ℂ] chi.realization :=
    T⁻¹ * F
  have hcomparison :
      ∀ n : N,
        comparison * realizationAction chi n =
          realizationAction chi n * comparison := by
    intro n
    have hTinv :
        T⁻¹ * realizationAction chi (beta n) =
          realizationAction chi n * T⁻¹ := by
      apply mul_left_cancel (a := T)
      calc
        T * (T⁻¹ * realizationAction chi (beta n)) =
            realizationAction chi (beta n) := by
          simp
        _ =
            (realizationAction chi (beta n) * T) * T⁻¹ := by
          group
        _ = (T * realizationAction chi n) * T⁻¹ := by
          rw [hT]
        _ = T * (realizationAction chi n * T⁻¹) := by
          rw [mul_assoc]
    change
      (T⁻¹ * F) * realizationAction chi n =
        realizationAction chi n * (T⁻¹ * F)
    calc
      (T⁻¹ * F) * realizationAction chi n =
          T⁻¹ * (F * realizationAction chi n) := by
        rw [mul_assoc]
      _ =
          T⁻¹ * (realizationAction chi (beta n) * F) := by
        rw [hF]
      _ =
          (T⁻¹ * realizationAction chi (beta n)) * F := by
        rw [mul_assoc]
      _ = (realizationAction chi n * T⁻¹) * F := by
        rw [hTinv]
      _ = realizationAction chi n * (T⁻¹ * F) := by
        rw [mul_assoc]
  let comparisonEndomorphism :
      chi.realization ⟶ chi.realization :=
    ⟨InducedCategory.homMk
        (ModuleCat.ofHom comparison.toLinearMap),
      fun n ↦ by
        ext v
        exact DFunLike.congr_fun (hcomparison n) v⟩
  obtain ⟨c, hc⟩ :=
    endomorphism_simple_eq_smul_id
      ℂ comparisonEndomorphism
  have hpoint :
      ∀ v : chi.realization,
        c • v = comparison v := by
    intro v
    have hv := ConcreteCategory.congr_hom hc v
    change c • v = comparison v at hv
    exact hv
  have hc0 : c ≠ 0 := by
    intro hc0
    obtain ⟨v : chi.realization, hv⟩ :=
      exists_ne (0 : chi.realization)
    have hzero : comparison v = 0 := by
      rw [← hpoint v, hc0, zero_smul]
    exact hv
      (comparison.injective
        (by simpa using hzero))
  refine ⟨Units.mk0 c hc0, fun v ↦ ?_⟩
  have hv :=
    congrArg T (hpoint v)
  change
    T (c • v) =
      T (T⁻¹ (F v)) at hv
  have hTF :
      T (T⁻¹ (F v)) = F v := by
    simp
  rw [map_smul, hTF] at hv
  change F v = c • T v
  exact hv.symm

/-- Compare a canonical invariant-character intertwiner with an associated
projective operator after embedding the irreducible normal action into the
normal restriction of an arbitrary character triple.

This is the form needed away from the Sylow factor in the DGN comparison:
the ambient projective operator need not be afforded by an honest extension
element, but its associated covariance law still determines it up to scalar
on the irreducible normal constituent. -/
theorem exists_intertwiner_scalar_of_associated_along
    {B : Type} [Group B] [Finite B]
    {T : CharacterTriple B}
    {W : Type} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] [Nontrivial W]
    {Q : ProjectiveRepresentation ℂ B W}
    (S : AssociatedProjectiveRepresentation T W Q)
    (j : N →* T.normalSubgroup)
    (E : Representation.Equiv
      chi.realization.ρ
      (S.fdRestriction.ρ.comp j))
    (ambient : Γ → B)
    (hconj :
      ∀ (gamma : Γ) (n : N),
        j (alpha gamma n) =
          MulAut.conjNormal (ambient gamma) (j n))
    (gamma : Γ) :
    ∃ c : ℂˣ, ∀ v : chi.realization,
      E (intertwiner alpha chi hchi gamma v) =
        (c : ℂ) • Q.operator (ambient gamma) (E v) := by
  let F : chi.realization ≃ₗ[ℂ] chi.realization :=
    (E.toLinearEquiv.trans
      (Q.operator (ambient gamma))).trans
        E.toLinearEquiv.symm
  have hF :
      ∀ n : N,
        F * realizationAction chi n =
          realizationAction chi (alpha gamma n) * F := by
    intro n
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro v
    apply E.toLinearEquiv.injective
    have hEn :=
      LinearMap.congr_fun (E.isIntertwining' n) v
    have hEalpha :=
      LinearMap.congr_fun
        (E.isIntertwining' (alpha gamma n))
        (F v)
    have hQ :=
      DFunLike.congr_fun
        (S.operator_mul_restriction
          (ambient gamma) (j n))
        (E v)
    change
      E (realizationAction chi n v) =
        S.restriction (j n) (E v) at hEn
    change
      E (realizationAction chi (alpha gamma n) (F v)) =
        S.restriction (j (alpha gamma n)) (E (F v))
        at hEalpha
    calc
      E (F (realizationAction chi n v)) =
          Q.operator (ambient gamma)
            (E (realizationAction chi n v)) := by
        change
          E.toLinearEquiv
              (E.toLinearEquiv.symm
                (Q.operator (ambient gamma)
                  (E.toLinearEquiv
                    (realizationAction chi n v)))) =
            Q.operator (ambient gamma)
              (E.toLinearEquiv
                (realizationAction chi n v))
        exact E.toLinearEquiv.apply_symm_apply _
      _ =
          Q.operator (ambient gamma)
            (S.restriction (j n) (E v)) := by
        rw [hEn]
      _ =
          S.restriction
              (MulAut.conjNormal (ambient gamma) (j n))
            (Q.operator (ambient gamma) (E v)) := by
        simpa only [LinearEquiv.mul_apply] using hQ
      _ =
          S.restriction (j (alpha gamma n))
            (Q.operator (ambient gamma) (E v)) := by
        rw [hconj gamma n]
      _ =
          S.restriction (j (alpha gamma n))
            (E (F v)) := by
        congr 1
        change
          Q.operator (ambient gamma) (E.toLinearEquiv v) =
            E.toLinearEquiv
              (E.toLinearEquiv.symm
                (Q.operator (ambient gamma)
                  (E.toLinearEquiv v)))
        exact (E.toLinearEquiv.apply_symm_apply _).symm
      _ =
          E (realizationAction chi (alpha gamma n) (F v)) :=
        hEalpha.symm
  obtain ⟨c, hc⟩ :=
    exists_scalar_of_covariance
      (chi := chi)
      (beta := alpha gamma)
      (intertwiner alpha chi hchi gamma)
      F
      (intertwiner_mul_rho alpha chi hchi gamma)
      hF
  let d : ℂˣ :=
    Units.mk0 ((c : ℂ)⁻¹) (inv_ne_zero c.ne_zero)
  refine ⟨d, fun v ↦ ?_⟩
  have hEF :
      E (F v) =
        Q.operator (ambient gamma) (E v) := by
    change
      E.toLinearEquiv
          (E.toLinearEquiv.symm
            (Q.operator (ambient gamma)
              (E.toLinearEquiv v))) =
        Q.operator (ambient gamma) (E.toLinearEquiv v)
    exact E.toLinearEquiv.apply_symm_apply _
  have hEc :
      Q.operator (ambient gamma) (E v) =
        (c : ℂ) •
          E (intertwiner alpha chi hchi gamma v) := by
    calc
      Q.operator (ambient gamma) (E v) =
          E (F v) := hEF.symm
      _ = E ((c : ℂ) •
          intertwiner alpha chi hchi gamma v) := by
        rw [hc v]
      _ = (c : ℂ) •
          E (intertwiner alpha chi hchi gamma v) := by
        rw [map_smul]
  calc
    E (intertwiner alpha chi hchi gamma v) =
        ((c : ℂ)⁻¹) •
          ((c : ℂ) •
            E (intertwiner alpha chi hchi gamma v)) := by
              simp [c.ne_zero]
    _ = ((c : ℂ)⁻¹) •
          Q.operator (ambient gamma) (E v) := by
            exact congrArg
              (fun w : W ↦ ((c : ℂ)⁻¹) • w)
              hEc.symm
    _ = (d : ℂ) •
          Q.operator (ambient gamma) (E v) := by
            rfl

include hconj in
/-- The transported honest extension operator differs from the canonical
invariant-character intertwiner by a nonzero scalar. -/
theorem exists_transportedExtensionOperator_scalar
    (gamma : Γ) :
    ∃ c : ℂˣ, ∀ v : chi.realization,
      transportedExtensionOperator
          chi i psi hpsi j gamma v =
        (c : ℂ) •
          intertwiner alpha chi hchi gamma v := by
  let T :=
    intertwiner alpha chi hchi gamma
  let F :=
    transportedExtensionOperator
      chi i psi hpsi j gamma
  let comparison : chi.realization ≃ₗ[ℂ] chi.realization :=
    T⁻¹ * F
  have hcomparison :
      ∀ n : N,
        comparison * realizationAction chi n =
          realizationAction chi n * comparison := by
    intro n
    have hT :=
      intertwiner_mul_rho alpha chi hchi gamma n
    have hF :=
      transportedExtensionOperator_covariance
        (alpha := alpha) (chi := chi)
        (i := i) (psi := psi) (hpsi := hpsi)
        (j := j) (hconj := hconj) gamma n
    have hTinv :
        T⁻¹ * realizationAction chi (alpha gamma n) =
          realizationAction chi n * T⁻¹ := by
      apply mul_left_cancel (a := T)
      calc
        T * (T⁻¹ *
            realizationAction chi (alpha gamma n)) =
            realizationAction chi (alpha gamma n) := by
          simp
        _ =
            (realizationAction chi (alpha gamma n) * T) * T⁻¹ := by
          group
        _ = (T * realizationAction chi n) * T⁻¹ := by
          rw [hT]
        _ = T *
            (realizationAction chi n * T⁻¹) := by
          rw [mul_assoc]
    change
      (T⁻¹ * F) * realizationAction chi n =
        realizationAction chi n * (T⁻¹ * F)
    calc
      (T⁻¹ * F) * realizationAction chi n =
          T⁻¹ * (F * realizationAction chi n) := by
        rw [mul_assoc]
      _ =
          T⁻¹ *
            (realizationAction chi (alpha gamma n) * F) := by
        rw [hF]
      _ =
          (T⁻¹ *
            realizationAction chi (alpha gamma n)) * F := by
        rw [mul_assoc]
      _ = (realizationAction chi n * T⁻¹) * F := by
        rw [hTinv]
      _ = realizationAction chi n * (T⁻¹ * F) := by
        rw [mul_assoc]
  let comparisonEndomorphism :
      chi.realization ⟶ chi.realization :=
    ⟨InducedCategory.homMk
        (ModuleCat.ofHom comparison.toLinearMap),
      fun n ↦ by
        ext v
        exact DFunLike.congr_fun (hcomparison n) v⟩
  obtain ⟨c, hc⟩ :=
    endomorphism_simple_eq_smul_id
      ℂ comparisonEndomorphism
  have hpoint :
      ∀ v : chi.realization,
        c • v = comparison v := by
    intro v
    have hv := ConcreteCategory.congr_hom hc v
    change c • v = comparison v at hv
    exact hv
  have hc0 : c ≠ 0 := by
    intro hc0
    obtain ⟨v : chi.realization, hv⟩ :=
      exists_ne (0 : chi.realization)
    have hzero : comparison v = 0 := by
      rw [← hpoint v, hc0, zero_smul]
    exact hv
      (comparison.injective
        (by simpa using hzero))
  refine ⟨Units.mk0 c hc0, fun v ↦ ?_⟩
  have hv :=
    congrArg T (hpoint v)
  change
    T (c • v) =
      T (T⁻¹ (F v)) at hv
  have hTF :
      T (T⁻¹ (F v)) = F v := by
    simp
  rw [map_smul, hTF] at hv
  change F v = c • T v
  exact hv.symm

include hconj in
/-- The scalar cochain comparing the transported honest extension
operators with the canonical invariant-character intertwiners. -/
def extensionIntertwinerScalar :
    Γ → ℂˣ :=
  fun gamma ↦
    Classical.choose
      (exists_transportedExtensionOperator_scalar
        (alpha := alpha) (chi := chi) (hchi := hchi)
        (i := i) (psi := psi) (hpsi := hpsi)
        (j := j) (hconj := hconj) gamma)

include hconj in
/-- Defining operator equation for the extension-intertwiner comparison
cochain. -/
theorem extensionIntertwinerScalar_spec
    (gamma : Γ) (v : chi.realization) :
    transportedExtensionOperator
        chi i psi hpsi j gamma v =
      (extensionIntertwinerScalar
          (alpha := alpha) (chi := chi) (hchi := hchi)
          (i := i) (psi := psi) (hpsi := hpsi)
          (j := j) (hconj := hconj) gamma : ℂ) •
        intertwiner alpha chi hchi gamma v :=
  Classical.choose_spec
    (exists_transportedExtensionOperator_scalar
      (alpha := alpha) (chi := chi) (hchi := hchi)
      (i := i) (psi := psi) (hpsi := hpsi)
      (j := j) (hconj := hconj) gamma) v

end AssociatedExistence
end CharacterTriple
end McKayConjecture
