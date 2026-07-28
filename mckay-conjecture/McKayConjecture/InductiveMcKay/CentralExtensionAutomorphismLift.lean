/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralExtensionLocalDescent

/-!
# Automorphism lifting across a central extension

A bare central extension does not provide a lift of every automorphism of
its target.  This is the first genuine obstruction to descending the full
inductive McKay condition: the target condition is equivariant under all of
`Aut(Q)_S`, whereas an upstairs datum only knows automorphisms of the cover.

`SylowAutomorphismLift` records exactly the missing group-theoretic datum.
The lift is required to be a group homomorphism, to preserve the lifted
Sylow subgroup, and to commute pointwise with the central projection.  From
these fields alone, an invariant upstairs intermediate projects to an
invariant intermediate downstairs.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {A : Type u} {Q : Type v}
variable [Group A] [Group Q] [Finite A]
variable {p : ℕ} [Fact p.Prime]

/-- A coherent lift of every target Sylow-stabilizing automorphism through a
central extension.  Existence of this structure is not automatic. -/
structure SylowAutomorphismLift
    (E : CentralExtension A Q) (S : Sylow p Q) where
  /-- The lifted automorphisms, preserving the unique Sylow lift. -/
  lift :
    SylowAutStabilizer S →*
      SylowAutStabilizer (E.sylowLift S)
  /-- The lift commutes with the central projection pointwise. -/
  projection_commutes :
    ∀ (α : SylowAutStabilizer S) (a : A),
      E.projection ((lift α).1 a) =
        α.1 (E.projection a)

namespace SylowAutomorphismLift

variable {E : CentralExtension A Q} {S : Sylow p Q}

/-- The inverse lifted automorphism commutes with the projection as well. -/
theorem projection_commutes_symm
    (L : SylowAutomorphismLift E S)
    (α : SylowAutStabilizer S) (a : A) :
    E.projection ((L.lift α).1.symm a) =
      α.1.symm (E.projection a) := by
  simpa using L.projection_commutes (α⁻¹) a

/-- Inflation of quotient characters intertwines a target automorphism with
its chosen lift. -/
@[simp]
theorem pPrimeInflationEquiv_smul
    (L : SylowAutomorphismLift E S)
    (α : SylowAutStabilizer S)
    (χ : PPrimeIrreducibleCharacter Q p) :
    (E.pPrimeInflationEquiv p (α • χ)).1 =
      L.lift α • (E.pPrimeInflationEquiv p χ).1 := by
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext a
  calc
    (E.pPrimeInflationEquiv p (α • χ)).1.1.values a =
        (α • χ).1.values (E.projection a) :=
      E.pPrimeInflationEquiv_apply_values p (α • χ) a
    _ =
        χ.1.values (α.1.symm (E.projection a)) :=
      rfl
    _ =
        χ.1.values
          (E.projection ((L.lift α).1.symm a)) := by
      rw [L.projection_commutes_symm α a]
    _ =
        (E.pPrimeInflationEquiv p χ).1.1.values
          ((L.lift α).1.symm a) :=
      (E.pPrimeInflationEquiv_apply_values p χ _).symm
    _ =
        (L.lift α •
          (E.pPrimeInflationEquiv p χ).1).1.values a :=
      rfl

/-- A target character stabilizer maps coherently into the stabilizer of
the inflated character upstairs. -/
def characterStabilizerLift
    (L : SylowAutomorphismLift E S)
    (χ : PPrimeIrreducibleCharacter Q p) :
    PPrimeCharacterStabilizer S χ →*
      PPrimeCharacterStabilizer
        (E.sylowLift S) (E.pPrimeInflationEquiv p χ).1 where
  toFun α :=
    ⟨L.lift α.1, by
      rw [PPrimeCharacterStabilizer.mem_iff]
      calc
        L.lift α.1 • (E.pPrimeInflationEquiv p χ).1 =
            (E.pPrimeInflationEquiv p (α.1 • χ)).1 :=
          (L.pPrimeInflationEquiv_smul α.1 χ).symm
        _ = (E.pPrimeInflationEquiv p χ).1 := by
          rw [MulAction.mem_stabilizer_iff.mp α.2]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one L.lift
  map_mul' α β := by
    apply Subtype.ext
    exact map_mul L.lift α.1 β.1

/-- The action of the downstairs character stabilizer on the cover through
the chosen automorphism lift. -/
def liftedAmbientAction
    (L : SylowAutomorphismLift E S)
    (χ : PPrimeIrreducibleCharacter Q p) :
    PPrimeCharacterStabilizer S χ →* MulAut A :=
  PPrimeCharacterStabilizer.ambientAction.comp
    (L.characterStabilizerLift χ)

@[simp]
theorem liftedAmbientAction_apply
    (L : SylowAutomorphismLift E S)
    (χ : PPrimeIrreducibleCharacter Q p)
    (α : PPrimeCharacterStabilizer S χ) (a : A) :
    L.liftedAmbientAction χ α a =
      (L.lift α.1).1 a :=
  rfl

/-- The semidirect-product projection used by triple descent.  It retains
the target character stabilizer verbatim and quotients only the normal
group coordinate. -/
def ambientSemidirectProjection
    (L : SylowAutomorphismLift E S)
    (χ : PPrimeIrreducibleCharacter Q p) :
    (A ⋊[L.liftedAmbientAction χ]
        PPrimeCharacterStabilizer S χ) →*
      (Q ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer S χ) :=
  SemidirectProduct.map E.projection
    (MonoidHom.id (PPrimeCharacterStabilizer S χ)) (by
      intro α
      ext a
      exact L.projection_commutes α.1 a)

@[simp]
theorem ambientSemidirectProjection_left
    (L : SylowAutomorphismLift E S)
    (χ : PPrimeIrreducibleCharacter Q p)
    (x :
      A ⋊[L.liftedAmbientAction χ]
        PPrimeCharacterStabilizer S χ) :
    (L.ambientSemidirectProjection χ x).left =
      E.projection x.left :=
  rfl

@[simp]
theorem ambientSemidirectProjection_right
    (L : SylowAutomorphismLift E S)
    (χ : PPrimeIrreducibleCharacter Q p)
    (x :
      A ⋊[L.liftedAmbientAction χ]
        PPrimeCharacterStabilizer S χ) :
    (L.ambientSemidirectProjection χ x).right =
      x.right :=
  rfl

/-- The semidirect-product projection is surjective. -/
theorem ambientSemidirectProjection_surjective
    (L : SylowAutomorphismLift E S)
    (χ : PPrimeIrreducibleCharacter Q p) :
    Function.Surjective (L.ambientSemidirectProjection χ) := by
  intro x
  obtain ⟨a, ha⟩ := E.surjective x.left
  refine ⟨⟨a, x.right⟩, ?_⟩
  apply SemidirectProduct.ext
  · exact ha
  · rfl

/-- The semidirect-product kernel is exactly the copy of the original
central-extension kernel in the normal coordinate.  It need not be central
in the semidirect product because lifted automorphisms may act nontrivially
on the kernel; normal quotient descent is the correct interface. -/
@[simp]
theorem ambientSemidirectProjection_ker
    (L : SylowAutomorphismLift E S)
    (χ : PPrimeIrreducibleCharacter Q p) :
    (L.ambientSemidirectProjection χ).ker =
      E.projection.ker.map
        (SemidirectProduct.inl :
          A →*
            A ⋊[L.liftedAmbientAction χ]
              PPrimeCharacterStabilizer S χ) := by
  ext x
  constructor
  · intro hx
    have hxOne :
        L.ambientSemidirectProjection χ x = 1 :=
      MonoidHom.mem_ker.mp hx
    have hxLeft : E.projection x.left = 1 := by
      exact congrArg SemidirectProduct.left hxOne
    have hxRight : x.right = 1 := by
      exact congrArg SemidirectProduct.right hxOne
    refine ⟨x.left, MonoidHom.mem_ker.mpr hxLeft, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact hxRight.symm
  · rintro ⟨a, ha, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply SemidirectProduct.ext
    · exact MonoidHom.mem_ker.mp ha
    · rfl

variable
  (d : LocalInductiveMcKayData (E.sylowLift S))

/-- Applying a lifted target automorphism preserves the upstairs
intermediate subgroup. -/
theorem lift_mem_intermediate
    (L : SylowAutomorphismLift E S)
    (α : SylowAutStabilizer S)
    {a : A} (ha : a ∈ d.intermediate) :
    (L.lift α).1 a ∈ d.intermediate := by
  have hmem :
      (L.lift α).1 a ∈
        d.intermediate.map ((L.lift α).1 : A →* A) :=
    ⟨a, ha, rfl⟩
  have hinvariant :=
    d.toEquivariant.intermediate_invariant (L.lift α)
  change
    d.intermediate.map ((L.lift α).1 : A →* A) =
      d.intermediate at hinvariant
  rw [hinvariant] at hmem
  exact hmem

/-- The projected intermediate is invariant under every target
Sylow-stabilizing automorphism. -/
theorem projectedIntermediate_invariant
    (L : SylowAutomorphismLift E S) :
    AutomorphismInvariant (SylowAutStabilizer S)
      (d.projectedIntermediate E.projection) := by
  intro α
  apply le_antisymm
  · intro q hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    obtain ⟨a, ha, rfl⟩ := hq₀
    refine
      ⟨(L.lift α).1 a,
        L.lift_mem_intermediate d α ha, ?_⟩
    exact L.projection_commutes α a
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := hq
    let aInv : A := (L.lift α).1.symm a
    have haInv : aInv ∈ d.intermediate := by
      simpa [aInv] using
        L.lift_mem_intermediate d (α⁻¹) ha
    have hqInv :
        E.projection aInv ∈
          d.projectedIntermediate E.projection :=
      ⟨aInv, haInv, rfl⟩
    refine ⟨E.projection aInv, hqInv, ?_⟩
    change α.1 (E.projection aInv) = E.projection a
    rw [L.projection_commutes_symm α a]
    exact α.1.apply_symm_apply (E.projection a)

/-- The automorphism induced on the projected intermediate. -/
def projectedIntermediateAutomorphism
    (L : SylowAutomorphismLift E S)
    (α : SylowAutStabilizer S) :
    MulAut (d.projectedIntermediate E.projection) :=
  AutomorphismInvariant.restrict
    (L.projectedIntermediate_invariant d) α

/-- The restriction of the chosen lifted automorphism to the upstairs
intermediate. -/
def liftedIntermediateAutomorphism
    (L : SylowAutomorphismLift E S)
    (α : SylowAutStabilizer S) :
    MulAut d.intermediate :=
  AutomorphismInvariant.restrict
    d.toEquivariant.intermediate_invariant (L.lift α)

/-- Inflation from the projected intermediate intertwines the explicit
downstairs automorphism with the explicit lifted automorphism upstairs. -/
theorem projectedIntermediatePPrimeInflationEquiv_automorphism
    (L : SylowAutomorphismLift E S)
    (α : SylowAutStabilizer S)
    (ψ : PPrimeIrreducibleCharacter
      (d.projectedIntermediate E.projection) p) :
    (d.projectedIntermediatePPrimeInflationEquiv E S
      (IrreducibleCharacter.pPrimeComapEquiv p
        (L.projectedIntermediateAutomorphism d α).symm ψ)).1 =
      IrreducibleCharacter.pPrimeComapEquiv p
        (L.liftedIntermediateAutomorphism d α).symm
        (d.projectedIntermediatePPrimeInflationEquiv E S ψ).1 := by
  let downAut :=
    L.projectedIntermediateAutomorphism d α
  let upAut :=
    L.liftedIntermediateAutomorphism d α
  have hprojection (a : d.intermediate) :
      d.intermediateProjection E.projection (upAut.symm a) =
        downAut.symm
          (d.intermediateProjection E.projection a) := by
    apply Subtype.ext
    exact L.projection_commutes_symm α (a : A)
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext a
  calc
    (d.projectedIntermediatePPrimeInflationEquiv
        E S
        (IrreducibleCharacter.pPrimeComapEquiv
          p downAut.symm ψ)).1.1.values a =
        (IrreducibleCharacter.pPrimeComapEquiv
          p downAut.symm ψ).1.values
          (d.intermediateProjection E.projection a) :=
      d.projectedIntermediatePPrimeInflationEquiv_apply_values
        E S
        (IrreducibleCharacter.pPrimeComapEquiv
          p downAut.symm ψ) a
    _ =
        ψ.1.values
          (downAut.symm
            (d.intermediateProjection E.projection a)) :=
      rfl
    _ =
        ψ.1.values
          (d.intermediateProjection E.projection
            (upAut.symm a)) := by
      rw [hprojection]
    _ =
        (d.projectedIntermediatePPrimeInflationEquiv
          E S ψ).1.1.values (upAut.symm a) :=
      (d.projectedIntermediatePPrimeInflationEquiv_apply_values
        E S ψ (upAut.symm a)).symm
    _ =
        (IrreducibleCharacter.pPrimeComapEquiv
          p upAut.symm
        (d.projectedIntermediatePPrimeInflationEquiv
            E S ψ).1).1.values a :=
      rfl

/-- A coherent Sylow-automorphism lift is sufficient to descend the entire
equivariant numerical local correspondence.  Thus automorphism lifting,
rather than the character bijection, is the precise obstruction at this
layer. -/
def quotientEquivariantLocalCorrespondence
    (L : SylowAutomorphismLift E S) :
    EquivariantLocalCorrespondence S where
  toLocalCorrespondence :=
    d.quotientLocalCorrespondence E S
  intermediate_invariant :=
    L.projectedIntermediate_invariant d
  map_smul' := by
    let hDown := L.projectedIntermediate_invariant d
    letI :
        MulAction (SylowAutStabilizer S)
          (PPrimeIrreducibleCharacter
            (d.projectedIntermediate E.projection) p) :=
      SylowAutStabilizer.intermediatePPrimeCharacterMulAction
        S (d.projectedIntermediate E.projection) hDown p
    letI :
        MulAction (SylowAutStabilizer (E.sylowLift S))
          (PPrimeIrreducibleCharacter d.intermediate p) :=
      d.toEquivariant.intermediateCharacterMulAction
    intro α χ
    apply
      (d.projectedIntermediatePPrimeInflationEquiv E S).injective
    apply Subtype.ext
    have hinflate :
        (E.pPrimeInflationEquiv p (α • χ)).1 =
          L.lift α • (E.pPrimeInflationEquiv p χ).1 :=
      L.pPrimeInflationEquiv_smul α χ
    have hupstairs :
        d.correspondence
            (L.lift α •
              (E.pPrimeInflationEquiv p χ).1) =
          L.lift α •
            d.correspondence
              (E.pPrimeInflationEquiv p χ).1 :=
      d.toEquivariant.map_smul
        (L.lift α) (E.pPrimeInflationEquiv p χ).1
    have hnatural :=
      L.projectedIntermediatePPrimeInflationEquiv_automorphism
        d α (d.projectedCorrespondence E S χ)
    calc
      (d.projectedIntermediatePPrimeInflationEquiv E S
          (d.projectedCorrespondence E S (α • χ))).1 =
          d.correspondence
            (E.pPrimeInflationEquiv p (α • χ)).1 :=
        congrArg Subtype.val
          (d.projectedIntermediatePPrimeInflationEquiv_projectedCorrespondence
            E S (α • χ))
      _ =
          d.correspondence
            (L.lift α •
              (E.pPrimeInflationEquiv p χ).1) := by
        rw [hinflate]
      _ =
          L.lift α •
            d.correspondence
              (E.pPrimeInflationEquiv p χ).1 :=
        hupstairs
      _ =
          IrreducibleCharacter.pPrimeComapEquiv p
            (L.liftedIntermediateAutomorphism d α).symm
            (d.correspondence
              (E.pPrimeInflationEquiv p χ).1) :=
        rfl
      _ =
          IrreducibleCharacter.pPrimeComapEquiv p
            (L.liftedIntermediateAutomorphism d α).symm
            (d.projectedIntermediatePPrimeInflationEquiv E S
              (d.projectedCorrespondence E S χ)).1 := by
        congr 1
        exact (congrArg Subtype.val
          (d.projectedIntermediatePPrimeInflationEquiv_projectedCorrespondence
            E S χ)).symm
      _ =
          (d.projectedIntermediatePPrimeInflationEquiv E S
            (IrreducibleCharacter.pPrimeComapEquiv p
              (L.projectedIntermediateAutomorphism d α).symm
              (d.projectedCorrespondence E S χ))).1 := by
        exact hnatural.symm
      _ =
          (d.projectedIntermediatePPrimeInflationEquiv E S
            (α • d.projectedCorrespondence E S χ)).1 :=
        rfl

end SylowAutomorphismLift
end InductiveMcKay
end McKayConjecture
