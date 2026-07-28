/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.PerfectCentralExtensionCenter
import McKayConjecture.InductiveMcKay.CentralExtensionRestrictedTripleAssociation
import McKayConjecture.InductiveMcKay.SemidirectStructure

/-!
# Descent of a restricted central-isomorphism witness

For a perfect source central extension, the restricted upstairs witness
descends to a genuine projective-compatibility witness downstairs.

Perfectness is used at one precise point.  If an element of the downstairs
semidirect product centralizes the downstairs normal group, a chosen lift
centralizes the upstairs normal group.  Indeed the lifted automorphism and
the corresponding inner automorphism induce the same automorphism of the
quotient; two endomorphisms of a perfect central extension with that
property are equal.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace InductiveMcKay
namespace SylowAutomorphismLift

open GroupTheory
open CharacterTriple

variable {A : Type u} {Q : Type v}
variable [Group A] [Group Q] [Finite A] [Finite Q]
variable [Group.IsPerfect A]
variable {p : ℕ} [Fact p.Prime]
variable {E : CentralExtension A Q} {S : Sylow p Q}
variable
  (L : SylowAutomorphismLift E S)
  (d : LocalInductiveMcKayData (E.sylowLift S))
  (χ : PPrimeIrreducibleCharacter Q p)

/-- In a perfect central extension, an ambient pullback element whose
projection centralizes the downstairs normal group already centralizes the
upstairs normal group. -/
theorem mem_restrictedAmbient_centralizer_of_projection
    (z : ambientLiftPullback L χ)
    (hz :
      ambientPullbackProjection L χ z ∈
        Subgroup.centralizer
          ((EquivariantLocalCorrespondence.ambientTriple
              (P := S) χ).normalSubgroup :
            Set
              (Q ⋊[PPrimeCharacterStabilizer.ambientAction]
                PPrimeCharacterStabilizer S χ))) :
    z ∈
      Subgroup.centralizer
        ((restrictedAmbientTriple L χ).normalSubgroup :
          Set (ambientLiftPullback L χ)) := by
  let γ : PPrimeCharacterStabilizer S χ :=
    ambientPullbackStabilizer L χ z
  have hright :
      L.characterStabilizerLift χ γ =
        z.1.right :=
    characterStabilizerLift_ambientPullbackStabilizer
      L χ z
  have hinnerProjection (a : A) :
      γ.1.1 (E.projection a) =
        (E.projection z.1.left)⁻¹ *
          E.projection a *
          E.projection z.1.left := by
    let xDown :
        (EquivariantLocalCorrespondence.ambientTriple
          (P := S) χ).normalSubgroup :=
      ⟨SemidirectProduct.inl (E.projection a),
        ⟨E.projection a, rfl⟩⟩
    have hcomm :=
      (Subgroup.mem_centralizer_iff.mp hz)
        (xDown :
          Q ⋊[PPrimeCharacterStabilizer.ambientAction]
            PPrimeCharacterStabilizer S χ)
        xDown.property
    have hleft :=
      congrArg SemidirectProduct.left hcomm
    have hleft' :
        E.projection a * E.projection z.1.left =
          E.projection z.1.left *
            γ.1.1 (E.projection a) := by
      simpa [xDown, γ] using hleft
    calc
      γ.1.1 (E.projection a) =
          (E.projection z.1.left)⁻¹ *
            (E.projection z.1.left *
              γ.1.1 (E.projection a)) := by simp
      _ =
          (E.projection z.1.left)⁻¹ *
            (E.projection a *
              E.projection z.1.left) := by
        rw [hleft']
      _ =
          (E.projection z.1.left)⁻¹ *
            E.projection a *
            E.projection z.1.left := by
        rw [mul_assoc]
  have hprojection :
      E.projection.comp
          (PPrimeCharacterStabilizer.ambientAction
            (P := E.sylowLift S)
            (χ := inflatedCharacter E χ)
            z.1.right).toMonoidHom =
        E.projection.comp
          (MulAut.conj z.1.left⁻¹).toMonoidHom := by
    ext a
    change
      E.projection (z.1.right.1.1 a) =
        E.projection
          (z.1.left⁻¹ * a * (z.1.left⁻¹)⁻¹)
    rw [← hright]
    change
      E.projection ((L.lift γ.1).1 a) =
        E.projection
          (z.1.left⁻¹ * a * (z.1.left⁻¹)⁻¹)
    rw [L.projection_commutes,
      map_mul, map_mul, map_inv, inv_inv]
    exact hinnerProjection a
  have hautomorphism :
      (PPrimeCharacterStabilizer.ambientAction
          (P := E.sylowLift S)
          (χ := inflatedCharacter E χ)
          z.1.right).toMonoidHom =
        (MulAut.conj z.1.left⁻¹).toMonoidHom :=
    E.hom_ext_of_source_perfect inferInstance _ _ hprojection
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxRight : x.1.right = 1 := by
    obtain ⟨a, ha⟩ := hx
    have hrightX := congrArg SemidirectProduct.right ha
    simpa using hrightX.symm
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change
      x.1.left *
          (PPrimeCharacterStabilizer.ambientAction
            (P := E.sylowLift S)
            (χ := inflatedCharacter E χ)
            x.1.right) z.1.left =
        z.1.left *
          (PPrimeCharacterStabilizer.ambientAction
            (P := E.sylowLift S)
            (χ := inflatedCharacter E χ)
            z.1.right) x.1.left
    rw [hxRight, map_one, MulAut.one_apply]
    change
      x.1.left * z.1.left =
        z.1.left *
          (PPrimeCharacterStabilizer.ambientAction
            (P := E.sylowLift S)
            (χ := inflatedCharacter E χ)
            z.1.right).toMonoidHom x.1.left
    rw [hautomorphism]
    simp only [
      MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply,
      inv_inv]
    group
  · simp [hxRight]

/-- A restricted upstairs central-isomorphism witness descends to the
representation-theoretic witness required for the downstairs local datum. -/
def descendProjectiveCompatibilityWitness
    {V W : Type}
    [AddCommGroup V] [Module ℂ V]
      [Module.Finite ℂ V] [Nontrivial V]
    [AddCommGroup W] [Module ℂ W]
      [Module.Finite ℂ W] [Nontrivial W]
    (C : CentralIsomorphismWitness
      (restrictedAmbientTriple L χ)
      (restrictedIntermediateTriple L d χ) V W)
    (hC :
      C.embedding =
        restrictedSemidirectEmbedding L d χ) :
    EquivariantLocalCorrespondence.ProjectiveCompatibilityWitness
      (L.quotientEquivariantLocalCorrespondence d) χ V W := by
  let qL := ambientTripleQuotientData L χ
  let qR := intermediateTripleQuotientData L d χ
  let hL :=
    qL.associated_isQuotientCompatible C.leftAssociated
  let hR :=
    qR.associated_isQuotientCompatible C.rightAssociated
  exact
    { leftProjective :=
        qL.quotientProjective hL
      leftAssociated :=
        qL.quotientAssociated C.leftAssociated hL
      rightProjective :=
        qR.quotientProjective hR
      rightAssociated :=
        qR.quotientAssociated C.rightAssociated hR
      factorAgreement := by
        intro h k
        obtain ⟨b, rfl⟩ :=
          intermediatePullbackProjection_surjective
            L d χ h
        obtain ⟨c, rfl⟩ :=
          intermediatePullbackProjection_surjective
            L d χ k
        rw [←
          pullbackProjection_restrictedSemidirectEmbedding
            L d χ b,
          ←
          pullbackProjection_restrictedSemidirectEmbedding
            L d χ c,
          qL.quotientProjective_factor_projection hL,
          qR.quotientProjective_factor_projection hR]
        simpa [hC] using C.factor_agreement b c
      scalarAgreement := by
        intro h hh
        obtain ⟨b, rfl⟩ :=
          intermediatePullbackProjection_surjective
            L d χ h
        have hzDown :
            ambientPullbackProjection L χ
                (restrictedSemidirectEmbedding L d χ b) ∈
              Subgroup.centralizer
                ((EquivariantLocalCorrespondence.ambientTriple
                    (P := S) χ).normalSubgroup :
                  Set
                    (Q ⋊[
                      PPrimeCharacterStabilizer.ambientAction]
                      PPrimeCharacterStabilizer S χ)) := by
          rw [pullbackProjection_restrictedSemidirectEmbedding]
          exact hh
        have hzUp :=
          mem_restrictedAmbient_centralizer_of_projection
            L χ
            (restrictedSemidirectEmbedding L d χ b)
            hzDown
        obtain ⟨c, hcLeft, hcRight⟩ :=
          C.scalar_agreement b (by
            simpa [hC] using hzUp)
        refine ⟨c, ?_, ?_⟩
        · rw [←
            pullbackProjection_restrictedSemidirectEmbedding
              L d χ b,
            qL.quotientProjective_operator_projection hL]
          simpa [hC] using hcLeft
        · rw [qR.quotientProjective_operator_projection hR]
          exact hcRight }

end SylowAutomorphismLift
end InductiveMcKay
end McKayConjecture
