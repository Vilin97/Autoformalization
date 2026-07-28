/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalar
import McKayConjecture.Character.GallagherCorrespondence
import McKayConjecture.CharacterTriple.InertiaTopExtension
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveComparison

/-!
# Central witnesses afforded by honest extensions

Suppose two normal-subgroup characters have honest irreducible extensions
to the two ambient groups in a proposed central isomorphism.  Their ordinary
representations are factor-one projective representations, so factor-set
agreement is automatic.

The remaining representation-theoretic datum can be stated numerically:
the two extensions must have equal normalized values on the preimage of the
left centralizer.  Schur's lemma converts this cross-multiplied character
identity into equality of the two operator scalars.  Together with the
ordinary group conditions, this constructs a complete central-isomorphism
witness.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {A : Type} {B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {X : Subgroup A} [X.Normal]
variable {Y : Subgroup B} [Y.Normal]
variable {chi : IrreducibleCharacter X}
variable {phi : IrreducibleCharacter Y}
variable {psi : IrreducibleCharacter A}
variable {xi : IrreducibleCharacter B}

/-- Two honest extensions, exact central-restriction group data, and equality
of normalized values on the left centralizer determine a complete central
isomorphism witness.

The cross identity is deliberately the only scalar hypothesis.  Both factor
sets are definitionally one, while Schur's lemma and the nonzero character
degrees force the two scalar operators to use the same unit. -/
def completeCentralIsomorphismWitnessOfExtensions
    (hpsi :
      IrreducibleCharacter.IsExtensionAlong
        X.subtype chi psi)
    (hxi :
      IrreducibleCharacter.IsExtensionAlong
        Y.subtype phi xi)
    (e : B →* A)
    (groupData :
      CentralRestrictionGroupData
        (IrreducibleCharacter.extensionCharacterTriple hpsi)
        (IrreducibleCharacter.extensionCharacterTriple hxi)
        e)
    (centralizer_cross :
      ∀ b : B,
        e b ∈ Subgroup.centralizer (X : Set A) →
          psi.values (e b) * (xi.degree : ℂ) =
            xi.values b * (psi.degree : ℂ)) :
    CompleteCentralIsomorphismWitness
      (IrreducibleCharacter.extensionCharacterTriple hpsi)
      (IrreducibleCharacter.extensionCharacterTriple hxi) := by
  letI : Nontrivial psi.realization :=
    CliffordRestriction.nontrivial_of_simple psi.realization
  letI : Nontrivial xi.realization :=
    CliffordRestriction.nontrivial_of_simple xi.realization
  let leftAssociated :=
    IrreducibleCharacter.extensionAssociatedProjectiveRepresentation hpsi
  let rightAssociated :=
    IrreducibleCharacter.extensionAssociatedProjectiveRepresentation hxi
  let comparison :
      CompleteCentralProjectiveComparisonData
        (IrreducibleCharacter.extensionCharacterTriple hpsi)
        (IrreducibleCharacter.extensionCharacterTriple hxi)
        e := by
    refine
      { leftSpace := psi.realization
        rightSpace := xi.realization
        leftProjective :=
          IrreducibleCharacter.extensionProjectiveRepresentation
            (ψ := psi)
        leftAssociated := leftAssociated
        rightProjective :=
          IrreducibleCharacter.extensionProjectiveRepresentation
            (ψ := xi)
        rightAssociated := rightAssociated
        factor_agreement := ?_
        scalar_agreement := ?_ }
    · intro b c
      rfl
    · intro b hb
      change
        e b ∈ Subgroup.centralizer (X : Set A)
        at hb
      have hbRight :
          b ∈ Subgroup.centralizer (Y : Set B) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        apply groupData.embedding_injective
        have hey :
            e y ∈ X := by
          have hmap :
              e y ∈ Y.map e :=
            ⟨y, hy, rfl⟩
          have hintersection :
              X ⊓ MonoidHom.range e =
                Y.map e := by
            simpa only [
              IrreducibleCharacter.extensionCharacterTriple
            ] using
              groupData.intersection_eq
          have hmapInf :
              e y ∈ X ⊓ MonoidHom.range e := by
            rw [hintersection]
            exact hmap
          exact hmapInf.1
        simpa using
          (Subgroup.mem_centralizer_iff.mp hb)
            (e y) hey
      obtain ⟨c, hc⟩ :=
        leftAssociated.operator_centralizer_isScalar
          (e b) hb
      obtain ⟨d, hd⟩ :=
        rightAssociated.operator_centralizer_isScalar
          b hbRight
      have hcLinear :
          psi.realization.ρ (e b) =
            (c : ℂ) •
              (LinearMap.id :
                Module.End ℂ psi.realization) := by
        ext z
        have hz := LinearEquiv.congr_fun hc z
        change
          (IrreducibleCharacter.extensionRealizationAction
            (ψ := psi) (e b)) z =
              (c : ℂ) • z
          at hz
        change
          psi.realization.ρ (e b) z =
            (c : ℂ) • z
        exact hz
      have hdLinear :
          xi.realization.ρ b =
            (d : ℂ) •
              (LinearMap.id :
                Module.End ℂ xi.realization) := by
        ext z
        have hz := LinearEquiv.congr_fun hd z
        change
          (IrreducibleCharacter.extensionRealizationAction
            (ψ := xi) b) z =
              (d : ℂ) • z
          at hz
        change
          xi.realization.ρ b z =
            (d : ℂ) • z
        exact hz
      have hcross := centralizer_cross b hb
      rw [
        psi.values_eq_scalar_mul_degree
          (e b) (c : ℂ) hcLinear,
        xi.values_eq_scalar_mul_degree
          b (d : ℂ) hdLinear
      ] at hcross
      have hpsiDegree : (psi.degree : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr psi.degree_ne_zero
      have hxiDegree : (xi.degree : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr xi.degree_ne_zero
      have hscalar : (c : ℂ) = (d : ℂ) := by
        apply
          mul_left_cancel₀
            (mul_ne_zero hpsiDegree hxiDegree)
        calc
          (psi.degree : ℂ) * (xi.degree : ℂ) * (c : ℂ) =
              (c : ℂ) * (psi.degree : ℂ) *
                (xi.degree : ℂ) := by ring
          _ =
              (d : ℂ) * (xi.degree : ℂ) *
                (psi.degree : ℂ) :=
            hcross
          _ =
              (psi.degree : ℂ) * (xi.degree : ℂ) *
                (d : ℂ) := by ring
      have hcd : c = d :=
        Units.ext hscalar
      exact
        ⟨c, hc, hcd ▸ hd⟩
  exact
    comparison.toCompleteCentralIsomorphismWitness
      groupData

@[simp]
theorem completeCentralIsomorphismWitnessOfExtensions_embedding
    (hpsi :
      IrreducibleCharacter.IsExtensionAlong
        X.subtype chi psi)
    (hxi :
      IrreducibleCharacter.IsExtensionAlong
        Y.subtype phi xi)
    (e : B →* A)
    (groupData :
      CentralRestrictionGroupData
        (IrreducibleCharacter.extensionCharacterTriple hpsi)
        (IrreducibleCharacter.extensionCharacterTriple hxi)
        e)
    (centralizer_cross :
      ∀ b : B,
        e b ∈ Subgroup.centralizer (X : Set A) →
          psi.values (e b) * (xi.degree : ℂ) =
            xi.values b * (psi.degree : ℂ)) :
    (completeCentralIsomorphismWitnessOfExtensions
      hpsi hxi e groupData centralizer_cross).embedding =
        e :=
  rfl

/-- Inertia-triple specialization of
`completeCentralIsomorphismWitnessOfExtensions`.

The two characters live on the two inertia groups and honestly extend the
canonical internal copies of the matched normal characters.  Exact group
data is stated directly for `ofInertia`; the preceding transport theorem
identifies those canonical triples with the extension triples used by the
factor-one constructor. -/
def completeCentralIsomorphismWitnessOfInertiaExtensions
    {G H : Type}
    [Group G] [Finite G] [Group H] [Finite H]
    (N : Subgroup G) [N.Normal]
    (M : Subgroup H) [M.Normal]
    (theta : IrreducibleCharacter N)
    (phi : IrreducibleCharacter M)
    (psi :
      IrreducibleCharacter
        (IrreducibleCharacter.inertia N theta))
    (xi :
      IrreducibleCharacter
        (IrreducibleCharacter.inertia M phi))
    (hpsi :
      IrreducibleCharacter.IsExtensionAlong
        (CliffordEquivalence.inertiaNormalCopy
          N theta).subtype
        (CliffordEquivalence.inertiaCopyCharacter
          N theta)
        psi)
    (hxi :
      IrreducibleCharacter.IsExtensionAlong
        (CliffordEquivalence.inertiaNormalCopy
          M phi).subtype
        (CliffordEquivalence.inertiaCopyCharacter
          M phi)
        xi)
    (e :
      IrreducibleCharacter.inertia M phi →*
        IrreducibleCharacter.inertia N theta)
    (groupData :
      CentralRestrictionGroupData
        (ofInertia N theta)
        (ofInertia M phi)
        e)
    (centralizer_cross :
      ∀ b : IrreducibleCharacter.inertia M phi,
        e b ∈
            Subgroup.centralizer
              (CliffordEquivalence.inertiaNormalCopy
                N theta :
                Set
                  (IrreducibleCharacter.inertia
                    N theta)) →
          psi.values (e b) * (xi.degree : ℂ) =
            xi.values b * (psi.degree : ℂ)) :
    CompleteCentralIsomorphismWitness
      (ofInertia N theta)
      (ofInertia M phi) := by
  have hleft :
      IrreducibleCharacter.extensionCharacterTriple hpsi =
        ofInertia N theta :=
    extensionCharacterTriple_eq_ofInertia
      N theta psi hpsi
  have hright :
      IrreducibleCharacter.extensionCharacterTriple hxi =
        ofInertia M phi :=
    extensionCharacterTriple_eq_ofInertia
      M phi xi hxi
  rw [← hleft, ← hright] at groupData ⊢
  exact
    completeCentralIsomorphismWitnessOfExtensions
      hpsi hxi e groupData centralizer_cross

namespace CompleteCentralIsomorphismWitness

/-- Forget the ordinary group fields of a complete central witness and retain
its associated projective representations and their two comparison laws. -/
def toCompleteCentralProjectiveComparisonData
    {A B : Type}
    [Group A] [Finite A] [Group B] [Finite B]
    {T : CharacterTriple A} {U : CharacterTriple B}
    (C : CompleteCentralIsomorphismWitness T U) :
    CompleteCentralProjectiveComparisonData
      T U C.embedding := by
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  exact
    { leftSpace := C.leftSpace
      rightSpace := C.rightSpace
      leftProjective := C.witness.leftProjective
      leftAssociated := C.witness.leftAssociated
      rightProjective := C.witness.rightProjective
      rightAssociated := C.witness.rightAssociated
      factor_agreement := C.witness.factor_agreement
      scalar_agreement := C.witness.scalar_agreement }

end CompleteCentralIsomorphismWitness

end InductiveMcKay
end McKayConjecture
