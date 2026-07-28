/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.MatchedCentralFibreCentralAction
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionKernel
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralScalarReduction

/-!
# The numerical Proposition 4.5 lift

Let `C ◁ X`, let `S ∈ Syl_q(X)`, and suppose
`X = C N_X(S)`.  Theorem 4.4 supplies a central-scalar numerical
correspondence on `CS`.  Its target `N_{CS}(S)` is transported to the
canonical normal copy inside `N_X(S)`.

To lift this correspondence from `CS` to `X`, Clifford theory needs only:

* equivariance of the transported Theorem-4.4 character equivalence under
  `N_X(S)`;
* equivalences of the exactly matched prime-to-`q` inertia fibres; and
* nonzero intertwiners between the matched realization operators at
  ambient-central elements.

`ProductAmbientCentralFibreCoherence` records exactly these additional
Proposition-4.5 inputs.  The resulting ambient correspondence is constructed
below; it is never assumed as a field.

The last item does not follow from the central-scalar identity on `CS`.
Indeed, one can take the direct product of any setup with a nontrivial
central `q'`-group `A`, while keeping `C` and `S` in the first factor.  The
group `CS` does not see the choice of the linear `A`-character in an ambient
inertia fibre.  Permuting those extensions can change their scalar at an
element of `A` while preserving all `CS` character data, including
noncentrality of `C` when it held before.  The nonzero central-action
intertwiner below is the smallest representation-level datum that rules out
precisely this ambiguity.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CliffordCorrespondence
open GroupTheory
open KernelAssembly

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The Theorem-4.4 equivalence, transported from `N_{CS}(S)` to its
canonical normal copy inside `N_X(S)`. -/
def internalTheorem44CentralFibreCharacterEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (d :
      ProductActiveKernelCentralFibreData
        S C hcentral) :
    PPrimeIrreducibleCharacter (product S C) q ≃
      PPrimeIrreducibleCharacter
        (internalProductNormalizer S C) q :=
  internalTheorem44CharacterEquiv S C
    (theorem44CharacterEquivOfCentralFibreData
      S C hcentral d)

/-- The exact ambient coherence needed to lift the numerical Theorem-4.4
fibre correspondence through Clifford theory. -/
structure ProductAmbientCentralFibreCoherence
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      ProductActiveKernelCentralFibreData
        S C hcentral) where
  /-- Equivariance of the transported `CS` character correspondence under
  the full ambient Sylow normalizer. -/
  characterEquiv_smul :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal
        S C hgenerate
    ∀ (h : ambientNormalizer S)
      (θ :
        PPrimeIrreducibleCharacter
          (product S C) q),
      internalTheorem44CentralFibreCharacterEquiv
          S C hcentral d (h • θ) =
        h •
          internalTheorem44CentralFibreCharacterEquiv
            S C hcentral d θ
  /-- Equivalence of the ambient inertia fibres for every exactly matched
  `CS` character. -/
  inertiaFibreEquiv :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal
        S C hgenerate
    ∀ θ :
        PPrimeIrreducibleCharacter
          (product S C) q,
      PPrimeIrreducibleCharactersOverInertia
          (product S C) θ.1 q ≃
        PPrimeIrreducibleCharactersOverInertia
          (internalProductNormalizer S C)
          (internalTheorem44CentralFibreCharacterEquiv
            S C hcentral d θ).1 q

namespace ProductAmbientCentralFibreCoherence

/-- Package the Proposition-4.5 coherence as general matched numerical
Clifford-assembly data. -/
def toMatchedCentralFibreCliffordAssemblyData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      ProductActiveKernelCentralFibreData
        S C hcentral)
    (c :
      ProductAmbientCentralFibreCoherence
        S C hcentral hgenerate d) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal
        S C hgenerate
    MatchedCentralFibreCliffordAssemblyData
      (product S C)
      (ambientNormalizer S)
      (internalProductNormalizer S C) q := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal
      S C hgenerate
  exact
    { sup_eq_top :=
        product_sup_normalizer_eq_top
          S C hgenerate
      characterEquiv :=
        internalTheorem44CentralFibreCharacterEquiv
          S C hcentral d
      characterEquiv_smul :=
        c.characterEquiv_smul
      inertiaFibreEquiv :=
        c.inertiaFibreEquiv }

/-- The final element-level coherence needed for central-scalar
preservation: the stored ambient inertia-fibre equivalences preserve
normalized values at ambient-central elements. -/
def PreservesCentralScalars
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      ProductActiveKernelCentralFibreData
        S C hcentral)
    (c :
      ProductAmbientCentralFibreCoherence
        S C hcentral hgenerate d) : Prop := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal
      S C hgenerate
  exact
    (c.toMatchedCentralFibreCliffordAssemblyData
      S C hcentral hgenerate d).PreservesCentralScalars

/-- The minimal representation-level compatibility needed beyond the
numerical inertia-fibre equivalences: every pair of matched fibre
realizations has a nonzero map intertwining the two operators attached to
an ambient-central element. -/
def HasCentralActionIntertwiners
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      ProductActiveKernelCentralFibreData
        S C hcentral)
    (c :
      ProductAmbientCentralFibreCoherence
        S C hcentral hgenerate d) : Prop := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal
      S C hgenerate
  exact
    (c.toMatchedCentralFibreCliffordAssemblyData
      S C hcentral hgenerate d).HasCentralActionIntertwiners

/-- The representation-level central-action intertwiners discharge the
element-level normalized central-value identity. -/
theorem preservesCentralScalars_of_hasCentralActionIntertwiners
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      ProductActiveKernelCentralFibreData
        S C hcentral)
    (c :
      ProductAmbientCentralFibreCoherence
        S C hcentral hgenerate d)
    (h :
      c.HasCentralActionIntertwiners
        S C hcentral hgenerate d) :
    c.PreservesCentralScalars
      S C hcentral hgenerate d := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal
      S C hgenerate
  let a :=
    c.toMatchedCentralFibreCliffordAssemblyData
      S C hcentral hgenerate d
  exact
    a.preservesCentralScalars_of_hasCentralActionIntertwiners h

/-- Rossi's Proposition 4.5 lift at exactly central-scalar numerical
strength.  The ambient correspondence is assembled from the `CS` data and
the explicit fibre and central-action coherence above. -/
def toCentralScalarLocalCorrespondence
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      ProductActiveKernelCentralFibreData
        S C hcentral)
    (c :
      ProductAmbientCentralFibreCoherence
        S C hcentral hgenerate d)
    (haction :
      c.HasCentralActionIntertwiners
        S C hcentral hgenerate d) :
    CentralScalarLocalCorrespondence S := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal
      S C hgenerate
  let a :=
    c.toMatchedCentralFibreCliffordAssemblyData
      S C hcentral hgenerate d
  exact
    { toLocalCorrespondence :=
        { intermediate := ambientNormalizer S
          normalizer_le := le_rfl
          proper_of_normalizer_ne_top := fun hne =>
            lt_top_iff_ne_top.mpr hne
          correspondence := a.assembledPPrimeEquiv }
      correspondence_central_cross := by
        intro χ z hzcentral hzintermediate
        exact
          a.assembledPPrimeEquiv_central_cross_of_hasCentralActionIntertwiners
            haction χ z hzcentral hzintermediate }

end ProductAmbientCentralFibreCoherence

/-- All genuine character-theoretic data in the numerical
Theorem-4.4/Proposition-4.5 branch, bundled without assuming its ambient
conclusion. -/
structure CentralFibreLiftData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤) where
  theorem44FibreData :
    ProductActiveKernelCentralFibreData
      S C hcentral
  ambientCoherence :
    ProductAmbientCentralFibreCoherence
      S C hcentral hgenerate theorem44FibreData
  centralActionIntertwiners :
    ambientCoherence.HasCentralActionIntertwiners
      S C hcentral hgenerate theorem44FibreData

namespace CentralFibreLiftData

/-- The bundled numerical Theorem-4.4/Proposition-4.5 input constructs the
ambient central-scalar local correspondence. -/
def toCentralScalarLocalCorrespondence
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      CentralFibreLiftData
        S C hcentral hgenerate) :
    CentralScalarLocalCorrespondence S :=
  d.ambientCoherence.toCentralScalarLocalCorrespondence
    S C hcentral hgenerate d.theorem44FibreData
      d.centralActionIntertwiners

end CentralFibreLiftData

end Proposition45
end NormalSubgroupCentralIntersectionReduction

/-- The exact remaining numerical DGN/Proposition-4.5 construction,
stated in terms of fibre data rather than the desired ambient
correspondence. -/
def CentralScalarCentralIntersectionFibreHypothesis
    (q : ℕ) [Fact q.Prime] : Prop :=
  ∀ (X : Type) [Group X] [Finite X]
    (S : Sylow q X) (C : Subgroup X)
    (hCnormal : C.Normal)
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤),
      letI : C.Normal := hCnormal
      Nonempty
        (NormalSubgroupCentralIntersectionReduction.Proposition45.CentralFibreLiftData
            S C hcentral hgenerate)

/-- The fibre-level DGN/Proposition-4.5 construction discharges the shared
central-intersection reduction hypothesis. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_fibreData
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionFibreHypothesis q) :
    CentralScalarCentralIntersectionReductionHypothesis q := by
  intro X _ _ S C hCnormal hcentral _hCnoncentral hgenerate
  letI : C.Normal := hCnormal
  obtain ⟨d⟩ :=
    h X S C hCnormal hcentral hgenerate
  exact
    ⟨d.toCentralScalarLocalCorrespondence
      S C hcentral hgenerate⟩

/-- The fibre-level Theorem-4.4/Proposition-4.5 construction, together
with the already constructed Proposition-4.2 branch, supplies the complete
central-scalar normal-subgroup reduction. -/
theorem centralScalarNormalSubgroupReductionHypothesis_of_centralIntersectionFibreData
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionFibreHypothesis q) :
    CentralScalarNormalSubgroupReductionHypothesis q :=
  centralScalarNormalSubgroupReductionHypothesis_of_centralIntersection
    (centralScalarCentralIntersectionReductionHypothesis_of_fibreData h)

end InductiveMcKay
end McKayConjecture
