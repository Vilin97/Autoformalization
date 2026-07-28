/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.MinimalNormalQuasisimple
import McKayConjecture.InductiveMcKay.ProductLocal
import McKayConjecture.InductiveMcKay.Transport

/-!
# Local correspondences for nonabelian minimal normal subgroups

A finite nonabelian minimal normal subgroup is a finite direct product of
nonabelian simple, hence quasisimple, factors.  The quasisimple inductive
McKay hypothesis supplies local data on those factors.  Taking their
finite product and transporting through the internal product
isomorphism supplies local data on a canonical Sylow subgroup of the
minimal normal subgroup.  Sylow conjugacy then supplies it for every
Sylow subgroup.

The group carriers and the factor index type in this file live in
`Type`.  This records the current universe-zero exhaustivity boundary of
`IrreducibleCharacter.finiteProductPPrimeEquiv`; the group-theoretic
decomposition itself is universe-polymorphic.
-/

noncomputable section

namespace McKayConjecture

variable {G : Type} [Group G] [Finite G]
variable {N : Subgroup G} [N.Normal]
variable {p : ℕ} [Fact p.Prime]

namespace GroupTheory.MinimalNormalFactors.NonabelianMinimalNormalDecomposition

/-- A chosen Sylow subgroup in each simple factor. -/
def factorSylowFamily
    (D : NonabelianMinimalNormalDecomposition N)
    (p : ℕ) :
    ∀ i, Sylow p (D.factor i) :=
  fun _ ↦ Classical.choice Sylow.nonempty

/-- The coordinatewise product of the chosen factor Sylow subgroups. -/
def productSylow
    (D : NonabelianMinimalNormalDecomposition N)
    (p : ℕ) :
    Sylow p (∀ i, D.factor i) := by
  letI : Fintype D.ι := D.fintype
  exact GroupTheory.Sylow.pi (D.factorSylowFamily p)

/-- The canonical Sylow subgroup of `N` obtained by transporting the
product of the chosen factor Sylows through the internal-product
isomorphism. -/
def canonicalSylow
    (D : NonabelianMinimalNormalDecomposition N)
    (p : ℕ) :
    Sylow p N :=
  McKayConjecture.Sylow.transport
    D.productEquiv (D.productSylow p)

end GroupTheory.MinimalNormalFactors.NonabelianMinimalNormalDecomposition

namespace InductiveMcKay

open GroupTheory
open GroupTheory.MinimalNormalFactors

namespace QuasisimpleInductiveMcKayHypothesis

/-- The local correspondence on the canonical Sylow subgroup associated
to a fixed nonabelian minimal-normal decomposition. -/
def canonicalLocalCorrespondence
    (h : QuasisimpleInductiveMcKayHypothesis.{0} p)
    (D : NonabelianMinimalNormalDecomposition N) :
    LocalCorrespondence (D.canonicalSylow p) := by
  letI : Fintype D.ι := D.fintype
  let factorData :
      ∀ i, LocalCorrespondence
        (D.factorSylowFamily p i) :=
    h.factorLocalCorrespondenceFamily D
      (D.factorSylowFamily p)
  let productData :
      LocalCorrespondence
        (GroupTheory.Sylow.pi
          (D.factorSylowFamily p)) :=
    LocalCorrespondence.finiteProduct
      (D.factorSylowFamily p) factorData
  change
    LocalCorrespondence
      (McKayConjecture.Sylow.transport
        D.productEquiv
        (GroupTheory.Sylow.pi
          (D.factorSylowFamily p)))
  exact
    LocalCorrespondence.transport
      D.productEquiv
      (GroupTheory.Sylow.pi
        (D.factorSylowFamily p))
      productData

/-- Local data for an arbitrary Sylow subgroup of a fixed nonabelian
minimal-normal decomposition. -/
def localCorrespondenceForSylow
    (h : QuasisimpleInductiveMcKayHypothesis.{0} p)
    (D : NonabelianMinimalNormalDecomposition N)
    (Q : Sylow p N) :
    LocalCorrespondence Q := by
  let P₀ : Sylow p N := D.canonicalSylow p
  let d₀ : LocalCorrespondence P₀ :=
    h.canonicalLocalCorrespondence D
  let g : N :=
    Classical.choose
      (MulAction.exists_smul_eq N P₀ Q)
  have hg : g • P₀ = Q :=
    Classical.choose_spec
      (MulAction.exists_smul_eq N P₀ Q)
  have htransport :
      McKayConjecture.Sylow.transport
          (MulAut.conj g) P₀ =
        Q := by
    simpa only [McKayConjecture.Sylow.transport_conj]
      using hg
  exact htransport ▸
    LocalCorrespondence.transport
      (MulAut.conj g) P₀ d₀

/-- A quasisimple inductive-McKay hypothesis supplies local data for
every Sylow subgroup of a finite nonabelian minimal normal subgroup. -/
def minimalNormalLocalCorrespondence
    (h : QuasisimpleInductiveMcKayHypothesis.{0} p)
    (hN : IsMinimalNormal N)
    (hnoncomm : ¬ IsMulCommutative N)
    (Q : Sylow p N) :
    LocalCorrespondence Q :=
  let D :=
    nonabelianMinimalNormalDecomposition
      hN hnoncomm
  h.localCorrespondenceForSylow D Q

/-- Existence form of `minimalNormalLocalCorrespondence`. -/
theorem nonempty_localCorrespondence_of_minimalNormal
    (h : QuasisimpleInductiveMcKayHypothesis.{0} p)
    (hN : IsMinimalNormal N)
    (hnoncomm : ¬ IsMulCommutative N)
    (Q : Sylow p N) :
    Nonempty (LocalCorrespondence Q) :=
  ⟨h.minimalNormalLocalCorrespondence
    hN hnoncomm Q⟩

end QuasisimpleInductiveMcKayHypothesis

end InductiveMcKay
end McKayConjecture
