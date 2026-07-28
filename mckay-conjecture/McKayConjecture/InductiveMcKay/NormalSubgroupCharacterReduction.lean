/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupJoinCenterReduction
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionReduction
import McKayConjecture.InductiveMcKay.NormalSubgroupReduction

/-!
# Character input for Rossi's first normal-subgroup reduction

Rossi's Proposition 4.2 constructs, for a suitable normal subgroup `N`,
an equivalence

`Irr_{p'}(G) ≃ Irr_{p'}((N ⊔ Z(G)) ⊔ N_G(P))`.

This file records that assertion at exactly the numerical strength needed
for Corollary 4.3.  In particular, the input below is an explicit character
equivalence, not an already assembled local correspondence.  Properness of
the target then turns the equivalence into the first field of
`NormalSubgroupLocalReductionPrinciples`.

The projective central-extension and fibrewise Clifford construction of the
equivalence is deliberately kept separate from this elementary assembly.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {P : Sylow p G}

/-- The numerical character-theoretic conclusion of Rossi's Proposition
4.2, uniformly for normal noncentral subgroups of `G`.

No properness hypothesis is imposed on the target: Proposition 4.2
constructs the equivalence before Corollary 4.3 decides whether that target
is all of `G`. -/
structure NormalSubgroupCharacterReductionData
    (P : Sylow p G) where
  normalizerIntermediateEquiv :
    ∀ (N : Subgroup G),
      N.Normal →
      ¬N ≤ Subgroup.center G →
      PPrimeIrreducibleCharacter G p ≃
        PPrimeIrreducibleCharacter
          (NormalSubgroupJoinCenterReduction.normalizerIntermediate
            P N) p

namespace NormalSubgroupCharacterReductionData

omit [Finite G] [Fact p.Prime] in
/-- A Proposition-4.2 character equivalence whose target is proper gives
the first local-reduction principle used in the minimal-counterexample
argument. -/
theorem localCorrespondence_of_normal_noncentral_sup_normalizer_ne_top
    (d : NormalSubgroupCharacterReductionData P)
    (N : Subgroup G)
    (hNnormal : N.Normal)
    (hNnoncentral : ¬N ≤ Subgroup.center G)
    (hproper :
      N ⊔ Subgroup.normalizer (P : Set G) ≠ ⊤) :
    Nonempty (LocalCorrespondence P) := by
  have hproper' :
      NormalSubgroupJoinCenterReduction.normalizerIntermediate P N ≠
        ⊤ := by
    rw [NormalSubgroupJoinCenterReduction.normalizerIntermediate_eq_normal_sup P N]
    exact hproper
  exact
    ⟨NormalSubgroupJoinCenterReduction.localCorrespondenceOfNormalizerIntermediateEquiv
        P N hproper'
        (d.normalizerIntermediateEquiv
          N hNnormal hNnoncentral)⟩

omit [Finite G] [Fact p.Prime] in
/-- Package Rossi's first character reduction together with the independent
second normal-subgroup character reduction into the exact two-principle
interface used by the minimal-counterexample structure theorem. -/
theorem toLocalReductionPrinciples
    (d : NormalSubgroupCharacterReductionData P)
    (second :
      ∀ K : Subgroup G,
        K.Normal →
        K ⊓ (P : Subgroup G) ≤ Subgroup.center G →
        ¬K ≤ Subgroup.center G →
        K ⊔ Subgroup.normalizer (P : Set G) = ⊤ →
        Nonempty (LocalCorrespondence P)) :
    NormalSubgroupLocalReductionPrinciples P where
  of_normal_noncentral_sup_sylowNormalizer_ne_top :=
    d.localCorrespondence_of_normal_noncentral_sup_normalizer_ne_top
  of_normal_inf_sylow_le_center_not_le_center_of_sup_sylowNormalizer_eq_top :=
    second

end NormalSubgroupCharacterReductionData

/-! ## Exact Theorem-4.4 input -/

section Theorem44

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable {S : Sylow q X}

/-- The exact Okuyama--Wajima/DGN input needed in Rossi's second
normal-subgroup reduction, uniformly for normal subgroups with central
Sylow intersection.

The field returns the bundled character equivalence, equivariance, and
central-triple witnesses of `Theorem44CharacterData`; it does not return an
ambient local correspondence. -/
structure NormalSubgroupTheorem44ReductionData
    (S : Sylow q X) where
  theorem44Data :
    ∀ (C : Subgroup X)
      (hCnormal : C.Normal)
      (_hcentral :
        C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
      (hgenerate :
        C ⊔ Subgroup.normalizer (S : Set X) = ⊤),
      letI : C.Normal := hCnormal
      NormalSubgroupCentralIntersectionReduction.Theorem44CharacterData
        S C hgenerate

namespace NormalSubgroupTheorem44ReductionData

/-- Exact Theorem-4.4 character data and the Corollary-4.3 generation
equality give the second local-reduction principle. -/
theorem localCorrespondence_of_centralIntersection_of_generation
    (d : NormalSubgroupTheorem44ReductionData S)
    (C : Subgroup X)
    (hCnormal : C.Normal)
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤) :
    Nonempty (LocalCorrespondence S) := by
  letI : C.Normal := hCnormal
  exact
    ⟨NormalSubgroupCentralIntersectionReduction.Theorem44CharacterData.toLocalCorrespondence
        S C hgenerate
        (d.theorem44Data C hCnormal hcentral hgenerate)⟩

/-- Proposition 4.2 and Theorem 4.4, both at their exact character-data
strength, construct the two normal-subgroup principles used in the
minimal-counterexample argument. -/
theorem localReductionPrinciples
    (first : NormalSubgroupCharacterReductionData S)
    (second : NormalSubgroupTheorem44ReductionData S) :
    NormalSubgroupLocalReductionPrinciples S :=
  first.toLocalReductionPrinciples (fun C hCnormal hcentral
      _hCnoncentral hgenerate ↦
    second.localCorrespondence_of_centralIntersection_of_generation
      C hCnormal hcentral hgenerate)

end NormalSubgroupTheorem44ReductionData

end Theorem44

end InductiveMcKay
end McKayConjecture
