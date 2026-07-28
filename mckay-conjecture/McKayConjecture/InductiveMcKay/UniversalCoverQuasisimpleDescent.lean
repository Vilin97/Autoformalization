/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.UniversalCoverPerfectCoverDescent
import McKayConjecture.InductiveMcKay.QuasisimpleFamilyReduction
import McKayConjecture.GroupTheory.FiniteUniversalCentralExtension

/-!
# From universal-cover data to quasisimple data

Every quasisimple group `A` is a perfect central cover of its nonabelian
simple central quotient `A / Z(A)`.  Once a finite universal central
extension of that quotient is chosen, full local inductive-McKay data
descend from the universal cover to `A`.

Finite universal central extensions are supplied by the classical
free-presentation construction `[F,F]/[F,R]`.
-/

noncomputable section

open scoped IsMulCommutative

universe u

namespace McKayConjecture

namespace InductiveMcKay

open GroupTheory

/-- Existence of finite universal central extensions for finite
nonabelian simple groups in a fixed universe. -/
def FiniteUniversalCentralExtensionExistence : Prop :=
  ∀ (S : Type u) [Group S] [Finite S],
    IsSimpleGroup S →
    ¬IsMulCommutative S →
    ∃ (U : Type u) (_ : Group U) (_ : Finite U),
      Nonempty (UniversalCentralExtension U S)

/-- Finite nonabelian simple groups have finite universal central
extensions. -/
theorem finiteUniversalCentralExtensionExistence :
    FiniteUniversalCentralExtensionExistence.{u} := by
  intro S _ _ hs hnoncomm
  exact
    finite_universalCentralExtension_exists_of_isSimpleGroup
      hs hnoncomm

namespace UniversalCoverInductiveMcKayHypothesis

/-- Universal-cover local data imply local data for every quasisimple
group. -/
theorem toQuasisimple
    {p : ℕ} [Fact p.Prime]
    (covers : UniversalCoverInductiveMcKayHypothesis.{u} p) :
    QuasisimpleInductiveMcKayHypothesis.{u} p := by
  intro A groupA finiteA hA P
  letI : Group A := groupA
  letI : Finite A := finiteA
  letI : Group.IsPerfect A := hA.isPerfect
  let S : Type u :=
    A ⧸ Subgroup.center A
  have hs : IsSimpleGroup S :=
    hA.isSimpleGroup_quotient
  letI : IsSimpleGroup S := hs
  have hnoncomm : ¬IsMulCommutative S :=
    quasisimple_centralQuotient_not_isMulCommutative hA
  obtain ⟨U, groupU, finiteU, ⟨E⟩⟩ :=
    finiteUniversalCentralExtensionExistence
      S hs hnoncomm
  letI : Group U := groupU
  letI : Finite U := finiteU
  exact
    covers.localInductiveMcKayData_on_perfect_cover
      hs hnoncomm E (centralQuotientExtension A)
      hA.isPerfect P

end UniversalCoverInductiveMcKayHypothesis
end InductiveMcKay
end McKayConjecture
