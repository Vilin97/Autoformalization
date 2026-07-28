/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionAmbientCyclotomic
import McKayConjecture.Character.PRegularConjugacyClasses

/-!
# A `p`-regular element inside its centralizer

Bernstein's local Brauer-induction function is constructed in the
centralizer of a `p`-regular element.  This file supplies the routine
subtype bookkeeping:

* the element itself, regarded as an element of its singleton centralizer;
* its centrality and `p`-regularity there;
* commuting `p`-elements transported into the centralizer;
* a chosen Sylow subgroup of the centralizer;
* the divisibility needed to put all Fourier coefficients in the
  cyclotomic ring indexed by the order of the original ambient group.
-/

noncomputable section

namespace McKayConjecture
namespace PRegularCentralizer

variable {G : Type} [Group G]

/-- The centralizer of one specified element. -/
abbrev group (a : G) : Subgroup G :=
  Subgroup.centralizer {a}

/-- The distinguished element, regarded as an element of its own
centralizer. -/
def element (a : G) : group a :=
  ⟨a, by
    rw [Subgroup.mem_centralizer_singleton_iff]⟩

@[simp]
theorem element_coe (a : G) :
    ((element a : group a) : G) = a :=
  rfl

/-- The distinguished element is central in its centralizer. -/
theorem element_mem_center (a : G) :
    element a ∈ Subgroup.center (group a) := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  exact
    Subgroup.mem_centralizer_singleton_iff.mp
      x.property

/-- `p`-regularity is unchanged when the distinguished element is
regarded inside its centralizer. -/
theorem element_isPRegular
    (p : ℕ) {a : G}
    (ha : IsPRegular p a) :
    IsPRegular p (element a) := by
  simpa only [IsPRegular, element,
    Subgroup.orderOf_mk] using ha

/-- A commuting element belongs to the singleton centralizer. -/
def commutingElement
    {a t : G} (hat : Commute a t) :
    group a :=
  ⟨t,
    Subgroup.mem_centralizer_singleton_iff.mpr
      hat.symm.eq⟩

@[simp]
theorem commutingElement_coe
    {a t : G} (hat : Commute a t) :
    ((commutingElement hat : group a) : G) = t :=
  rfl

/-- A `p`-element remains a `p`-element in the singleton centralizer when
its commutation proof is used to form the subtype element. -/
theorem commutingElement_isPElement
    (p : ℕ) {a t : G}
    (hat : Commute a t)
    (ht : IsPElement p t) :
    IsPElement p (commutingElement hat) := by
  obtain ⟨k, hk⟩ := ht
  refine ⟨k, ?_⟩
  apply Subtype.ext
  exact hk

/-- The distinguished centralizer element commutes with every transported
commuting element. -/
theorem element_commute_commutingElement
    {a t : G} (hat : Commute a t) :
    Commute (element a) (commutingElement hat) := by
  exact
    (Subgroup.mem_center_iff.mp
      (element_mem_center a)
      (commutingElement hat)).symm

variable [Finite G]

/-- A canonical choice of Sylow subgroup in the singleton centralizer. -/
noncomputable def sylow
    (p : ℕ) [Fact p.Prime] (a : G) :
    Sylow p (group a) :=
  Classical.choice inferInstance

omit [Finite G] in
/-- The singleton centralizer has order dividing that of the ambient
finite group. -/
theorem card_group_dvd (a : G) :
    Nat.card (group a) ∣ Nat.card G :=
  Subgroup.card_subgroup_dvd_card (group a)

/-- The cyclic factor used in Bernstein's canonical elementary subgroup
inside the singleton centralizer has order dividing the order of the
original ambient group. -/
theorem cyclicPart_card_dvd_ambient
    (p : ℕ) [Fact p.Prime]
    {a : G} (ha : IsPRegular p a) :
    Nat.card
        (centralPRegularElementaryDecomposition
          (element a)
          (element_mem_center a)
          (element_isPRegular p ha)
          (sylow p a)).cyclicPart ∣
      Nat.card G := by
  exact
    (ClassFunction.centralPRegularCyclicPart_card_dvd
      (element a)
      (element_mem_center a)
      (element_isPRegular p ha)
      (sylow p a)).trans
        (card_group_dvd a)

end PRegularCentralizer
end McKayConjecture
