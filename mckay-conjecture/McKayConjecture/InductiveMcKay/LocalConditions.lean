/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.Condition
import McKayConjecture.InductiveMcKay.EquivariantExtensionMap
import McKayConjecture.InductiveMcKay.StableTransversal

/-!
# Abstract local conditions A and B

This file packages the group-independent content of the local hypotheses
usually denoted `A(d)` and `B(d)`.

* `LocalConditionA` is a stable orbit transversal together with inertia
  extensions for its representatives.
* `LocalConditionB` consists of explicit extension maps for two normal
  subgroups of a common overgroup; the second map is equivariant for an
  outer action and compatible with a twist action.

These hypotheses do not, by themselves, construct the global/local
character bijection or its projective character-triple witnesses.  The
finite-reductive local criterion supplies that additional mathematical
step.  `LocalCriterionBridge` records its exact output, indexed by the
particular `A`- and `B`-data used to prove it.  Only after this bridge is
given does `LocalCriterionBridge.assemble` produce
`LocalInductiveMcKayData`.
-/

noncomputable section

universe u v w x

namespace McKayConjecture.InductiveMcKay

open McKayConjecture
open McKayConjecture.IrreducibleCharacter

/-! ## Local condition A -/

section ConditionA

variable {K : Type u} [Group K]
variable (H : Subgroup K) [H.Normal]
variable (M : Type v) (A : Type w)
variable [Group M] [Group A]
variable [MulAction M (IrreducibleCharacter H)]
variable [MulAction A (IrreducibleCharacter H)]

/-- Abstract `A(d)`-data: an outer-stable orbit transversal in `Irr(H)`
whose representatives extend to their inertia groups in `K`. -/
structure LocalConditionA where
  /-- The stable transversal and all of its chosen extension witnesses. -/
  transversal : ExtendibleStableCharacterTransversal H M A

/-- Existence form of `LocalConditionA`. -/
def HasLocalConditionA : Prop :=
  Nonempty (LocalConditionA H M A)

namespace LocalConditionA

variable {H M A}

/-- Every orbit contains a selected character with a certified inertia
extension. -/
theorem exists_smul_extension
    (d : LocalConditionA H M A)
    (χ : IrreducibleCharacter H) :
    ∃ m : M,
      ∃ ψ : IrreducibleCharacter (inertia H (m • χ)),
        m • χ ∈ d.transversal.representatives ∧
          IsInertiaExtension H (m • χ) ψ :=
  d.transversal.exists_smul_extension χ

/-- Condition `A` implies maximal extendibility on its representative set,
and makes no assertion about nonrepresentatives. -/
theorem representative_extendible
    (d : LocalConditionA H M A)
    (χ : IrreducibleCharacter H)
    (hχ : χ ∈ d.transversal.representatives) :
    ∃ ψ : IrreducibleCharacter (inertia H χ),
      IsInertiaExtension H χ ψ :=
  ⟨d.transversal.extensionAt χ hχ,
    d.transversal.extensionAt_isExtension χ hχ⟩

end LocalConditionA

end ConditionA

/-! ## Local condition B -/

section ConditionB

variable {K : Type u} [Group K]
variable (N C : Subgroup K) [N.Normal] [C.Normal]
variable {A : Type v} {T : Type w}
variable [Group A] [Group T]
variable [MulAction A (IrreducibleCharacter C)]
variable [MulAction A (InertiaCharacter C)]
variable [MulAction T (IrreducibleCharacter C)]
variable [MulAction T (InertiaCharacter C)]

/-- Abstract `B(d)`-data for two normal subgroups `N` and `C` of a common
overgroup `K`.

The extension map for `N` records its maximal extendibility.  The extension
map for `C` additionally records outer equivariance and compatibility with
the specified twist action. -/
structure LocalConditionB
    (outerLiesOver : InertiaActionLiesOver C (A := A))
    (twistLiesOver : InertiaActionLiesOver C (A := T)) where
  /-- Simultaneous extensions witnessing maximal extendibility for `N`. -/
  normalizerExtensionMap : ExtensionMap N
  /-- The equivariant and twist-compatible extension map for `C`. -/
  centralizerExtensionMap :
    TwistCompatibleEquivariantExtensionMap C
      outerLiesOver twistLiesOver

/-- Existence form of `LocalConditionB`. -/
def HasLocalConditionB
    (outerLiesOver : InertiaActionLiesOver C (A := A))
    (twistLiesOver : InertiaActionLiesOver C (A := T)) : Prop :=
  Nonempty (LocalConditionB N C outerLiesOver twistLiesOver)

namespace LocalConditionB

variable {N C}
variable {outerLiesOver : InertiaActionLiesOver C (A := A)}
variable {twistLiesOver : InertiaActionLiesOver C (A := T)}

/-- The first extension map gives maximal extendibility for `N ⫳ K`. -/
theorem normalizer_maximallyExtendible
    (d : LocalConditionB N C outerLiesOver twistLiesOver) :
    IsMaximallyExtendible N :=
  d.normalizerExtensionMap.maximallyExtendible

/-- The twist-compatible extension map gives maximal extendibility for
`C ⫳ K` after forgetting both compatibility laws. -/
theorem centralizer_maximallyExtendible
    (d : LocalConditionB N C outerLiesOver twistLiesOver) :
    IsMaximallyExtendible C :=
  d.centralizerExtensionMap.maximallyExtendible

/-- Retain the outer-equivariant extension map for `C` and forget only
twist compatibility. -/
def centralizerOuterExtensionMap
    (d : LocalConditionB N C outerLiesOver twistLiesOver) :
    EquivariantExtensionMap C outerLiesOver :=
  d.centralizerExtensionMap.forgetTwists

/-- Retain the twist-equivariant extension map for `C` and forget only the
outer compatibility law. -/
def centralizerTwistExtensionMap
    (d : LocalConditionB N C outerLiesOver twistLiesOver) :
    EquivariantExtensionMap C twistLiesOver :=
  d.centralizerExtensionMap.toTwistEquivariantExtensionMap

end LocalConditionB

end ConditionB

/-! ## The explicit assembly boundary -/

section Assembly

variable {G : Type u} [Group G] [Finite G] {p : ℕ}
variable (P : Sylow p G)

/-- The extra output required from a proof of the finite-reductive local
criterion.

The type is indexed by the actual condition-`A` and condition-`B` witnesses
used in that proof.  The indices can be any concrete instantiations of the
abstract structures above.  The fields make the two genuinely new
obligations explicit: an equivariant local correspondence and one complete
character-triple witness for every source character. -/
structure LocalCriterionBridge
    {ConditionAData : Type v} {ConditionBData : Type w}
    (conditionA : ConditionAData) (conditionB : ConditionBData) where
  /-- The global/local `p'`-character correspondence, including its
  intermediate subgroup and automorphism equivariance. -/
  correspondence : EquivariantLocalCorrespondence P
  /-- The projective central-isomorphism witness for every paired
  character. -/
  tripleCompatible :
    ∀ χ : PPrimeIrreducibleCharacter G p,
      correspondence.TripleCompatible χ

namespace LocalCriterionBridge

variable {P}
variable {ConditionAData : Type v} {ConditionBData : Type w}
variable {conditionA : ConditionAData} {conditionB : ConditionBData}

/-- Assemble the exact existing definition of the local inductive McKay
condition from the explicit output of the local criterion. -/
def assemble
    (d : LocalCriterionBridge P conditionA conditionB) :
    LocalInductiveMcKayData P where
  toEquivariantLocalCorrespondence := d.correspondence
  triple_compatible := d.tripleCompatible

@[simp]
theorem assemble_toEquivariant
    (d : LocalCriterionBridge P conditionA conditionB) :
    d.assemble.toEquivariant = d.correspondence :=
  rfl

@[simp]
theorem assemble_triple_compatible
    (d : LocalCriterionBridge P conditionA conditionB)
    (χ : PPrimeIrreducibleCharacter G p) :
    d.assemble.triple_compatible χ = d.tripleCompatible χ :=
  rfl

end LocalCriterionBridge

end Assembly

end McKayConjecture.InductiveMcKay
