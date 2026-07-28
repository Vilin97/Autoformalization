/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedCoprimeLinearization

/-!
# Extension from normal Hall prime-to-p subgroups

An invariant irreducible character of a normal `p'`-subgroup extends across
a `p`-group quotient. The construction is representation-theoretic: an
associated projective lift is given a finite factor set, the coprime central
extension is split by Schur--Zassenhaus, and the resulting factor-one lift is
packaged as an irreducible character.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A normal-subgroup character with full inertia defines a character
triple on the ambient group. -/
def ofInertiaTop
    (N : Subgroup G) [N.Normal]
    (chi : IrreducibleCharacter N)
    (hinertia :
      IrreducibleCharacter.inertia N chi = ⊤) :
    CharacterTriple G where
  normalSubgroup := N
  isNormal := inferInstance
  character := chi
  isInvariant := by
    intro g x
    have hg :
        g⁻¹ ∈ IrreducibleCharacter.inertia N chi := by
      rw [hinertia]
      exact Subgroup.mem_top _
    have hfix :
        IrreducibleCharacter.conjBy N g⁻¹ chi = chi :=
      (IrreducibleCharacter.mem_inertia_iff
        N chi g⁻¹).mp hg
    have hvalue :=
      congrArg
        (fun eta : IrreducibleCharacter N ↦ eta.values x)
        hfix
    rw [IrreducibleCharacter.conjBy_values] at hvalue
    convert hvalue using 1
    apply congrArg chi.values
    apply Subtype.ext
    simp [conjugateNormalElement]

@[simp]
theorem ofInertiaTop_normalSubgroup
    (N : Subgroup G) [N.Normal]
    (chi : IrreducibleCharacter N)
    (hinertia :
      IrreducibleCharacter.inertia N chi = ⊤) :
    (ofInertiaTop N chi hinertia).normalSubgroup = N :=
  rfl

@[simp]
theorem ofInertiaTop_character
    (N : Subgroup G) [N.Normal]
    (chi : IrreducibleCharacter N)
    (hinertia :
      IrreducibleCharacter.inertia N chi = ⊤) :
    (ofInertiaTop N chi hinertia).character = chi :=
  rfl

/-- Coprime extension for an invariant character of a normal Hall
`p'`-subgroup. -/
theorem exists_pPrime_extension_of_normalHall
    (T : CharacterTriple G)
    (hN :
      GroupTheory.IsPPrimeGroup p T.normalSubgroup)
    (hquotient :
      IsPGroup p (G ⧸ T.normalSubgroup))
    (hdegree :
      T.character.IsPPrimeDegree p) :
    ∃ psi : PPrimeIrreducibleCharacter G p,
      IrreducibleCharacter.IsExtensionAlong
        T.normalSubgroup.subtype T.character psi.1 := by
  let R :=
    AssociatedGeneralExistence.associated T
  have hrealizationDegree :
      ¬p ∣ Module.finrank ℂ T.character.realization := by
    rw [T.character.realization_finrank]
    exact hdegree
  obtain ⟨Q, hQassociated, hQfactor⟩ :=
    R.exists_factorOne_associated_of_coprime
      hN hquotient hrealizationDegree
  let S : AssociatedProjectiveRepresentation
      T T.character.realization Q :=
    Classical.choice hQassociated
  let psi : IrreducibleCharacter G :=
    S.extensionCharacterOfFactorOne hQfactor
  have hpsiPPrime : psi.IsPPrimeDegree p := by
    change ¬p ∣ psi.degree
    rw [show psi.degree =
        Module.finrank ℂ T.character.realization from
      S.extensionCharacterOfFactorOne_degree hQfactor]
    exact hrealizationDegree
  exact
    ⟨⟨psi, hpsiPPrime⟩,
      S.extensionCharacterOfFactorOne_isExtension hQfactor⟩

/-- Coprime extension stated directly for a normal subgroup character with
full inertia. -/
theorem exists_pPrime_extension_of_normalHall_inertiaTop
    (N : Subgroup G) [N.Normal]
    (chi : IrreducibleCharacter N)
    (hinertia :
      IrreducibleCharacter.inertia N chi = ⊤)
    (hN : GroupTheory.IsPPrimeGroup p N)
    (hquotient : IsPGroup p (G ⧸ N))
    (hdegree : chi.IsPPrimeDegree p) :
    ∃ psi : PPrimeIrreducibleCharacter G p,
      IrreducibleCharacter.IsExtensionAlong
        N.subtype chi psi.1 := by
  exact
    exists_pPrime_extension_of_normalHall
      (ofInertiaTop N chi hinertia)
      hN hquotient hdegree

end CharacterTriple
end McKayConjecture
