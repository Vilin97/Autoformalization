/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ActiveOrbitSylowRepresentative
import McKayConjecture.Character.ActiveOrbitTransport
import McKayConjecture.InductiveMcKay.NormalSubgroupIntermediateInertia

/-!
# Sylow-adapted representatives in Rossi's intermediate

Let `J = N Z(G)` and `H = J N_G(P)`.  The identity-on-elements character
equivalence between `J` and its internal copy in `H` transports a
`P`-fixed representative to a representative fixed by the canonical copy
of `P` in `H`.

This file records the construction in both directions.  It deliberately
does not assert that the resulting orbit is active: that fact comes from
the factor-extension equivalence on the corresponding inertia fibres.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupIntermediateRepresentatives

open CliffordPartition
open CliffordCorrespondence
open CliffordEquivalence
open NormalSubgroupIntermediateInertia

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G)
variable (N : Subgroup G) [N.Normal]

noncomputable local instance normalSubgroupIntermediateRepresentativesFintypeG :
    Fintype G :=
  Fintype.ofFinite G

noncomputable local instance normalSubgroupIntermediateRepresentativesFintypeH :
    Fintype (intermediate P N) :=
  Fintype.ofFinite (intermediate P N)

/-- The canonical Sylow subgroup of `J N_G(P)`. -/
abbrev intermediateSylow :
    Sylow p (intermediate P N) :=
  NormalSubgroupJoinCenterReduction.normalizerIntermediateSylow P N

/-- The source representative of an active `G`-orbit, chosen so that its
inertia group contains `P`. -/
abbrev sourceRepresentative
    (q : ActiveOrbit (joinCenter N) p) :
    PPrimeIrreducibleCharacter (joinCenter N) p :=
  q.pPrimeSylowRepresentative (joinCenter N) P

/-- Transport the Sylow-adapted source representative to the internal copy
of `J` in `J N_G(P)`. -/
abbrev forwardRepresentative
    (q : ActiveOrbit (joinCenter N) p) :
    PPrimeIrreducibleCharacter (internalJoinCenter P N) p :=
  internalCharacterEquiv P N (sourceRepresentative P N q)

@[simp]
theorem sourceRepresentative_orbit
    (q : ActiveOrbit (joinCenter N) p) :
    (Quotient.mk'' (sourceRepresentative P N q).1 :
        OrbitSpace (joinCenter N)) =
      q.1 :=
  q.mk_sylowRepresentative (joinCenter N) P

/-- The prescribed ambient Sylow subgroup fixes the forward source
representative. -/
theorem sylow_le_sourceInertia
    (q : ActiveOrbit (joinCenter N) p) :
    (P : Subgroup G) ≤
      sourceInertia N (sourceRepresentative P N q) :=
  q.sylow_le_inertia_sylowRepresentative
    (joinCenter N) P

/-- The canonical internal copy of `P` fixes the transported forward
representative. -/
theorem intermediateSylow_le_forwardInertia
    (q : ActiveOrbit (joinCenter N) p) :
    (intermediateSylow P N :
        Subgroup (intermediate P N)) ≤
      targetInertia P N (sourceRepresentative P N q) := by
  change
    (intermediateSylow P N :
        Subgroup (intermediate P N)) ≤
      IrreducibleCharacter.inertia
        (IrreducibleCharacter.internalNormal
          (joinCenter N) (intermediate P N))
        ((IrreducibleCharacter.internalNormalPPrimeEquiv
          (joinCenter N) (intermediate P N)
          (NormalSubgroupJoinCenterReduction.joinCenter_le_normalizerIntermediate
            P N)
          p)
          (sourceRepresentative P N q)).1
  rw [
    IrreducibleCharacter.inertia_internalNormalPPrimeEquiv_eq_comap
      (joinCenter N) (intermediate P N)
      (NormalSubgroupJoinCenterReduction.joinCenter_le_normalizerIntermediate
        P N)
      p
      (sourceRepresentative P N q)]
  intro x hx
  exact
    sylow_le_sourceInertia P N q hx

/-- The forward target inertia index is prime to `p`. -/
theorem forwardInertiaIndex_isPPrime
    (q : ActiveOrbit (joinCenter N) p) :
    ¬p ∣
      (targetInertia P N
        (sourceRepresentative P N q)).index := by
  intro hdiv
  exact
    (intermediateSylow P N).not_dvd_index
      (hdiv.trans
        (Subgroup.index_dvd_of_le
          (intermediateSylow_le_forwardInertia P N q)))

/-- A concrete prime-to-`p` character in the source inertia fibre at the
adapted representative. -/
def sourceInertiaFibreElement
    (q : ActiveOrbit (joinCenter N) p) :
    PPrimeIrreducibleCharactersOverInertia
      (joinCenter N) (sourceRepresentative P N q).1 p := by
  let horbit :
      (Quotient.mk'' q.1.out :
          OrbitSpace (joinCenter N)) =
        Quotient.mk'' (sourceRepresentative P N q).1 := by
    calc
      (Quotient.mk'' q.1.out :
          OrbitSpace (joinCenter N)) = q.1 :=
        Quotient.out_eq' q.1
      _ = Quotient.mk'' (sourceRepresentative P N q).1 :=
        (sourceRepresentative_orbit P N q).symm
  let block :
      PPrimeIrreducibleCharactersOverOrbit
        (joinCenter N) (sourceRepresentative P N q).1 p :=
    pPrimeOrbitBlockEquivOfQuotientMkEq
      (joinCenter N) horbit p q.2.some
  exact
    (cliffordPPrimeCorrespondence
      (joinCenter N) (sourceRepresentative P N q).1
      Fact.out
      (q.sylowRepresentative_inertia_index_isPPrime
        (joinCenter N) P)).symm block

/-- The adapted source inertia fibre is nonempty. -/
theorem sourceInertiaFibre_nonempty
    (q : ActiveOrbit (joinCenter N) p) :
    Nonempty
      (PPrimeIrreducibleCharactersOverInertia
        (joinCenter N) (sourceRepresentative P N q).1 p) :=
  ⟨sourceInertiaFibreElement P N q⟩

/-! ## The reverse adapted representative -/

/-- Choose a representative of an active orbit in the intermediate that is
fixed by the canonical internal copy of `P`. -/
abbrev targetRepresentative
    (r : ActiveOrbit (internalJoinCenter P N) p) :
    PPrimeIrreducibleCharacter (internalJoinCenter P N) p :=
  r.pPrimeSylowRepresentative
    (internalJoinCenter P N) (intermediateSylow P N)

/-- Pull the adapted intermediate representative back to `J`. -/
abbrev reverseRepresentative
    (r : ActiveOrbit (internalJoinCenter P N) p) :
    PPrimeIrreducibleCharacter (joinCenter N) p :=
  (internalCharacterEquiv P N).symm
    (targetRepresentative P N r)

@[simp]
theorem targetRepresentative_orbit
    (r : ActiveOrbit (internalJoinCenter P N) p) :
    (Quotient.mk'' (targetRepresentative P N r).1 :
        OrbitSpace (internalJoinCenter P N)) =
      r.1 :=
  r.mk_sylowRepresentative
    (internalJoinCenter P N) (intermediateSylow P N)

/-- The ambient Sylow subgroup fixes the pulled-back reverse
representative. -/
theorem sylow_le_reverseInertia
    (r : ActiveOrbit (internalJoinCenter P N) p) :
    (P : Subgroup G) ≤
      sourceInertia N (reverseRepresentative P N r) := by
  intro x hx
  let xH : intermediate P N :=
    ⟨x,
      NormalSubgroupJoinCenterReduction.sylow_le_normalizerIntermediate
        P N hx⟩
  have hxInternal :
      xH ∈
        (intermediateSylow P N :
          Subgroup (intermediate P N)) :=
    hx
  have hxTarget :
      xH ∈
        IrreducibleCharacter.inertia
          (internalJoinCenter P N)
          (targetRepresentative P N r).1 :=
    r.sylow_le_inertia_sylowRepresentative
      (internalJoinCenter P N)
      (intermediateSylow P N)
      hxInternal
  have hinertia :=
    IrreducibleCharacter.inertia_internalNormalPPrimeEquiv_eq_comap
      (joinCenter N) (intermediate P N)
      (NormalSubgroupJoinCenterReduction.joinCenter_le_normalizerIntermediate
        P N)
      p
      (reverseRepresentative P N r)
  have hcharacter :
      internalCharacterEquiv P N
          (reverseRepresentative P N r) =
        targetRepresentative P N r :=
    (internalCharacterEquiv P N).apply_symm_apply
      (targetRepresentative P N r)
  rw [hcharacter] at hinertia
  rw [hinertia] at hxTarget
  exact hxTarget

/-- The reverse source inertia index is prime to `p`. -/
theorem reverseInertiaIndex_isPPrime
    (r : ActiveOrbit (internalJoinCenter P N) p) :
    ¬p ∣
      (sourceInertia N
        (reverseRepresentative P N r)).index := by
  intro hdiv
  exact
    P.not_dvd_index
      (hdiv.trans
        (Subgroup.index_dvd_of_le
          (sylow_le_reverseInertia P N r)))

/-- The target representative in the reverse construction also has
prime-to-`p` inertia index, directly from its Sylow-adapted construction. -/
theorem targetRepresentative_inertiaIndex_isPPrime
    (r : ActiveOrbit (internalJoinCenter P N) p) :
    ¬p ∣
      (IrreducibleCharacter.inertia
        (internalJoinCenter P N)
        (targetRepresentative P N r).1).index :=
  r.sylowRepresentative_inertia_index_isPPrime
    (internalJoinCenter P N) (intermediateSylow P N)

/-- A concrete prime-to-`p` character in the intermediate inertia fibre at
the reverse adapted representative. -/
def targetInertiaFibreElement
    (r : ActiveOrbit (internalJoinCenter P N) p) :
    PPrimeIrreducibleCharactersOverInertia
      (internalJoinCenter P N)
      (targetRepresentative P N r).1 p := by
  let horbit :
      (Quotient.mk'' r.1.out :
          OrbitSpace (internalJoinCenter P N)) =
        Quotient.mk'' (targetRepresentative P N r).1 := by
    calc
      (Quotient.mk'' r.1.out :
          OrbitSpace (internalJoinCenter P N)) = r.1 :=
        Quotient.out_eq' r.1
      _ = Quotient.mk'' (targetRepresentative P N r).1 :=
        (targetRepresentative_orbit P N r).symm
  let block :
      PPrimeIrreducibleCharactersOverOrbit
        (internalJoinCenter P N)
        (targetRepresentative P N r).1 p :=
    pPrimeOrbitBlockEquivOfQuotientMkEq
      (internalJoinCenter P N) horbit p r.2.some
  exact
    (cliffordPPrimeCorrespondence
      (internalJoinCenter P N)
      (targetRepresentative P N r).1
      Fact.out
      (targetRepresentative_inertiaIndex_isPPrime P N r)).symm
      block

/-- The adapted intermediate inertia fibre is nonempty. -/
theorem targetInertiaFibre_nonempty
    (r : ActiveOrbit (internalJoinCenter P N) p) :
    Nonempty
      (PPrimeIrreducibleCharactersOverInertia
        (internalJoinCenter P N)
        (targetRepresentative P N r).1 p) :=
  ⟨targetInertiaFibreElement P N r⟩

end NormalSubgroupIntermediateRepresentatives
end InductiveMcKay
end McKayConjecture
