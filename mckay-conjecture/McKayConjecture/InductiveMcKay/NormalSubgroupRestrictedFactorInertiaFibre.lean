/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupIntermediateOrbitAssembly
import McKayConjecture.InductiveMcKay.NormalSubgroupRestrictedFactorInertiaTransport
import McKayConjecture.InductiveMcKay.NormalSubgroupRestrictedFactorScalarFibre

/-!
# Fixed restricted factors and ordinary inertia fibres

For a `P`-fixed character of `N Z(G)`, the factor-extension argument
canonically reaches the inverse-coefficient fibre in the fixed pulled-back
extension of the restricted inertia triple.  The fixed-data character
correspondence first converts this fibre back to ordinary characters of that
literal restricted triple.  Simultaneous identity-on-elements transport of
the ambient group and normal copy then identifies it with the ordinary target
inertia fibre in `N Z(G) N_G(P)`.

The constructors below package, respectively, the full and scalar-local
central-index induction hypotheses as the `InertiaFibreData` needed by the
active-orbit assembly.  No equality with a freshly determinant-normalized
factor set is used.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupRestrictedFactorInertiaFibre

open CharacterTriple
open CliffordCorrespondence
open GroupTheory
open NormalSubgroupAssociatedFactorFibre
open NormalSubgroupFactorNormalizerFibre
open NormalSubgroupInertiaFactorDescent
open NormalSubgroupIntermediateInertia
open NormalSubgroupIntermediateOrbitAssembly
open NormalSubgroupRestrictedFactorFibre
open NormalSubgroupRestrictedFactorInertiaTransport

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G)
variable (N : Subgroup G) [N.Normal]

/-- The descent package from the fixed pulled-back factor extension to the
ordinary target inertia fibre. -/
structure FixedRestrictedFactorInertiaDescent where
  fibreEquiv :
    ∀ (θ : PPrimeIrreducibleCharacter
        (NormalSubgroupIntermediateInertia.joinCenter N) p)
      (hP :
        (P : Subgroup G) ≤
          NormalSubgroupIntermediateInertia.sourceInertia N θ),
      RestrictedPPrimeInverseCoefficientFibre
          (inertiaTriple N θ.1)
          (inertiaQuotientSylow N P θ.1 hP) ≃
        PPrimeIrreducibleCharactersOverInertia
          (NormalSubgroupIntermediateInertia.internalJoinCenter P N)
          (NormalSubgroupIntermediateInertia.internalCharacterEquiv
            P N θ).1 p

/-- The literal fixed restriction and identity-on-elements inertia transport
supply the required descent without any normalization-choice hypothesis. -/
def fixedRestrictedFactorInertiaDescent :
    FixedRestrictedFactorInertiaDescent P N where
  fibreEquiv θ hP :=
    restrictedInverseCoefficientFibreEquivTargetInertia
      P N θ hP

/-- The normal character in the inertia triple has prime-to-`p` degree
whenever the original character does. -/
theorem inertiaTriple_character_isPPrimeDegree
    (θ : PPrimeIrreducibleCharacter
      (NormalSubgroupIntermediateInertia.joinCenter N) p) :
    (inertiaTriple N θ.1).character.IsPPrimeDegree p := by
  change ¬p ∣
    (CliffordEquivalence.inertiaCopyCharacter
      (NormalSubgroupIntermediateInertia.joinCenter N) θ.1).degree
  simpa only [CliffordEquivalence.inertiaCopyCharacter,
    IrreducibleCharacter.comap_degree,
    IrreducibleCharacter.IsPPrimeDegree] using θ.2

/-- Full central-index induction plus fixed-factor descent supplies all
ordinary inertia-fibre equivalences needed by the orbit assembly. -/
def inertiaFibreDataOfCentralIndexIH
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex G →
          ∀ Q : Sylow p Y,
            Nonempty (LocalInductiveMcKayData Q))
    (hNnoncentral : ¬N ≤ Subgroup.center G) :
    InertiaFibreData P N where
  fibreEquiv θ hP :=
    (CharacterTriple.pPrimeIrreducibleCharactersOverInertiaEquivTriple
      (NormalSubgroupIntermediateInertia.joinCenter N) θ.1 p).trans
      ((restrictedPPrimeCharacterEquivOfCentralIndexIH
        ih
        (inertiaTriple N θ.1)
        (inertiaTriple_character_isPPrimeDegree N θ)
        (centralIndex_inertiaFactorExtension_lt
          N hNnoncentral θ.1)
        (inertiaQuotientSylow N P θ.1 hP)).trans
        ((fixedRestrictedFactorInertiaDescent
          P N).fibreEquiv θ hP))

/-- The scalar-local central-index induction hypothesis is already
sufficient for the ordinary inertia-fibre data once fixed-factor descent is
available. -/
def inertiaFibreDataOfCentralScalarLocalIH
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex G →
          ∀ Q : Sylow p Y,
            Nonempty (CentralScalarLocalCorrespondence Q))
    (hNnoncentral : ¬N ≤ Subgroup.center G) :
    InertiaFibreData P N where
  fibreEquiv θ hP :=
    (CharacterTriple.pPrimeIrreducibleCharactersOverInertiaEquivTriple
      (NormalSubgroupIntermediateInertia.joinCenter N) θ.1 p).trans
      ((restrictedPPrimeCharacterEquivOfCentralScalarLocalIH
        ih
        (inertiaTriple N θ.1)
        (inertiaTriple_character_isPPrimeDegree N θ)
        (centralIndex_inertiaFactorExtension_lt
          N hNnoncentral θ.1)
        (inertiaQuotientSylow N P θ.1 hP)).trans
        ((fixedRestrictedFactorInertiaDescent
          P N).fibreEquiv θ hP))

/-- The resulting numerical Proposition-4.2 correspondence, with Sylow
fixed-point fusion discharged by the canonical orbit-assembly theorem. -/
def assembledPPrimeEquivOfCentralScalarLocalIH
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex G →
          ∀ Q : Sylow p Y,
            Nonempty (CentralScalarLocalCorrespondence Q))
    (hNnoncentral : ¬N ≤ Subgroup.center G) :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter
        (NormalSubgroupIntermediateInertia.intermediate P N) p :=
  NormalSubgroupIntermediateOrbitAssembly.InertiaFibreData.assembledPPrimeEquivCanonical
    P N
      (inertiaFibreDataOfCentralScalarLocalIH
        P N ih hNnoncentral)

end NormalSubgroupRestrictedFactorInertiaFibre
end InductiveMcKay
end McKayConjecture
