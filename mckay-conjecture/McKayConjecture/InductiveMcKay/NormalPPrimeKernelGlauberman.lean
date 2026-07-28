/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanCorrespondence
import McKayConjecture.Character.ActiveExtension
import McKayConjecture.Character.PGroupQuotientGallagher
import McKayConjecture.InductiveMcKay.CentralIntersectionKernelNumerical

/-!
# Active Clifford orbits from the Glauberman correspondence

For a normal `p′`-kernel `K` with `G = KP`, the active kernel characters
are invariant.  The classical Glauberman correspondence therefore gives
the expected matching with characters of `C_K(P)`, once the two elementary
activation statements are supplied:

* invariant characters of the normal Hall subgroup are active (canonical
  coprime extension); and
* characters of `C_K(P)` are active in `C_K(P) × P`.

This file performs the rest of the construction and produces the actual
equivalence of active Clifford orbit spaces.  The activation hypotheses are
strictly below the final McKay bijection and are separated from the
Okuyama--Wajima cardinal comparison of characters above matched kernel
characters.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalPPrimeKernelGlauberman

open CliffordPartition
open CentralIntersectionKernelAssembly

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K P : Subgroup G) [K.Normal]

noncomputable local instance normalPPrimeKernelGlaubermanFintypeG :
    Fintype G :=
  Fintype.ofFinite G

noncomputable local instance normalPPrimeKernelGlaubermanFintypeH :
    Fintype (localNormalizer P) :=
  Fintype.ofFinite (localNormalizer P)

/-- Explicit invariant extensions across the `p`-group quotient.

For the intended normal Hall `p′`-kernel this is the canonical coprime
extension theorem.  Keeping the extensions themselves makes the Gallagher
coordinates on every fibre available, instead of remembering only that the
corresponding Clifford orbit is active. -/
structure InvariantPPrimeExtensionData
    (s : CentralIntersectionSetup (p := p) K P) where
  /-- A selected prime-to-`p` extension of every `P`-invariant kernel
  character. -/
  extension :
    PInvariantPPrimeIrreducibleCharacter K P p →
      PPrimeIrreducibleCharacter G p
  /-- The selected character restricts to the given invariant kernel
  character. -/
  isExtension :
    ∀ θ : PInvariantPPrimeIrreducibleCharacter K P p,
      IrreducibleCharacter.IsExtensionAlong
        K.subtype θ.1.1 (extension θ).1

namespace InvariantPPrimeExtensionData

variable {K P}
variable {s : CentralIntersectionSetup (p := p) K P}

/-- A selected invariant extension is a concrete witness that the source
kernel character belongs to an active prime-to-`p` Clifford orbit. -/
theorem source_active
    (d : InvariantPPrimeExtensionData K P s)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    IsActivePPrimeCharacter K θ.1 :=
  CliffordPartition.isActivePPrimeCharacter_of_isExtension
    K θ.1 (d.extension θ) (d.isExtension θ)

/-- Gallagher's correspondence above an invariant kernel character, with
the quotient parameter exposed as an actual multiplicative linear
character.  The fact that the quotient has no nonlinear `p′`-degree
characters is supplied by `pGroupPPrimeLinearEquiv`. -/
def linearGallagherEquiv
    (d : InvariantPPrimeExtensionData K P s)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    ((G ⧸ K) →* ℂˣ) ≃
      CliffordCorrespondence.PPrimeIrreducibleCharactersOverAlong
        K.subtype θ.1.1 p :=
  IrreducibleCharacter.gallagherLinearCorrespondenceOfPGroupQuotient
    K s.quotientPGroup (d.isExtension θ) θ.1.2

end InvariantPPrimeExtensionData

/-- The two activation facts used when passing from the classical
Glauberman correspondence to active Clifford orbits.  The target is
written using an explicit relabelling of the internal local kernel with
the ambient fixed-point subgroup. -/
structure ActivationData
    (s : CentralIntersectionSetup (p := p) K P)
    (e :
      internalKernelNormalizer K P ≃*
        coprimeFixedPoints K P) : Prop where
  /-- A `P`-invariant kernel character lies below a prime-to-`p`
  ambient character.  For a normal Hall subgroup this is canonical
  coprime extendibility. -/
  source_active :
    ∀ θ : PInvariantPPrimeIrreducibleCharacter K P p,
      IsActivePPrimeCharacter K θ.1
  /-- Every fixed-point character, transported to the internal local
  kernel, lies below a prime-to-`p` local character.  In the intended
  direct-product coordinates this is extension by the trivial character
  of `P`. -/
  target_active :
    ∀ φ :
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints K P) p,
      IsActivePPrimeCharacter
        (internalKernelNormalizer K P)
        (IrreducibleCharacter.pPrimeComapEquiv p e φ)

namespace ActivationData

variable {K P}
variable {s : CentralIntersectionSetup (p := p) K P}
variable {e :
  internalKernelNormalizer K P ≃*
    coprimeFixedPoints K P}

/-- Build the source half of the activation data from genuine invariant
extensions.  Only the target direct-product activation remains to be
supplied. -/
theorem ofInvariantExtensions
    (d : InvariantPPrimeExtensionData K P s)
    (htarget :
      ∀ φ :
        PPrimeIrreducibleCharacter
          (coprimeFixedPoints K P) p,
        IsActivePPrimeCharacter
          (internalKernelNormalizer K P)
          (IrreducibleCharacter.pPrimeComapEquiv p e φ)) :
    ActivationData K P s e where
  source_active := d.source_active
  target_active := htarget

/-- Active source characters are exactly the invariant characters relevant
to the Glauberman correspondence. -/
def sourceActiveEquivInvariant
    (a : ActivationData K P s e) :
    ActivePPrimeIrreducibleCharacter K p ≃
      PInvariantPPrimeIrreducibleCharacter K P p where
  toFun θ :=
    ⟨θ.1, by
      rw [s.activeKernel_inertia_eq_top
        K P θ.1 θ.2]
      exact le_top⟩
  invFun θ := ⟨θ.1, a.source_active θ⟩
  left_inv θ := by
    apply Subtype.ext
    rfl
  right_inv θ := by
    apply Subtype.ext
    rfl

@[simp]
theorem sourceActiveEquivInvariant_apply_coe
    (a : ActivationData K P s e)
    (θ : ActivePPrimeIrreducibleCharacter K p) :
    (a.sourceActiveEquivInvariant θ).1 = θ.1 :=
  rfl

/-- Fixed-point characters are exactly the active local-kernel characters,
after relabelling along `e`. -/
def fixedPointsEquivTargetActive
    (a : ActivationData K P s e) :
    PPrimeIrreducibleCharacter
          (coprimeFixedPoints K P) p ≃
      ActivePPrimeIrreducibleCharacter
        (internalKernelNormalizer K P) p where
  toFun φ :=
    ⟨IrreducibleCharacter.pPrimeComapEquiv p e φ,
      a.target_active φ⟩
  invFun ψ :=
    (IrreducibleCharacter.pPrimeComapEquiv p e).symm ψ.1
  left_inv φ := by
    exact
      (IrreducibleCharacter.pPrimeComapEquiv p e).symm_apply_apply φ
  right_inv ψ := by
    apply Subtype.ext
    exact
      (IrreducibleCharacter.pPrimeComapEquiv p e).apply_symm_apply ψ.1

@[simp]
theorem fixedPointsEquivTargetActive_apply_coe
    (a : ActivationData K P s e)
    (φ :
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints K P) p) :
    (a.fixedPointsEquivTargetActive φ).1 =
      IrreducibleCharacter.pPrimeComapEquiv p e φ :=
  rfl

/-- The active-character equivalence obtained from Glauberman plus the two
activation facts. -/
def activeCharacterEquiv
    (a : ActivationData K P s e)
    (d : GlaubermanCorrespondence K P p) :
    ActivePPrimeIrreducibleCharacter K p ≃
      ActivePPrimeIrreducibleCharacter
        (internalKernelNormalizer K P) p :=
  a.sourceActiveEquivInvariant |>.trans <|
    d.characterEquiv.trans
      a.fixedPointsEquivTargetActive

@[simp]
theorem activeCharacterEquiv_apply_coe
    (a : ActivationData K P s e)
    (d : GlaubermanCorrespondence K P p)
    (θ : ActivePPrimeIrreducibleCharacter K p) :
    (a.activeCharacterEquiv d θ).1 =
      IrreducibleCharacter.pPrimeComapEquiv p e
        (d.characterEquiv
          (a.sourceActiveEquivInvariant θ)) :=
  rfl

omit [Fact p.Prime] in
/-- A character whose inertia group is the whole ambient group is fixed by
every ambient conjugation. -/
theorem active_smul_eq_of_inertia_eq_top
    {A : Type} [Group A]
    (N : Subgroup A) [N.Normal]
    (θ : ActivePPrimeIrreducibleCharacter N p)
    (hinertia :
      IrreducibleCharacter.inertia N θ.1.1 = ⊤)
    (g : A) :
    g • θ = θ := by
  apply Subtype.ext
  apply Subtype.ext
  exact
    (IrreducibleCharacter.mem_inertia_iff
      N θ.1.1 g).mp
      (by rw [hinertia]; exact Subgroup.mem_top g)

/-- The active-character equivalence is equivariant for the action of the
local normalizer.  This is formal because both active characters have full
inertia in their respective ambient groups. -/
theorem activeCharacterEquiv_map_smul
    (a : ActivationData K P s e)
    (d : GlaubermanCorrespondence K P p)
    (h : localNormalizer P)
    (θ : ActivePPrimeIrreducibleCharacter K p) :
    a.activeCharacterEquiv d (h • θ) =
      h • a.activeCharacterEquiv d θ := by
  have hsource : h • θ = θ :=
    active_smul_eq_of_inertia_eq_top
      K θ
      (s.activeKernel_inertia_eq_top
        K P θ.1 θ.2)
      (h : G)
  have htarget :
      h • a.activeCharacterEquiv d θ =
        a.activeCharacterEquiv d θ :=
    active_smul_eq_of_inertia_eq_top
      (internalKernelNormalizer K P)
      (a.activeCharacterEquiv d θ)
      (s.activeLocalKernel_inertia_eq_top
        K P
        (a.activeCharacterEquiv d θ).1
        (a.activeCharacterEquiv d θ).2)
      h
  rw [hsource, htarget]

/-- Equivariant equivalences of the exact active-character subtypes descend
to active Clifford orbit spaces. -/
def activeOrbitEquiv
    (a : ActivationData K P s e)
    (d : GlaubermanCorrespondence K P p) :
    ActiveOrbit K p ≃
      ActiveOrbit (internalKernelNormalizer K P) p :=
  (activeOrbitEquivActivePPrimeOrbitSpace K p).trans <|
    (activePPrimeOrbitQuotientEquivSubgroupOfSupEqTop
      K (localNormalizer P) (p := p)
      (kernel_sup_localNormalizer_eq_top
        K P s.generate)).trans <|
      (McKayConjecture.GroupTheory.equivariantOrbitQuotientEquiv
        (a.activeCharacterEquiv d)
        (a.activeCharacterEquiv_map_smul d)).trans <|
        (activeOrbitEquivActivePPrimeOrbitSpace
          (internalKernelNormalizer K P) p).symm

@[simp]
theorem activeOrbitEquiv_apply_coe
    (a : ActivationData K P s e)
    (d : GlaubermanCorrespondence K P p)
    (q : ActiveOrbit K p) :
    (a.activeOrbitEquiv d q).1 =
      (Quotient.mk''
        ((a.activeCharacterEquiv d
          (activePPrimeOut K q)).1.1) :
        OrbitSpace (internalKernelNormalizer K P)) :=
  rfl

end ActivationData
end NormalPPrimeKernelGlauberman
end InductiveMcKay
end McKayConjecture
