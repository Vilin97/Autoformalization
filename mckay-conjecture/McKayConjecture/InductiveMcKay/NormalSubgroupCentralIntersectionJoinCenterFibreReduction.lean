/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanExistence
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionJoinCenterAmbient
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizerAssemblyNaturality
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProjectiveCenterMismatch

/-!
# Proposition 4.5 from ordinary inertia-fibre equivalences

After adjoining the ambient center to the normal subgroup, every
ambient-central element belongs to both normal subgroups in the matched
Clifford assembly.  Consequently an arbitrary family of numerical
prime-to-`q` inertia-fibre equivalences automatically preserves the central
scalars required by the final assembly.

This file records that reduction directly for the canonical
Glauberman--Okuyama--Wajima correspondence.  In particular, the remaining
input is only an ordinary character equivalence on each matched inertia
fibre; it need not be packaged as a central character-triple isomorphism.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CliffordCorrespondence
open ComplementReduction
open GroupTheory
open KernelAssembly
open NormalSubgroupJoinCenterReduction

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- Equivariance is already a theorem of the canonical
Glauberman--Okuyama--Wajima correspondence, so a family of ordinary
inertia-fibre equivalences is all that remains to construct the numerical
ambient coherence. -/
def productAmbientGlaubermanTheorem44CoherenceOfInertiaFibreEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (fibreEquiv :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      ∀ theta :
          PPrimeIrreducibleCharacter
            (product S C) q,
        PPrimeIrreducibleCharactersOverInertia
            (product S C) theta.1 q ≃
          PPrimeIrreducibleCharactersOverInertia
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C
              (complementCharacterEquivOfGlauberman
                S C hcentral g) theta).1 q) :
    ProductAmbientTheorem44Coherence
      S C hgenerate
      (complementCharacterEquivOfGlauberman
        S C hcentral g) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    { characterEquiv_smul :=
        complementCharacterEquivOfGlauberman_internal_smul
          S C hcentral hgenerate g
      inertiaFibreEquiv := fibreEquiv }

/-- For the center-adjoined kernel, ordinary ambient coherence
automatically preserves central scalars. -/
theorem joinCenterKernel_glaubermanCoherence_preservesCentralScalars
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g :
      ProductGlaubermanCorrespondence
        S (joinCenterKernel C)
        (joinCenterKernel_inf_sylow_le_center
          S C hcentral))
    (c :
      ProductAmbientTheorem44Coherence
        S (joinCenterKernel C)
        (joinCenterKernel_sup_normalizer_eq_top
          S C hgenerate)
        (complementCharacterEquivOfGlauberman
          S (joinCenterKernel C)
          (joinCenterKernel_inf_sylow_le_center
            S C hcentral) g)) :
    c.PreservesCentralScalars
      S (joinCenterKernel C)
      (joinCenterKernel_sup_normalizer_eq_top
        S C hgenerate)
      (complementCharacterEquivOfGlauberman
        S (joinCenterKernel C)
        (joinCenterKernel_inf_sylow_le_center
          S C hcentral) g) := by
  let J := joinCenterKernel C
  let hJcentral :=
    joinCenterKernel_inf_sylow_le_center
      S C hcentral
  let hJgenerate :=
    joinCenterKernel_sup_normalizer_eq_top
      S C hgenerate
  letI : (product S J).Normal :=
    product_normal S J hJgenerate
  letI :
      (internalProductNormalizer S J).Normal :=
    internalProductNormalizer_normal S J hJgenerate
  let a :=
    c.toMatchedCentralFibreCliffordAssemblyData
      S J hJgenerate
      (complementCharacterEquivOfGlauberman
        S J hJcentral g)
  exact a.preservesCentralScalars_of_center_containing
    (fun (z : X) (hz : z ∈ Subgroup.center X) ↦
      center_le_joinCenterKernel_product S C hz)
    (fun (z : X) (hz : z ∈ Subgroup.center X)
        (hzNormalizer : z ∈ ambientNormalizer S) ↦
      center_mem_joinCenterKernel_internalProductNormalizer
        S C z hz hzNormalizer)
    (fun (theta :
          PPrimeIrreducibleCharacter (product S J) q)
        (z : X) (hz : z ∈ Subgroup.center X)
        (hzNormalizer : z ∈ ambientNormalizer S) ↦ by
    let zProduct : product S J :=
      ⟨z, center_le_joinCenterKernel_product S C hz⟩
    have hzProductCenter :
        zProduct ∈ Subgroup.center (product S J) := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact
        Subgroup.mem_center_iff.mp hz
          (x : X)
    let zCenter : Subgroup.center (product S J) :=
      ⟨zProduct, hzProductCenter⟩
    have hcross :=
      complementCharacterEquivOfGlauberman_internal_central_cross
        S J hJcentral g theta zCenter
    have htarget :
        productAmbientCenterInternalElement S J zCenter =
          ⟨⟨z, hzNormalizer⟩,
            center_mem_joinCenterKernel_internalProductNormalizer
              S C z hz hzNormalizer⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    have haCharacter :
        a.characterEquiv theta =
          internalTheorem44CharacterEquiv
            S J
            (complementCharacterEquivOfGlauberman
              S J hJcentral g) theta := by
      rfl
    rw [haCharacter]
    simpa [J, hJcentral, zProduct, zCenter, htarget] using hcross)

/-- Numerical Proposition 4.5 for the center-adjoined kernel from ordinary
inertia-fibre equivalences alone. -/
def centralScalarLocalCorrespondenceOfJoinCenterKernelGlaubermanCoherence
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g :
      ProductGlaubermanCorrespondence
        S (joinCenterKernel C)
        (joinCenterKernel_inf_sylow_le_center
          S C hcentral))
    (c :
      ProductAmbientTheorem44Coherence
        S (joinCenterKernel C)
        (joinCenterKernel_sup_normalizer_eq_top
          S C hgenerate)
        (complementCharacterEquivOfGlauberman
          S (joinCenterKernel C)
          (joinCenterKernel_inf_sylow_le_center
            S C hcentral) g)) :
    CentralScalarLocalCorrespondence S :=
  c.toCentralScalarLocalCorrespondence
    S (joinCenterKernel C)
    (joinCenterKernel_sup_normalizer_eq_top
      S C hgenerate)
    (complementCharacterEquivOfGlauberman
      S (joinCenterKernel C)
      (joinCenterKernel_inf_sylow_le_center
        S C hcentral) g)
    ((ProductAmbientTheorem44Coherence.hasCentralActionIntertwiners_iff_preservesCentralScalars
      S (joinCenterKernel C)
      (joinCenterKernel_sup_normalizer_eq_top
        S C hgenerate)
      (complementCharacterEquivOfGlauberman
        S (joinCenterKernel C)
        (joinCenterKernel_inf_sylow_le_center
          S C hcentral) g) c).mpr
      (joinCenterKernel_glaubermanCoherence_preservesCentralScalars
        S C hcentral hgenerate g c))

end Proposition45

/-- The exact remaining numerical input after adjoining the center:
ordinary prime-to-`q` equivalences on the matched inertia fibres. -/
def CentralScalarCentralIntersectionInertiaFibreEquivHypothesis
    (q : ℕ) [Fact q.Prime] : Prop :=
  ∀ (X : Type) [Group X] [Finite X]
    (S : Sylow q X) (C : Subgroup X)
    (hCnormal : C.Normal)
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤),
      letI : C.Normal := hCnormal
      ∀ g :
          ComplementReduction.ProductGlaubermanCorrespondence
            S C hcentral,
        letI : (product S C).Normal :=
          product_normal S C hgenerate
        letI :
            (internalProductNormalizer S C).Normal :=
          internalProductNormalizer_normal S C hgenerate
        ∀ theta :
            PPrimeIrreducibleCharacter
              (product S C) q,
          Nonempty
            (CliffordCorrespondence.PPrimeIrreducibleCharactersOverInertia
                (product S C) theta.1 q ≃
              CliffordCorrespondence.PPrimeIrreducibleCharactersOverInertia
                (internalProductNormalizer S C)
                (internalTheorem44CharacterEquiv
                  S C
                  (Proposition45.complementCharacterEquivOfGlauberman
                    S C hcentral g) theta).1 q)

/-- Ordinary inertia-fibre equivalences imply the complete
central-intersection reduction.  The proof applies them only after adjoining
the ambient center, where central-scalar preservation is automatic. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_inertiaFibreEquiv
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionInertiaFibreEquivHypothesis q) :
    CentralScalarCentralIntersectionReductionHypothesis q := by
  intro X _ _ S C hCnormal hcentral _hCnoncentral hgenerate
  letI : C.Normal := hCnormal
  let J :=
    Proposition45.joinCenterKernel C
  let hJcentral :=
    Proposition45.joinCenterKernel_inf_sylow_le_center
      S C hcentral
  let hJgenerate :=
    Proposition45.joinCenterKernel_sup_normalizer_eq_top
      S C hgenerate
  letI : J.Normal := inferInstance
  obtain ⟨g⟩ :=
    ComplementReduction.exists_productGlaubermanCorrespondence
      S J hJcentral
  let fibreEquiv :=
    fun theta ↦
      Classical.choice
        (h X S J inferInstance hJcentral hJgenerate g theta)
  let c :=
    Proposition45.productAmbientGlaubermanTheorem44CoherenceOfInertiaFibreEquiv
      S J hJcentral hJgenerate g fibreEquiv
  exact
    ⟨Proposition45.centralScalarLocalCorrespondenceOfJoinCenterKernelGlaubermanCoherence
      S C hcentral hgenerate g c⟩

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
