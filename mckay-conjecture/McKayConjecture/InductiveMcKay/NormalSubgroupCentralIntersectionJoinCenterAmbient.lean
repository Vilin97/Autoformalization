/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.MatchedCentralFibreCenterContaining
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45

/-!
# The join-center variant of the Proposition-4.5 ambient lift

For `C ◁ X` with `C ∩ S ≤ Z(X)`, replace `C` by `C Z(X)`.  The new
kernel still has central Sylow intersection, while the Theorem-4.4 source
`(C Z(X))S` and its internal normalizer both contain the relevant copies of
`Z(X)`.

Consequently, once numerical ambient inertia-fibre equivalences have been
constructed, no further central-action coherence is required: the
central-scalar identity of the Theorem-4.4 correspondence automatically
passes through every inertia fibre.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CliffordCorrespondence
open GroupTheory
open KernelAssembly
open NormalSubgroupJoinCenterReduction

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The original kernel with the ambient center adjoined. -/
abbrev joinCenterKernel : Subgroup X :=
  joinCenter C

/-- The join-center kernel remains normal. -/
instance joinCenterKernel_normal :
    (joinCenterKernel C).Normal :=
  inferInstance

/-- Adjoining the center preserves the central Sylow-intersection
hypothesis. -/
theorem joinCenterKernel_inf_sylow_le_center
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    joinCenterKernel C ⊓ (S : Subgroup X) ≤
      Subgroup.center X :=
  joinCenter_inf_sylow_le_center
    S C hcentral

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- The join-center kernel and the ambient Sylow normalizer still generate
the ambient group. -/
theorem joinCenterKernel_sup_normalizer_eq_top
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤) :
    joinCenterKernel C ⊔
        Subgroup.normalizer (S : Set X) =
      ⊤ := by
  apply top_unique
  rw [← hgenerate]
  exact
    sup_le
      (le_sup_left.trans le_sup_left)
      le_sup_right

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- The ambient center lies in the Theorem-4.4 source built from the
join-center kernel. -/
theorem center_le_joinCenterKernel_product :
    Subgroup.center X ≤
      product S (joinCenterKernel C) :=
  (center_le_joinCenter C).trans le_sup_left

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- The canonical copy of every ambient-central element in the Sylow
normalizer belongs to the internal Theorem-4.4 target for the join-center
kernel. -/
theorem center_mem_joinCenterKernel_internalProductNormalizer
    (z : X) (hzcentral : z ∈ Subgroup.center X)
    (hzNormalizer :
      z ∈ ambientNormalizer S) :
    (⟨z, hzNormalizer⟩ : ambientNormalizer S) ∈
      internalProductNormalizer S (joinCenterKernel C) :=
  center_le_joinCenterKernel_product S C hzcentral

/-- The transported Theorem-4.4 equivalence for the join-center kernel
preserves normalized values of ambient-central elements. -/
theorem joinCenterKernel_internalTheorem44_central_cross
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (d :
      ProductActiveKernelCentralFibreData
        S (joinCenterKernel C)
          (joinCenterKernel_inf_sylow_le_center
            S C hcentral))
    (θ :
      PPrimeIrreducibleCharacter
        (product S (joinCenterKernel C)) q)
    (z : X) (hzcentral : z ∈ Subgroup.center X)
    (hzNormalizer : z ∈ ambientNormalizer S) :
    θ.1.values
          ⟨z, center_le_joinCenterKernel_product S C hzcentral⟩ *
        (((internalTheorem44CentralFibreCharacterEquiv
          S (joinCenterKernel C)
          (joinCenterKernel_inf_sylow_le_center
            S C hcentral) d θ).1.degree : ℂ)) =
      (internalTheorem44CentralFibreCharacterEquiv
          S (joinCenterKernel C)
          (joinCenterKernel_inf_sylow_le_center
            S C hcentral) d θ).1.values
        ⟨⟨z, hzNormalizer⟩,
          center_mem_joinCenterKernel_internalProductNormalizer
            S C z hzcentral hzNormalizer⟩ *
        (θ.1.degree : ℂ) := by
  let J := joinCenterKernel C
  let hJcentral :=
    joinCenterKernel_inf_sylow_le_center
      S C hcentral
  let zProduct : product S J :=
    ⟨z, center_le_joinCenterKernel_product S C hzcentral⟩
  have hzProductCenter :
      zProduct ∈
        Subgroup.center (product S J) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact
      Subgroup.mem_center_iff.mp hzcentral
        (x : X)
  let zRaw :
      Subgroup.normalizer
        (productSylow S J :
          Set (product S J)) :=
    ⟨zProduct,
      Subgroup.center_le_normalizer
        (productSylow S J :
          Set (product S J))
        hzProductCenter⟩
  let zInternal :
      internalProductNormalizer S J :=
    ⟨⟨z, hzNormalizer⟩,
      center_mem_joinCenterKernel_internalProductNormalizer
        S C z hzcentral hzNormalizer⟩
  let raw :=
    theorem44CharacterEquivOfCentralFibreData
      S J hJcentral d θ
  have hraw :=
    (theorem44CentralScalarLocalCorrespondenceOfCentralFibreData
      S J hJcentral d).correspondence_central_cross
        θ zProduct hzProductCenter zRaw.2
  have htargetValue :
      (internalTheorem44CentralFibreCharacterEquiv
          S J hJcentral d θ).1.values zInternal =
        raw.1.values zRaw := by
    change
      (raw.1.comap
        (productNormalizerEquivInternal S J).symm).values
          zInternal =
        raw.1.values zRaw
    rw [IrreducibleCharacter.comap_values]
    congr 1
  have htargetDegree :
      (internalTheorem44CentralFibreCharacterEquiv
          S J hJcentral d θ).1.degree =
        raw.1.degree :=
    rfl
  change
    θ.1.values zProduct * (raw.1.degree : ℂ) =
      raw.1.values zRaw * (θ.1.degree : ℂ) at hraw
  rw [← htargetValue] at hraw
  rw [htargetDegree]
  simpa [J, hJcentral, zProduct, zRaw, zInternal, raw] using hraw

/-- For the join-center kernel, every numerical Proposition-4.5 ambient
coherence automatically has the central-scalar compatibility needed by
the final Clifford assembly. -/
theorem joinCenterKernel_ambientCoherence_preservesCentralScalars
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      ProductActiveKernelCentralFibreData
        S (joinCenterKernel C)
          (joinCenterKernel_inf_sylow_le_center
            S C hcentral))
    (c :
      ProductAmbientCentralFibreCoherence
        S (joinCenterKernel C)
        (joinCenterKernel_inf_sylow_le_center
          S C hcentral)
        (joinCenterKernel_sup_normalizer_eq_top
          S C hgenerate)
        d) :
    c.PreservesCentralScalars
      S (joinCenterKernel C)
      (joinCenterKernel_inf_sylow_le_center
        S C hcentral)
      (joinCenterKernel_sup_normalizer_eq_top
        S C hgenerate)
      d := by
  let hJcentral :=
    joinCenterKernel_inf_sylow_le_center
      S C hcentral
  let hJgenerate :=
    joinCenterKernel_sup_normalizer_eq_top
      S C hgenerate
  letI :
      (product S (joinCenterKernel C)).Normal :=
    product_normal S (joinCenterKernel C)
      hJgenerate
  letI :
      (internalProductNormalizer
        S (joinCenterKernel C)).Normal :=
    internalProductNormalizer_normal
      S (joinCenterKernel C) hJgenerate
  let a :=
    c.toMatchedCentralFibreCliffordAssemblyData
      S (joinCenterKernel C)
      hJcentral hJgenerate d
  exact
    a.preservesCentralScalars_of_center_containing
      (fun z hzcentral =>
        center_le_joinCenterKernel_product
          S C hzcentral)
      (fun z hzcentral hzNormalizer =>
        center_mem_joinCenterKernel_internalProductNormalizer
          S C z hzcentral hzNormalizer)
      (fun θ z hzcentral hzNormalizer =>
        joinCenterKernel_internalTheorem44_central_cross
          S C hcentral d θ z hzcentral hzNormalizer)

/-- The formerly separate central-action intertwiner requirement is
automatic for the join-center kernel. -/
theorem joinCenterKernel_ambientCoherence_hasCentralActionIntertwiners
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      ProductActiveKernelCentralFibreData
        S (joinCenterKernel C)
          (joinCenterKernel_inf_sylow_le_center
            S C hcentral))
    (c :
      ProductAmbientCentralFibreCoherence
        S (joinCenterKernel C)
        (joinCenterKernel_inf_sylow_le_center
          S C hcentral)
        (joinCenterKernel_sup_normalizer_eq_top
          S C hgenerate)
        d) :
    c.HasCentralActionIntertwiners
      S (joinCenterKernel C)
      (joinCenterKernel_inf_sylow_le_center
        S C hcentral)
      (joinCenterKernel_sup_normalizer_eq_top
        S C hgenerate)
      d := by
  let hJcentral :=
    joinCenterKernel_inf_sylow_le_center
      S C hcentral
  let hJgenerate :=
    joinCenterKernel_sup_normalizer_eq_top
      S C hgenerate
  letI :
      (product S (joinCenterKernel C)).Normal :=
    product_normal S (joinCenterKernel C)
      hJgenerate
  letI :
      (internalProductNormalizer
        S (joinCenterKernel C)).Normal :=
    internalProductNormalizer_normal
      S (joinCenterKernel C) hJgenerate
  let a :=
    c.toMatchedCentralFibreCliffordAssemblyData
      S (joinCenterKernel C)
      hJcentral hJgenerate d
  exact
    a.hasCentralActionIntertwiners_of_preservesCentralScalars
      (joinCenterKernel_ambientCoherence_preservesCentralScalars
        S C hcentral hgenerate d c)

/-- Thus numerical ambient coherence for the join-center kernel directly
constructs the ambient central-scalar local correspondence; there is no
additional scalar-coherence input. -/
def centralScalarLocalCorrespondenceOfJoinCenterKernelAmbientCoherence
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d :
      ProductActiveKernelCentralFibreData
        S (joinCenterKernel C)
          (joinCenterKernel_inf_sylow_le_center
            S C hcentral))
    (c :
      ProductAmbientCentralFibreCoherence
        S (joinCenterKernel C)
        (joinCenterKernel_inf_sylow_le_center
          S C hcentral)
        (joinCenterKernel_sup_normalizer_eq_top
          S C hgenerate)
        d) :
    CentralScalarLocalCorrespondence S :=
  c.toCentralScalarLocalCorrespondence
    S (joinCenterKernel C)
    (joinCenterKernel_inf_sylow_le_center
      S C hcentral)
    (joinCenterKernel_sup_normalizer_eq_top
      S C hgenerate)
    d
    (joinCenterKernel_ambientCoherence_hasCentralActionIntertwiners
      S C hcentral hgenerate d c)

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
