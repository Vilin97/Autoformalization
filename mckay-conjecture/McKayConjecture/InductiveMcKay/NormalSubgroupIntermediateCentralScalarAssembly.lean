/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalarConstituent
import McKayConjecture.InductiveMcKay.CentralScalarLocalCorrespondence
import McKayConjecture.InductiveMcKay.NormalSubgroupIntermediateOrbitAssembly

/-!
# Central-scalar preservation in the normal-subgroup intermediate

The Clifford assembler for Rossi's normal-subgroup reduction matches an
ambient character over a character `θ` of `J = N Z(G)` with an intermediate
character over the identity-transport of `θ`.  A central element therefore
acts by the same scalar on both ambient representations.  This conclusion
is independent of the particular equivalence between the two inertia
fibres.

This file records that observation and packages the assembled numerical
correspondence as `CentralScalarLocalCorrespondence`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupIntermediateOrbitAssembly

open CliffordCorrespondence
open CliffordPartition
open NormalSubgroupIntermediateInertia
open NormalSubgroupIntermediateRepresentatives

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G)
variable (N : Subgroup G) [N.Normal]

noncomputable local instance
    normalSubgroupIntermediateCentralScalarAssemblyFintypeG :
    Fintype G :=
  Fintype.ofFinite G

noncomputable local instance
    normalSubgroupIntermediateCentralScalarAssemblyFintypeH :
    Fintype (intermediate P N) :=
  Fintype.ofFinite (intermediate P N)

namespace InertiaFibreData

/-- The equivalence assembled from normal-subgroup inertia fibres preserves
the normalized value of every ambient central element. -/
theorem assembledPPrimeEquiv_central_cross
    (d : InertiaFibreData P N)
    (hfusion : SylowFixedOrbitFusion P N)
    (χ : PPrimeIrreducibleCharacter G p)
    (z : G)
    (hzcentral : z ∈ Subgroup.center G)
    (hzintermediate : z ∈ intermediate P N) :
    χ.1.values z *
        ((assembledPPrimeEquiv P N d hfusion χ).1.degree : ℂ) =
      (assembledPPrimeEquiv P N d hfusion χ).1.values
          ⟨z, hzintermediate⟩ *
        (χ.1.degree : ℂ) := by
  let a :=
    toAdaptedCliffordFibreAssemblyData
      P N d hfusion
  let q := activeOrbitIndex (joinCenter N) χ
  let θ := sourceRepresentative P N q
  let φ := forwardRepresentative P N q
  let ψ := a.assembledPPrimeEquiv χ
  let zJ : joinCenter N :=
    ⟨z,
      NormalSubgroupJoinCenterReduction.center_le_joinCenter
        N hzcentral⟩
  let zH : intermediate P N :=
    ⟨z, hzintermediate⟩
  let zI : internalJoinCenter P N :=
    ⟨zH,
      NormalSubgroupJoinCenterReduction.center_le_joinCenter
        N hzcentral⟩
  have hzHcentral :
      zH ∈ Subgroup.center (intermediate P N) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact
      Subgroup.mem_center_iff.mp hzcentral
        (h : G)
  have hsourceLies :
      LiesOverAlong (joinCenter N).subtype θ.1 χ.1 := by
    exact a.liesOver_sourceRepresentative χ
  have htargetLies :
      LiesOverAlong (internalJoinCenter P N).subtype
        φ.1 ψ.1 := by
    exact
      a.liesOver_targetRepresentative_assembledPPrimeEquiv χ
  have hsource :=
    central_cross_of_liesOverSubgroup
      (joinCenter N) θ.1 χ.1
      hsourceLies zJ hzcentral
  have htarget :=
    central_cross_of_liesOverSubgroup
      (internalJoinCenter P N) φ.1 ψ.1
      htargetLies zI hzHcentral
  have hφdegree : φ.1.degree = θ.1.degree :=
    rfl
  have hφvalue : φ.1.values zI = θ.1.values zJ :=
    rfl
  have htarget' :
      ψ.1.values zH * (θ.1.degree : ℂ) =
        θ.1.values zJ * (ψ.1.degree : ℂ) := by
    simpa [hφdegree, hφvalue] using htarget
  apply mul_right_cancel₀
    (Nat.cast_ne_zero.mpr θ.1.degree_ne_zero)
  calc
    (χ.1.values z * (ψ.1.degree : ℂ)) *
          (θ.1.degree : ℂ) =
        (χ.1.values z * (θ.1.degree : ℂ)) *
          (ψ.1.degree : ℂ) := by ring
    _ =
        (θ.1.values zJ * (χ.1.degree : ℂ)) *
          (ψ.1.degree : ℂ) := by rw [hsource]
    _ =
        (θ.1.values zJ * (ψ.1.degree : ℂ)) *
          (χ.1.degree : ℂ) := by ring
    _ =
        (ψ.1.values zH * (θ.1.degree : ℂ)) *
          (χ.1.degree : ℂ) := by rw [htarget']
    _ =
        (ψ.1.values zH * (χ.1.degree : ℂ)) *
          (θ.1.degree : ℂ) := by ring

/-- Canonical Sylow fusion discharges the only orbit-theoretic input in
the preceding central-scalar theorem. -/
theorem assembledPPrimeEquivCanonical_central_cross
    (d : InertiaFibreData P N)
    (χ : PPrimeIrreducibleCharacter G p)
    (z : G)
    (hzcentral : z ∈ Subgroup.center G)
    (hzintermediate : z ∈ intermediate P N) :
    χ.1.values z *
        ((assembledPPrimeEquivCanonical P N d χ).1.degree : ℂ) =
      (assembledPPrimeEquivCanonical P N d χ).1.values
          ⟨z, hzintermediate⟩ *
        (χ.1.degree : ℂ) :=
  assembledPPrimeEquiv_central_cross
    P N d (sylowFixedOrbitFusion P N)
      χ z hzcentral hzintermediate

/-- When Rossi's normalizer intermediate is proper, the fibrewise
construction gives exactly the central-scalar local datum needed by the
numerical induction. -/
def toCentralScalarLocalCorrespondence
    (d : InertiaFibreData P N)
    (hproper :
      N ⊔ Subgroup.normalizer (P : Set G) ≠ ⊤) :
    CentralScalarLocalCorrespondence P where
  toLocalCorrespondence :=
    { intermediate := intermediate P N
      normalizer_le :=
        NormalSubgroupJoinCenterReduction.normalizer_le_normalizerIntermediate
          P N
      proper_of_normalizer_ne_top := fun _ ↦ by
        apply lt_top_iff_ne_top.mpr
        intro htop
        apply hproper
        rw [←
          NormalSubgroupJoinCenterReduction.normalizerIntermediate_eq_normal_sup
            P N]
        exact htop
      correspondence :=
        assembledPPrimeEquivCanonical P N d }
  correspondence_central_cross :=
    d.assembledPPrimeEquivCanonical_central_cross

end InertiaFibreData
end NormalSubgroupIntermediateOrbitAssembly
end InductiveMcKay
end McKayConjecture
