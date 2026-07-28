/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralIndexSubgroup
import McKayConjecture.InductiveMcKay.CentralScalarNormalizerInduction

/-!
# Central-scalar normalizer induction below a central-index bound

Rossi's factor-extension argument is performed inside an induction on
`|G / Z(G)|`.  It therefore supplies local inductive-McKay data only for
groups whose central index is below the current ambient bound, rather than
for every finite group in the universe.

This file gives the bounded form of scalar-preserving normalizer induction.
Every proper local intermediate contains the center of its ambient group,
because it contains the Sylow normalizer.  Its central index is consequently
strictly smaller, so the recursion remains below the original bound.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {p : ℕ}

/-- Full local inductive-McKay data for every group below a fixed
central-index bound. -/
abbrev CentralIndexBoundedLocalProvider
    (p bound : ℕ) :=
  ∀ (Y : Type u) [Group Y] [Finite Y],
    centralIndex Y < bound →
      ∀ Q : Sylow p Y,
        LocalInductiveMcKayData Q

/-- Scalar-preserving normalizer induction using only local data below a
fixed central-index bound. -/
def centralScalarCorrespondenceOfCentralIndexBound
    (bound : ℕ)
    (localData :
      CentralIndexBoundedLocalProvider.{u} p bound)
    (G : Type u) [Group G] [Finite G]
    (hGbound : centralIndex G < bound)
    (Q : Sylow p G)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ) :
    CentralScalarNormalizerCorrespondence
      G p Q Z hZcentral lambda := by
  have all :
      ∀ n : ℕ,
        (∀ m < n,
          ∀ (Y : Type u) [Group Y] [Finite Y],
            centralIndex Y = m →
            centralIndex Y < bound →
          ∀ (R : Sylow p Y)
            (C : Subgroup Y)
            (hCcentral : C ≤ Subgroup.center Y)
            (mu : C →* ℂˣ),
            Nonempty
              (CentralScalarNormalizerCorrespondence
                Y p R C hCcentral mu)) →
        ∀ (Y : Type u) [Group Y] [Finite Y],
          centralIndex Y = n →
          centralIndex Y < bound →
        ∀ (R : Sylow p Y)
          (C : Subgroup Y)
          (hCcentral : C ≤ Subgroup.center Y)
          (mu : C →* ℂˣ),
          Nonempty
            (CentralScalarNormalizerCorrespondence
              Y p R C hCcentral mu) := by
    intro n ih Y _ _ hmeasure hYbound R C hCcentral mu
    let datum := localData Y hYbound R
    by_cases hnormalizer :
        Subgroup.normalizer (R : Set Y) = ⊤
    · exact
        ⟨centralScalarCorrespondenceOfNormalizerEqTop
          R hnormalizer C hCcentral mu⟩
    · have hproper : datum.intermediate < ⊤ :=
        datum.proper_of_normalizer_ne_top hnormalizer
      have hcenter :
          Subgroup.center Y ≤ datum.intermediate :=
        (Subgroup.center_le_normalizer
          (R : Set Y)).trans datum.normalizer_le
      have hsmall :
          centralIndex datum.intermediate < n := by
        rw [← hmeasure]
        exact
          centralIndex_lt_of_center_le_of_lt_top
            datum.intermediate hcenter hproper
      have hIntermediateBound :
          centralIndex datum.intermediate < bound :=
        hsmall.trans (hmeasure ▸ hYbound)
      let hRle :
          (R : Subgroup Y) ≤ datum.intermediate :=
        Subgroup.le_normalizer.trans
          datum.normalizer_le
      let R' : Sylow p datum.intermediate :=
        sylowIn R datum.intermediate hRle
      let hCle : C ≤ datum.intermediate :=
        (central_le_sylowNormalizer
          R C hCcentral).trans datum.normalizer_le
      let C' : Subgroup datum.intermediate :=
        centralSubgroupIn C datum.intermediate
      let hC'central :
          C' ≤ Subgroup.center datum.intermediate :=
        centralSubgroupIn_le_center
          C datum.intermediate hCcentral hCle
      let mu' : C' →* ℂˣ :=
        centralScalarIn C datum.intermediate hCle mu
      obtain ⟨inductionCorrespondence⟩ :=
        ih (centralIndex datum.intermediate) hsmall
          datum.intermediate rfl hIntermediateBound
          R' C' hC'central mu'
      let localCorrespondence :
          PPrimeCentralScalarCharacter Y p C mu ≃
            PPrimeCentralScalarCharacter
              datum.intermediate p C' mu' :=
        datum.centralScalarCorrespondence
          C hCcentral hCle mu
      let normalizerTransport :
          NormalizerCentralScalarCharacter
              R' C' hC'central mu' ≃
            NormalizerCentralScalarCharacter
              R C hCcentral mu :=
        normalizerCentralScalarTransport
          R datum.intermediate datum.normalizer_le
          C hCcentral mu
      exact
        ⟨localCorrespondence.trans
          (inductionCorrespondence.trans
            normalizerTransport)⟩
  exact
    Classical.choice
      (Nat.strong_induction_on
        (centralIndex G)
        (p := fun n =>
          ∀ (Y : Type u) [Group Y] [Finite Y],
            centralIndex Y = n →
            centralIndex Y < bound →
          ∀ (R : Sylow p Y)
            (C : Subgroup Y)
            (hCcentral : C ≤ Subgroup.center Y)
            (mu : C →* ℂˣ),
            Nonempty
              (CentralScalarNormalizerCorrespondence
                Y p R C hCcentral mu))
        all G rfl hGbound Q Z hZcentral lambda)

/-- Specialization to the induction hypothesis at the central index of a
fixed ambient group. -/
def centralScalarCorrespondenceOfCentralIndexIH
    {A : Type u} [Group A] [Finite A]
    (ih :
      ∀ (Y : Type u) [Group Y] [Finite Y],
        centralIndex Y < centralIndex A →
          ∀ Q : Sylow p Y,
            Nonempty (LocalInductiveMcKayData Q))
    (G : Type u) [Group G] [Finite G]
    (hGsmall : centralIndex G < centralIndex A)
    (Q : Sylow p G)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ) :
    CentralScalarNormalizerCorrespondence
      G p Q Z hZcentral lambda :=
  centralScalarCorrespondenceOfCentralIndexBound
    (centralIndex A)
    (fun Y _ _ hY R ↦ Classical.choice (ih Y hY R))
    G hGsmall Q Z hZcentral lambda

end InductiveMcKay
end McKayConjecture
