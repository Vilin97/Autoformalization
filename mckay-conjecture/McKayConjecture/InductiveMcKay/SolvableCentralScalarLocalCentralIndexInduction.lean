/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralScalarLocalCentralIndexInduction

/-!
# Central-scalar normalizer induction inside solvable groups

The ordinary bounded central-index provider ranges over all finite groups.
For a solvable ambient group, every intermediate subgroup is again
solvable, so the same recursion only needs local data on solvable groups.
This file records that sharper interface.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {p : ℕ}

/-- Central-scalar local data for every solvable group below a fixed
central-index bound. -/
abbrev SolvableCentralIndexBoundedCentralScalarLocalProvider
    (p bound : ℕ) :=
  ∀ (Y : Type u) [Group Y] [Finite Y] [Group.IsSolvable Y],
    centralIndex Y < bound →
      ∀ Q : Sylow p Y,
        CentralScalarLocalCorrespondence Q

/-- Scalar-preserving normalizer induction below a central-index bound,
restricted throughout to solvable groups. -/
def centralScalarCorrespondenceOfSolvableCentralScalarLocalCentralIndexBound
    (bound : ℕ)
    (localData :
      SolvableCentralIndexBoundedCentralScalarLocalProvider.{u}
        p bound)
    (G : Type u) [Group G] [Finite G] [Group.IsSolvable G]
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
          ∀ (Y : Type u) [Group Y] [Finite Y]
            [Group.IsSolvable Y],
            centralIndex Y = m →
            centralIndex Y < bound →
          ∀ (R : Sylow p Y)
            (C : Subgroup Y)
            (hCcentral : C ≤ Subgroup.center Y)
            (mu : C →* ℂˣ),
            Nonempty
              (CentralScalarNormalizerCorrespondence
                Y p R C hCcentral mu)) →
        ∀ (Y : Type u) [Group Y] [Finite Y]
          [Group.IsSolvable Y],
          centralIndex Y = n →
          centralIndex Y < bound →
        ∀ (R : Sylow p Y)
          (C : Subgroup Y)
          (hCcentral : C ≤ Subgroup.center Y)
          (mu : C →* ℂˣ),
          Nonempty
            (CentralScalarNormalizerCorrespondence
              Y p R C hCcentral mu) := by
    intro n ih Y _ _ _ hmeasure hYbound R C hCcentral mu
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
          ∀ (Y : Type u) [Group Y] [Finite Y]
            [Group.IsSolvable Y],
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

/-- Specialization to a solvable central-index induction hypothesis at an
ambient solvable group. -/
def centralScalarCorrespondenceOfSolvableCentralScalarLocalCentralIndexIH
    {A : Type u} [Group A] [Finite A] [Group.IsSolvable A]
    (ih :
      ∀ (Y : Type u) [Group Y] [Finite Y] [Group.IsSolvable Y],
        centralIndex Y < centralIndex A →
          ∀ Q : Sylow p Y,
            Nonempty (CentralScalarLocalCorrespondence Q))
    (G : Type u) [Group G] [Finite G] [Group.IsSolvable G]
    (hGsmall : centralIndex G < centralIndex A)
    (Q : Sylow p G)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ) :
    CentralScalarNormalizerCorrespondence
      G p Q Z hZcentral lambda :=
  centralScalarCorrespondenceOfSolvableCentralScalarLocalCentralIndexBound
    (centralIndex A)
    (fun Y _ _ _ hY R ↦ Classical.choice (ih Y hY R))
    G hGsmall Q Z hZcentral lambda

end InductiveMcKay
end McKayConjecture
