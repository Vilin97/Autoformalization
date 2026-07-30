/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.InnerAutomorphismSubgroup
import McKayConjecture.InductiveMcKay.AutomorphismStabilizerCorrection
import McKayConjecture.InductiveMcKay.NormalizerInnerAutomorphismStabilizer

/-!
# From global automorphism generation to Sylow-stabilizer generation

Suppose two automorphisms already stabilize a fixed Sylow subgroup `P`, and
together with all inner automorphisms they generate `Aut(G)`.  Then those
same two elements, together with conjugations coming only from `N_G(P)`,
generate `Aut(G)_P`.

Indeed, write a stabilizing automorphism as an inner automorphism times a
word in the two stabilizing generators.  The word still stabilizes `P`, so
the remaining inner factor stabilizes `P`; its conjugating element must
therefore normalize `P`.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay
namespace SylowAutStabilizer

open GroupTheory

variable {G : Type u} [Group G] {p : ℕ}

/-- A global inner-plus-two-elements generation statement descends to the
corresponding Sylow-stabilizer generation statement, provided the two
displayed elements already stabilize the chosen Sylow subgroup.

The outer subgroup in the global hypothesis is written as the image of the
local closure.  This avoids any hidden choice of lifts and is exactly the
form needed by concrete corrected automorphisms. -/
theorem normalizerInner_sup_closure_pair_eq_top_of_global
    (P : Sylow p G)
    (a b : SylowAutStabilizer P)
    (hGlobal :
      innerAutomorphismSubgroup G ⊔
          (Subgroup.closure ({a, b} :
            Set (SylowAutStabilizer P))).map
            (SylowAutStabilizer P).subtype =
        ⊤) :
    (normalizerInnerHom P).range ⊔
        Subgroup.closure ({a, b} :
          Set (SylowAutStabilizer P)) =
      ⊤ := by
  apply top_unique
  intro s _
  have hsGlobal :
      (s : MulAut G) ∈
        innerAutomorphismSubgroup G ⊔
          (Subgroup.closure ({a, b} :
            Set (SylowAutStabilizer P))).map
            (SylowAutStabilizer P).subtype := by
    rw [hGlobal]
    exact Subgroup.mem_top _
  obtain ⟨i, hi, o, ho, hio⟩ :=
    (Subgroup.mem_sup_of_normal_left.mp hsGlobal)
  obtain ⟨g, rfl⟩ := hi
  obtain ⟨oLocal, hoLocal, rfl⟩ := ho
  have hInnerEq :
      MulAut.conj g =
        (s : MulAut G) * (oLocal : MulAut G)⁻¹ := by
    rw [← hio]
    simp
  have hInnerMem :
      MulAut.conj g ∈ SylowAutStabilizer P := by
    rw [hInnerEq]
    exact
      (SylowAutStabilizer P).mul_mem
        s.2
        ((SylowAutStabilizer P).inv_mem oLocal.2)
  have hgNormalizer :
      g ∈ Subgroup.normalizer (P : Subgroup G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hsylow :
        MulAut.conj g • P = P :=
      (mem_iff (P := P) (MulAut.conj g)).mp hInnerMem
    exact congrArg (fun Q : Sylow p G ↦ (Q : Subgroup G)) hsylow
  let gNormalizer : SylowNormalizer P :=
    ⟨g, hgNormalizer⟩
  have hLocalEq :
      normalizerInnerHom P gNormalizer * oLocal = s := by
    apply Subtype.ext
    exact hio
  rw [← hLocalEq]
  exact
    Subgroup.mul_mem_sup
      (show normalizerInnerHom P gNormalizer ∈
          (normalizerInnerHom P).range from
        ⟨gNormalizer, rfl⟩)
      hoLocal

/-- If two arbitrary automorphisms generate the full automorphism group
together with the inner subgroup, their chosen Sylow corrections generate
the Sylow stabilizer together with the normalizer-inner range. -/
theorem
    normalizerInner_sup_corrected_pair_eq_top_of_global
    [Finite G] [Fact p.Prime]
    (P : Sylow p G)
    (a b : MulAut G)
    (hGlobal :
      innerAutomorphismSubgroup G ⊔
          Subgroup.closure ({a, b} : Set (MulAut G)) =
        ⊤) :
    (normalizerInnerHom P).range ⊔
        Subgroup.closure
          ({corrected P a, corrected P b} :
            Set (SylowAutStabilizer P)) =
      ⊤ := by
  apply
    normalizerInner_sup_closure_pair_eq_top_of_global
      P (corrected P a) (corrected P b)
  let K :
      Subgroup (MulAut G) :=
    innerAutomorphismSubgroup G ⊔
      (Subgroup.closure
        ({corrected P a, corrected P b} :
          Set (SylowAutStabilizer P))).map
        (SylowAutStabilizer P).subtype
  have hCorrectedA :
      (corrected P a : MulAut G) ∈
        (Subgroup.closure
          ({corrected P a, corrected P b} :
            Set (SylowAutStabilizer P))).map
          (SylowAutStabilizer P).subtype := by
    exact
      ⟨corrected P a,
        Subgroup.subset_closure (by simp),
        rfl⟩
  have hCorrectedB :
      (corrected P b : MulAut G) ∈
        (Subgroup.closure
          ({corrected P a, corrected P b} :
            Set (SylowAutStabilizer P))).map
          (SylowAutStabilizer P).subtype := by
    exact
      ⟨corrected P b,
        Subgroup.subset_closure (by simp),
        rfl⟩
  have haK : a ∈ K := by
    have hInner :
        (MulAut.conj (correctionConjugator P a))⁻¹ ∈
          innerAutomorphismSubgroup G :=
      (innerAutomorphismSubgroup G).inv_mem
        ⟨correctionConjugator P a, rfl⟩
    have hproduct :
        (MulAut.conj (correctionConjugator P a))⁻¹ *
            (corrected P a : MulAut G) =
          a := by
      rw [corrected_coe]
      simp
    rw [← hproduct]
    exact Subgroup.mul_mem_sup hInner hCorrectedA
  have hbK : b ∈ K := by
    have hInner :
        (MulAut.conj (correctionConjugator P b))⁻¹ ∈
          innerAutomorphismSubgroup G :=
      (innerAutomorphismSubgroup G).inv_mem
        ⟨correctionConjugator P b, rfl⟩
    have hproduct :
        (MulAut.conj (correctionConjugator P b))⁻¹ *
            (corrected P b : MulAut G) =
          b := by
      rw [corrected_coe]
      simp
    rw [← hproduct]
    exact Subgroup.mul_mem_sup hInner hCorrectedB
  have hOuter :
      Subgroup.closure ({a, b} : Set (MulAut G)) ≤ K := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact haK
    · simpa only [Set.mem_singleton_iff] using hx ▸ hbK
  have hGenerated :
      innerAutomorphismSubgroup G ⊔
          Subgroup.closure ({a, b} : Set (MulAut G)) ≤
        K :=
    sup_le le_sup_left hOuter
  rw [hGlobal] at hGenerated
  exact top_unique hGenerated

end SylowAutStabilizer
end InductiveMcKay
end McKayConjecture
