/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FinitePermutationRepresentationBasis
import McKayConjecture.Character.PGroupPermutationSummandExchange
import McKayConjecture.Character.SubrepresentationDirectSum

/-!
# Direct summands of p-group permutation modules

Every finite-dimensional representation decomposes, by induction on
dimension, into directly indecomposable summands.  For a split retract
of a finite permutation module for a finite `p`-group, the local
exchange theorem identifies each such summand with a transitive orbit
factor of the original permutation module.  Combining their bases
proves that the retract itself has a finite permutation basis.

This argument needs only the existence half of Krull--Schmidt, not
uniqueness or cancellation of multiplicities.
-/

noncomputable section

namespace Representation
namespace PermutationModuleBasis

variable {p : ℕ} [Fact p.Prime]
variable {k P V ι : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [MulAction P ι] [Finite ι]

variable (B : PermutationModuleBasis
  (k := k) (P := P) (V := V) (ι := ι))

local notation "ρ" => B.representation
local notation "Ω" => MulAction.orbitRel.Quotient P ι

/-- The intrinsic finite permutation basis on one canonical orbit
factor. -/
def orbitFinitePermutationBasis (ω : Ω) :
    FinitePermutationBasis
      (B.orbitSubrepresentation ω).toRepresentation where
  Index := ω.orbit
  indexFintype := Fintype.ofFinite ω.orbit
  action := MulAction.toPermHom P ω.orbit
  basis := B.orbitBasis ω
  map_basis := B.orbitBasis_action ω

/-- Any finite-dimensional split retract of a finite permutation
module for a finite `p`-group has a finite permutation basis. -/
theorem finitePermutationBasis_of_split_retract
    (hP : IsPGroup p P)
    {A : Type} [AddCommGroup A] [Module k A]
    [FiniteDimensional k A]
    (ρA : Representation k P A)
    (includeA : IntertwiningMap ρA ρ)
    (retractA : IntertwiningMap ρ ρA)
    (hretract : retractA.comp includeA =
      IntertwiningMap.id ρA) :
    Nonempty (FinitePermutationBasis ρA) := by
  classical
  suffices
      ∀ n : ℕ,
        ∀ {A : Type} [AddCommGroup A] [Module k A]
          [FiniteDimensional k A],
          (ρA : Representation k P A) →
          (includeA : IntertwiningMap ρA ρ) →
          (retractA : IntertwiningMap ρ ρA) →
          retractA.comp includeA = IntertwiningMap.id ρA →
          Module.finrank k A = n →
          Nonempty (FinitePermutationBasis ρA) by
    exact this (Module.finrank k A) ρA includeA retractA
      hretract rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro A _ _ _ ρA includeA retractA hretract hdim
      by_cases hn : n = 0
      · have hzero : Module.finrank k A = 0 :=
          hdim.trans hn
        letI : Subsingleton A :=
          Module.finrank_zero_iff.1 hzero
        exact ⟨FinitePermutationBasis.empty ρA⟩
      · have hpos : 0 < Module.finrank k A := by
          rw [hdim]
          exact Nat.pos_of_ne_zero hn
        letI : Nontrivial A :=
          Module.finrank_pos_iff.mp hpos
        by_cases hindecomposable :
            ρA.IsDirectSumIndecomposable
        · obtain ⟨ω, ⟨e⟩⟩ :=
            B.exists_orbit_equiv_of_indecomposable_split_retract
              hP ρA hindecomposable includeA retractA hretract
          exact
            ⟨(B.orbitFinitePermutationBasis ω).transport e⟩
        · have hsplit :
              ∃ U W : Subrepresentation ρA,
                IsCompl U.toSubmodule W.toSubmodule ∧
                U ≠ ⊥ ∧ W ≠ ⊥ := by
            have hnotforall :
                ¬ ∀ U W : Subrepresentation ρA,
                  IsCompl U.toSubmodule W.toSubmodule →
                    U = ⊥ ∨ W = ⊥ := by
              intro hforall
              exact hindecomposable ⟨inferInstance, hforall⟩
            push Not at hnotforall
            exact hnotforall
          obtain ⟨U, W, hUW, hU, hW⟩ := hsplit
          have hUlt : U.toSubmodule < ⊤ := by
            apply lt_top_iff_ne_top.mpr
            intro hUtop
            apply hW
            apply Subrepresentation.ext
            have hdisjoint := hUW.disjoint.eq_bot
            rw [hUtop, top_inf_eq] at hdisjoint
            exact hdisjoint
          have hWlt : W.toSubmodule < ⊤ := by
            apply lt_top_iff_ne_top.mpr
            intro hWtop
            apply hU
            apply Subrepresentation.ext
            have hdisjoint := hUW.disjoint.eq_bot
            rw [hWtop, inf_top_eq] at hdisjoint
            exact hdisjoint
          have hUdim :
              Module.finrank k U.toSubmodule < n := by
            calc
              Module.finrank k U.toSubmodule <
                  Module.finrank k (⊤ : Submodule k A) :=
                Submodule.finrank_lt_finrank_of_lt hUlt
              _ = Module.finrank k A := finrank_top k A
              _ = n := hdim
          have hWdim :
              Module.finrank k W.toSubmodule < n := by
            calc
              Module.finrank k W.toSubmodule <
                  Module.finrank k (⊤ : Submodule k A) :=
                Submodule.finrank_lt_finrank_of_lt hWlt
              _ = Module.finrank k A := finrank_top k A
              _ = n := hdim
          let includeU : IntertwiningMap U.toRepresentation ρ :=
            includeA.comp
              (Subrepresentation.inclusionIntertwiningMap U)
          let retractU : IntertwiningMap ρ U.toRepresentation :=
            (Subrepresentation.projectionIntertwiningMap U W hUW).comp
              retractA
          have hretractU :
              retractU.comp includeU =
                IntertwiningMap.id U.toRepresentation := by
            apply IntertwiningMap.ext
            apply LinearMap.ext
            intro u
            change
              Subrepresentation.projectionIntertwiningMap U W hUW
                  (retractA (includeA (u : A))) =
                u
            have hretractAt :=
              congrArg
                (fun t : IntertwiningMap ρA ρA => t (u : A))
                hretract
            rw [show retractA (includeA (u : A)) = (u : A) by
              simpa only [IntertwiningMap.comp_apply,
                IntertwiningMap.id_apply] using hretractAt]
            exact
              Submodule.projectionOnto_apply_left hUW u
          let includeW : IntertwiningMap W.toRepresentation ρ :=
            includeA.comp
              (Subrepresentation.inclusionIntertwiningMap W)
          let retractW : IntertwiningMap ρ W.toRepresentation :=
            (Subrepresentation.projectionIntertwiningMap W U hUW.symm).comp
              retractA
          have hretractW :
              retractW.comp includeW =
                IntertwiningMap.id W.toRepresentation := by
            apply IntertwiningMap.ext
            apply LinearMap.ext
            intro w
            change
              Subrepresentation.projectionIntertwiningMap W U hUW.symm
                  (retractA (includeA (w : A))) =
                w
            have hretractAt :=
              congrArg
                (fun t : IntertwiningMap ρA ρA => t (w : A))
                hretract
            rw [show retractA (includeA (w : A)) = (w : A) by
              simpa only [IntertwiningMap.comp_apply,
                IntertwiningMap.id_apply] using hretractAt]
            exact
              Submodule.projectionOnto_apply_left hUW.symm w
          obtain ⟨CU⟩ :=
            ih (Module.finrank k U.toSubmodule) hUdim
              U.toRepresentation includeU retractU hretractU rfl
          obtain ⟨CW⟩ :=
            ih (Module.finrank k W.toSubmodule) hWdim
              W.toRepresentation includeW retractW hretractW rfl
          let eUW :=
            Subrepresentation.prodEquivOfIsCompl U W hUW
          exact ⟨(CU.prod CW).transport eUW.symm⟩

/-- The range of every equivariant idempotent on a finite permutation
module for a finite `p`-group has a finite permutation basis.  This is
the direct-summand theorem with no orbit-preservation hypothesis. -/
theorem finitePermutationBasis_range_of_idempotent
    (hP : IsPGroup p P)
    (e : IntertwiningMap ρ ρ)
    (he : IsIdempotentElem e) :
    Nonempty (FinitePermutationBasis e.range.toRepresentation) := by
  letI : FiniteDimensional k V :=
    B.basis.finiteDimensional_of_finite
  exact
    B.finitePermutationBasis_of_split_retract hP
      e.range.toRepresentation
      (B.endomorphismRangeInclusion e)
      (B.endomorphismRangeRetract e)
      (B.endomorphismRangeRetract_comp_inclusion e he)

end PermutationModuleBasis
end Representation
