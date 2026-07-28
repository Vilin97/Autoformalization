/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ActiveExtension
import McKayConjecture.Character.OverAlongTransport

/-!
# Transporting activity along group equivalences

Simultaneous relabelling of an ambient finite group and a normal subgroup
preserves the exact active-character predicate.  The proof uses the
equivalent formulation of activity by an ambient prime-to-`p` character
lying over the selected constituent.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordPartition

variable {G G' : Type} [Group G] [Group G']
variable [Finite G] [Finite G']
variable {p : ℕ}

/-- Activity is invariant under a commuting square of ambient and
normal-subgroup equivalences. -/
theorem isActivePPrimeCharacter_comap_equiv_iff
    (K : Subgroup G) [K.Normal]
    (K' : Subgroup G') [K'.Normal]
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom)
    (θ : PPrimeIrreducibleCharacter K p) :
    @IsActivePPrimeCharacter
        G' _ K' _ p
        (IrreducibleCharacter.pPrimeComapEquiv p eK θ) ↔
      @IsActivePPrimeCharacter G _ K _ p θ := by
  rw [isActivePPrimeCharacter_iff_exists_liesOver,
    isActivePPrimeCharacter_iff_exists_liesOver]
  constructor
  · rintro ⟨χ', hχ'⟩
    let χ :
        PPrimeIrreducibleCharacter G p :=
      ⟨χ'.1.comap eG.symm, χ'.2⟩
    refine ⟨χ, ?_⟩
    have hχcoe :
        χ.1.comap eG = χ'.1 := by
      dsimp [χ]
      simp
    have hleft :
        CliffordCorrespondence.LiesOverAlong K'.subtype
          (θ.1.comap eK) (χ.1.comap eG) := by
      rw [hχcoe]
      change
        CliffordCorrespondence.LiesOverAlong K'.subtype
          (θ.1.comap eK) χ'.1 at hχ'
      exact hχ'
    exact
      (CliffordCorrespondence.liesOverAlong_comap_equiv_iff
        eG eK K.subtype K'.subtype hcomm
        θ.1 χ.1).mp hleft
  · rintro ⟨χ, hχ⟩
    refine
      ⟨IrreducibleCharacter.pPrimeComapEquiv p eG χ, ?_⟩
    exact
      (CliffordCorrespondence.liesOverAlong_comap_equiv_iff
        eG eK K.subtype K'.subtype hcomm
        θ.1 χ.1).mpr hχ

end CliffordPartition
end McKayConjecture
