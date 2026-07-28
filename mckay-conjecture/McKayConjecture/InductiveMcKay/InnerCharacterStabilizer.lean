/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InnerAutomorphism
import McKayConjecture.Character.KernelQuotient
import McKayConjecture.InductiveMcKay.ExactNormalizerProjectiveTableData

/-!
# Inner automorphisms in a Sylow-character stabilizer

Conjugation by the exact Sylow normalizer preserves the Sylow subgroup, and
inner automorphisms fix every ordinary character.  Hence the normalizer maps
canonically to every character stabilizer occurring in the inductive McKay
condition.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

variable {G : Type u} [Group G] {p : ℕ}

/-- Conjugation by the Sylow normalizer, bundled in the stabilizer of a fixed
`p'`-character. -/
def normalizerInnerCharacterStabilizerHom
    (P : Sylow p G)
    (χ : PPrimeIrreducibleCharacter G p) :
    SylowNormalizer P →*
      PPrimeCharacterStabilizer P χ where
  toFun g :=
    ⟨⟨MulAut.conj g.1, by
        rw [SylowAutStabilizer.mem_iff]
        apply Sylow.ext
        exact
          Subgroup.mem_normalizer_iff_map_conj_eq.mp g.2⟩,
      by
        rw [PPrimeCharacterStabilizer.mem_iff]
        exact pPrime_conj_smul p g.1 χ⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one (MulAut.conj : G →* MulAut G)
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul (MulAut.conj : G →* MulAut G) g.1 h.1

@[simp]
theorem normalizerInnerCharacterStabilizerHom_ambientAction
    (P : Sylow p G)
    (χ : PPrimeIrreducibleCharacter G p)
    (g : SylowNormalizer P) :
    PPrimeCharacterStabilizer.ambientAction
        (normalizerInnerCharacterStabilizerHom P χ g) =
      MulAut.conj g.1 :=
  rfl

@[simp]
theorem normalizerInnerCharacterStabilizerHom_intermediateAction
    [Finite G]
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p)
    (g : SylowNormalizer P) :
    e.toExactNormalizerLocalCorrespondence.stabilizerIntermediateAction χ
        (normalizerInnerCharacterStabilizerHom P χ g) =
      MulAut.conj g := by
  apply DFunLike.ext _ _
  intro n
  apply Subtype.ext
  rfl

/-- The kernel of the normalizer-to-character-stabilizer map consists of
elements central in the ambient group. -/
theorem mem_center_of_mem_normalizerInnerCharacterStabilizerHom_ker
    (P : Sylow p G)
    (χ : PPrimeIrreducibleCharacter G p)
    (g : SylowNormalizer P)
    (hg :
      g ∈ (normalizerInnerCharacterStabilizerHom P χ).ker) :
    g.1 ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro x
  have hconj :
      MulAut.conj g.1 = 1 := by
    have hstab :
        normalizerInnerCharacterStabilizerHom P χ g = 1 :=
      MonoidHom.mem_ker.mp hg
    exact congrArg (fun a : PPrimeCharacterStabilizer P χ ↦ a.1.1) hstab
  have hx := DFunLike.congr_fun hconj x
  change g.1 * x * g.1⁻¹ = x at hx
  symm
  calc
    g.1 * x = (g.1 * x * g.1⁻¹) * g.1 := by simp [mul_assoc]
    _ = x * g.1 := by rw [hx]

/-- The same kernel is central inside the exact normalizer itself. -/
theorem mem_normalizer_center_of_mem_innerCharacterStabilizerHom_ker
    (P : Sylow p G)
    (χ : PPrimeIrreducibleCharacter G p)
    (g : SylowNormalizer P)
    (hg :
      g ∈ (normalizerInnerCharacterStabilizerHom P χ).ker) :
    g ∈ Subgroup.center (SylowNormalizer P) := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  exact
    Subgroup.mem_center_iff.mp
      (mem_center_of_mem_normalizerInnerCharacterStabilizerHom_ker
        P χ g hg) x.1

/-- An ambient character which is trivial on the ambient center supplies
the kernel condition needed to descend its normalizer implementers. -/
theorem normalizerInnerCharacterStabilizerHom_ker_le_ambientRealization
    [Finite G]
    (P : Sylow p G)
    (χ : PPrimeIrreducibleCharacter G p)
    (hχ : χ.1.TrivialOn (Subgroup.center G)) :
    (normalizerInnerCharacterStabilizerHom P χ).ker ≤
      (χ.1.realizationLinearEquivHom.comp
        (Subgroup.normalizer (P : Set G)).subtype).ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  apply LinearEquiv.toLinearMap_injective
  rw [MonoidHom.comp_apply,
    χ.1.realizationLinearEquivHom_toLinearMap]
  exact
    hχ
      ⟨g.1,
        mem_center_of_mem_normalizerInnerCharacterStabilizerHom_ker
          P χ g hg⟩

/-- A normalizer character trivial on the normalizer center likewise
supplies the descended local implementers. -/
theorem normalizerInnerCharacterStabilizerHom_ker_le_localRealization
    [Finite G]
    (P : Sylow p G)
    (χ : PPrimeIrreducibleCharacter G p)
    (ξ : IrreducibleCharacter (SylowNormalizer P))
    (hξ : ξ.TrivialOn (Subgroup.center (SylowNormalizer P))) :
    (normalizerInnerCharacterStabilizerHom P χ).ker ≤
      ξ.realizationLinearEquivHom.ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  apply LinearEquiv.toLinearMap_injective
  rw [ξ.realizationLinearEquivHom_toLinearMap]
  exact
    hξ
      ⟨g,
        mem_normalizer_center_of_mem_innerCharacterStabilizerHom_ker
          P χ g hg⟩

end InductiveMcKay
end McKayConjecture
