/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveRepresentation

/-!
# Removing scalar error from projective intertwiners

An operator equivalence which is equivariant up to a nonzero scalar
cochain becomes strictly equivariant after rescaling the source
projective representation by the inverse cochain.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K G V W : Type}
variable [Field K] [Group G]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- Inverse rescaling removes a pointwise scalar discrepancy in an
operator intertwining relation. -/
theorem rescale_inverse_intertwines
    (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W)
    (E : V ≃ₗ[K] W)
    (r : G → Kˣ)
    (h :
      ∀ (g : G) (v : V),
        E (P.operator g v) =
          (r g : K) • Q.operator g (E v))
    (g : G) (v : V) :
    E ((P.rescale (fun x ↦ (r x)⁻¹)).operator g v) =
      Q.operator g (E v) := by
  let s : K := (((r g)⁻¹ : Kˣ) : K)
  change
    E (s • P.operator g v) =
      Q.operator g (E v)
  calc
    E (s • P.operator g v) =
        s • E (P.operator g v) :=
      E.map_smul s _
    _ =
        s •
          ((r g : K) • Q.operator g (E v)) :=
      congrArg (fun y ↦ s • y) (h g v)
    _ = Q.operator g (E v) := by
      rw [smul_smul]
      simp [s]

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
