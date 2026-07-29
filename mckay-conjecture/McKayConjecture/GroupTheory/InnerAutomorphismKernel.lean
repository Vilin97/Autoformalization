/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-!
# The kernel of the inner-automorphism map

Conjugation by an element is the identity automorphism exactly when that
element is central.  Combined with the first isomorphism theorem, the
kernel equality below identifies the group of inner automorphisms with the
quotient by the center.
-/

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G]

/-- The kernel of the conjugation homomorphism is the center. -/
theorem mulAutConj_ker_eq_center :
    (MulAut.conj : G →* MulAut G).ker =
      Subgroup.center G := by
  ext z
  simp only [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro hz g
    have hzg :=
      DFunLike.congr_fun hz g
    have hconj :
        z * g * z⁻¹ = g := by
      simpa [MulAut.conj_apply] using hzg
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  · intro hz
    apply MulEquiv.ext
    intro g
    rw [MulAut.conj_apply]
    change z * g * z⁻¹ = g
    rw [mul_inv_eq_iff_eq_mul]
    exact (hz g).symm

end GroupTheory
end McKayConjecture
