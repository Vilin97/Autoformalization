/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InertiaQuotientEmbedding

/-!
# The relative-degree boundary above an inertia character

For `N ◁ G`, `θ ∈ Irr(N)`, and `ψ ∈ Irr(I_G(θ) | θ)`, Navarro's
relative-degree theorem says that

`ψ.degree / θ.degree ∣ |I_G(θ) / N|`.

The character-theoretic divisibility theorem is not yet proved in this
file.  Instead, `InertiaRelativeDegreeDivisibility` records its exact,
division-free conclusion on the existing inertia fibre.  The theorems below
close the elementary arithmetic seam: if that conclusion is available,
`θ` has prime-to-`p` degree, and the inertia quotient is a `p′`-group, then
every irreducible character in the inertia fibre has prime-to-`p` degree.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordCorrespondence

open GroupTheory

variable {G : Type} [Group G]

/-- The still-missing relative-degree divisibility input on an inertia
fibre.

The witness `e` is the relative degree `ψ.degree / θ.degree`.  The
division-free equality is the formalization-friendly form of the degree
factorization, while divisibility by the inertia-quotient order is the
specialization of Navarro's relative-degree theorem to `I_G(θ)`. -/
def InertiaRelativeDegreeDivisibility
    (N : Subgroup G) [N.Normal]
    (θ : IrreducibleCharacter N) : Prop :=
  ∀ ψ : IrreducibleCharactersOverInertia N θ,
    ∃ e : ℕ,
      e ∣ Nat.card (IrreducibleCharacter.inertiaQuotient N θ) ∧
        e * θ.degree = ψ.1.degree

/-- Relative-degree divisibility and a prime-to-`p` inertia quotient force
every character above a prime-to-`p` normal character to have prime-to-`p`
degree.

This is only the arithmetic adapter.  Its
`InertiaRelativeDegreeDivisibility` argument is the substantive
character-theoretic input still required from Navarro's theorem. -/
theorem forall_isPPrimeDegree_overInertia_of_relativeDegreeDivisibility
    {p : ℕ} (hp : p.Prime)
    (N : Subgroup G) [N.Normal]
    (θ : IrreducibleCharacter N)
    (hdiv : InertiaRelativeDegreeDivisibility N θ)
    (hθ : θ.IsPPrimeDegree p)
    (hquotient :
      IsPPrimeGroup p
        (IrreducibleCharacter.inertiaQuotient N θ)) :
    ∀ ψ : IrreducibleCharactersOverInertia N θ,
      ψ.1.IsPPrimeDegree p := by
  intro ψ
  obtain ⟨e, he, hdegree⟩ := hdiv ψ
  rw [IrreducibleCharacter.IsPPrimeDegree, ← hdegree,
    hp.dvd_mul, not_or]
  exact
    ⟨fun hpe ↦
        ((isPPrimeGroup_iff_not_dvd
          (G := IrreducibleCharacter.inertiaQuotient N θ) hp).mp
            hquotient)
          (hpe.trans he),
      hθ⟩

/-- Relative-index form of the automatic prime-to-`p` degree adapter.

The relative index here is `|I_G(θ):N|`, not the different Clifford
induction index `|G:I_G(θ)|`. -/
theorem
    forall_isPPrimeDegree_overInertia_of_relativeDegreeDivisibility_of_relIndex
    {p : ℕ} (hp : p.Prime)
    (N : Subgroup G) [N.Normal]
    (θ : IrreducibleCharacter N)
    (hdiv : InertiaRelativeDegreeDivisibility N θ)
    (hθ : θ.IsPPrimeDegree p)
    (hindex :
      ¬p ∣ N.relIndex (IrreducibleCharacter.inertia N θ)) :
    ∀ ψ : IrreducibleCharactersOverInertia N θ,
      ψ.1.IsPPrimeDegree p := by
  apply
    forall_isPPrimeDegree_overInertia_of_relativeDegreeDivisibility
      hp N θ hdiv hθ
  rw [isPPrimeGroup_iff_not_dvd hp]
  exact hindex

end CliffordCorrespondence
end McKayConjecture
