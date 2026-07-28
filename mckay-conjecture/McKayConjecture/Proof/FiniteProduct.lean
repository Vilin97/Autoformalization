/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FiniteProductCorrespondence
import McKayConjecture.GroupTheory.SylowPi
import McKayConjecture.Proof.Correspondence

/-!
# McKay correspondences for finite indexed products

Explicit McKay correspondences for the factors of a finite indexed
product combine into an explicit correspondence for the product.  The
construction uses the finite external-tensor classification of
irreducible characters and the coordinatewise description of the
normalizer of the product Sylow subgroup.
-/

noncomputable section

namespace McKayConjecture

variable {ι : Type} [Fintype ι]
variable {G : ι → Type} [∀ i, Finite (G i)]
variable [∀ i, Group (G i)]
variable {p : ℕ} [Fact p.Prime]

namespace McKayCorrespondence

/-- A finite indexed product of explicit McKay correspondences. -/
def finiteProduct
    (P : ∀ i, Sylow p (G i))
    (e : ∀ i, McKayCorrespondence (G i) p (P i)) :
    McKayCorrespondence (∀ i, G i) p
      (GroupTheory.Sylow.pi P) :=
  (IrreducibleCharacter.finiteProductPPrimeEquiv G p).symm
    |>.trans (Equiv.piCongrRight e)
    |>.trans
      (IrreducibleCharacter.finiteProductPPrimeEquiv
        (fun i ↦ SylowNormalizer (P i)) p)
    |>.trans
      (IrreducibleCharacter.pPrimeComapEquiv p
        (GroupTheory.Subgroup.normalizerPiMulEquiv
          (fun i ↦ (P i : Subgroup (G i)))))

end McKayCorrespondence

namespace Statement

omit [Fintype ι] in
/-- The McKay statement for a finite indexed product follows from
explicit McKay correspondences for all its factors. -/
theorem of_finiteProduct_correspondences
    [Finite ι]
    (P : ∀ i, Sylow p (G i))
    (e : ∀ i, McKayCorrespondence (G i) p (P i)) :
    Statement (∀ i, G i) p
      (GroupTheory.Sylow.pi P) := by
  letI : Fintype ι := Fintype.ofFinite ι
  exact Statement.of_correspondence
    (McKayCorrespondence.finiteProduct P e)

end Statement

end McKayConjecture
