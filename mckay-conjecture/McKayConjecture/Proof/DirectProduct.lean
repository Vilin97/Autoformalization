/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DirectProductCorrespondence
import McKayConjecture.GroupTheory.SylowProduct
import McKayConjecture.Proof.Correspondence

/-!
# McKay correspondences for direct products

An explicit McKay correspondence for each factor gives one for their direct
product.  The construction uses the external-tensor-product classification of
irreducible characters and the product description of the Sylow normalizer.
-/

noncomputable section

namespace McKayConjecture

variable {G H : Type} [Group G] [Group H]
variable {p : ℕ} [Fact p.Prime]
variable {P : Sylow p G} {Q : Sylow p H}

namespace McKayCorrespondence

/-- The product of two explicit McKay correspondences. -/
def prod
    [Finite G] [Finite H]
    (eG : McKayCorrespondence G p P)
    (eH : McKayCorrespondence H p Q) :
    McKayCorrespondence (G × H) p
      (GroupTheory.sylowProduct P Q) :=
  (IrreducibleCharacter.directProductPPrimeEquiv
      (G := G) (H := H) p).symm
    |>.trans (Equiv.prodCongr eG eH)
    |>.trans
      (IrreducibleCharacter.directProductPPrimeEquiv
        (G := SylowNormalizer P)
        (H := SylowNormalizer Q) p)
    |>.trans
      (IrreducibleCharacter.pPrimeComapEquiv p
        (GroupTheory.sylowProductNormalizerEquiv P Q))

end McKayCorrespondence

namespace Statement

/-- The McKay statement for a direct product follows from explicit McKay
correspondences for both factors. -/
theorem of_product_correspondences
    [Finite G] [Finite H]
    (eG : McKayCorrespondence G p P)
    (eH : McKayCorrespondence H p Q) :
    Statement (G × H) p
      (GroupTheory.sylowProduct P Q) :=
  Statement.of_correspondence
    (McKayCorrespondence.prod eG eH)

end Statement

end McKayConjecture
