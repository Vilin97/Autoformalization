/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.NormalizedCharacterCertificate

/-!
# Character-row certificates from known simple representations

The normalized character certificate interface is useful both when
irreducibility is established by a direct norm computation and when a
representation has already been proved simple by structural arguments.
This file supplies the latter conversion.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CharacterRowCertificate

variable {G : Type} [Group G] [Finite G]

/-- Package a representation already known to be simple as a normalized
character-row certificate.  The character norm is derived from the
kernel-checked finite-group orthogonality theorem. -/
def ofSimple
    (V : FDRep ℂ G) [Simple V] :
    CharacterRowCertificate G :=
  ofCharacterSum V (by
    letI : Fintype G := Fintype.ofFinite G
    change
      (∑ g : G, V.character g * V.character g⁻¹) =
        (Nat.card G : ℂ)
    exact (FDRep.simple_iff_char_is_norm_one V).mp inferInstance)

@[simp]
theorem ofSimple_representation
    (V : FDRep ℂ G) [Simple V] :
    (ofSimple V).representation = V :=
  rfl

end CharacterRowCertificate
end McKayConjecture
