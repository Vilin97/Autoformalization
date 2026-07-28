/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Proof.Correspondence

/-!
# Isomorphism invariance of the McKay correspondence

This file transports Sylow subgroups, their normalizers, and McKay character
correspondences along group isomorphisms.  It makes explicit that the theorem
depends only on the finite group up to isomorphism, rather than on a chosen
underlying type.
-/

noncomputable section

universe u v

namespace McKayConjecture

variable {G : Type u} {H : Type v}
variable [Group G] [Group H] {p : ℕ}

namespace Sylow

/-- Transport a Sylow subgroup along a group isomorphism. -/
def transport (e : G ≃* H) (P : Sylow p G) : Sylow p H :=
  P.comapOfInjective e.symm.toMonoidHom e.symm.injective
    (by
      intro x hx
      exact ⟨e x, by simp⟩)

/-- The subgroup underlying a transported Sylow subgroup is the image of the
original subgroup. -/
@[simp]
theorem coe_transport (e : G ≃* H) (P : Sylow p G) :
    (transport e P : Subgroup H) = (P : Subgroup G).map e.toMonoidHom := by
  change (P : Subgroup G).comap e.symm.toMonoidHom =
    (P : Subgroup G).map e.toMonoidHom
  exact Subgroup.comap_equiv_eq_map_symm e.symm (P : Subgroup G)

@[simp]
theorem transport_refl (P : Sylow p G) :
    transport (MulEquiv.refl G) P = P := by
  apply Sylow.ext
  simp

@[simp]
theorem transport_symm_transport (e : G ≃* H) (P : Sylow p G) :
    transport e.symm (transport e P) = P := by
  apply Sylow.ext
  rw [coe_transport, coe_transport, Subgroup.map_map]
  have he :
      e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext
    simp
  rw [he, Subgroup.map_id]

open scoped Pointwise in
/-- Transport along an inner automorphism agrees with the usual conjugation
action on Sylow subgroups. -/
@[simp]
theorem transport_conj (g : G) (P : Sylow p G) :
    transport (MulAut.conj g) P = g • P := by
  apply Sylow.ext
  rw [coe_transport]
  rfl

/-- A group isomorphism restricts to an isomorphism between the corresponding
Sylow normalizers. -/
def normalizerEquiv (e : G ≃* H) (P : Sylow p G) :
    SylowNormalizer P ≃* SylowNormalizer (transport e P) :=
  ((Subgroup.normalizer (P : Set G)).equivMapOfInjective
      e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (by
      calc
        (Subgroup.normalizer (P : Set G)).map e.toMonoidHom =
            Subgroup.normalizer
              ((P : Subgroup G).map e.toMonoidHom : Set H) :=
          Subgroup.map_equiv_normalizer_eq (P : Subgroup G) e
        _ = Subgroup.normalizer (transport e P : Set H) := by
          rw [show (P : Subgroup G).map e.toMonoidHom =
            (transport e P : Subgroup H) from (coe_transport e P).symm]
          exact congrArg Subgroup.normalizer (Sylow.coe_coe (transport e P))))

@[simp]
theorem normalizerEquiv_apply_coe (e : G ≃* H) (P : Sylow p G)
    (x : SylowNormalizer P) :
    ((normalizerEquiv e P x :
        SylowNormalizer (transport e P)) : H) = e x :=
  rfl

end Sylow

namespace McKayCorrespondence

/-- Transport a McKay correspondence along an isomorphism of ambient groups. -/
def transport (e : G ≃* H) (P : Sylow p G)
    (f : McKayCorrespondence G p P) :
    McKayCorrespondence H p (Sylow.transport e P) :=
  (IrreducibleCharacter.pPrimeComapEquiv p e).trans
    (f.trans
      (IrreducibleCharacter.pPrimeComapEquiv p
        (Sylow.normalizerEquiv e P).symm))

end McKayCorrespondence

namespace Statement

/-- The McKay cardinal equality is invariant under isomorphism of the
ambient finite group. -/
theorem transport [Finite G] [Finite H] [Fact p.Prime]
    (e : G ≃* H) (P : Sylow p G) (h : Statement G p P) :
    Statement H p (Sylow.transport e P) := by
  let eG :
      PPrimeIrreducibleCharacter H p ≃
        PPrimeIrreducibleCharacter G p :=
    IrreducibleCharacter.pPrimeComapEquiv p e
  let eN :
      PPrimeIrreducibleCharacter (SylowNormalizer P) p ≃
        PPrimeIrreducibleCharacter
          (SylowNormalizer (Sylow.transport e P)) p :=
    IrreducibleCharacter.pPrimeComapEquiv p
      (Sylow.normalizerEquiv e P).symm
  apply Cardinal.lift_injective
  calc
    Cardinal.lift
        (Cardinal.mk (PPrimeIrreducibleCharacter H p)) =
      Cardinal.lift
        (Cardinal.mk (PPrimeIrreducibleCharacter G p)) :=
      eG.lift_cardinal_eq
    _ = Cardinal.lift
        (Cardinal.mk
          (PPrimeIrreducibleCharacter (SylowNormalizer P) p)) :=
      congrArg Cardinal.lift h
    _ = Cardinal.lift
        (Cardinal.mk
          (PPrimeIrreducibleCharacter
            (SylowNormalizer (Sylow.transport e P)) p)) :=
      eN.lift_cardinal_eq

/-- Isomorphic finite groups satisfy the corresponding McKay statements
simultaneously. -/
theorem transport_iff [Finite G] [Finite H] [Fact p.Prime]
    (e : G ≃* H) (P : Sylow p G) :
    Statement G p P ↔ Statement H p (Sylow.transport e P) := by
  constructor
  · exact transport e P
  · intro h
    simpa using
      transport e.symm (Sylow.transport e P) h

end Statement

end McKayConjecture
