/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NumericalReduction
import McKayConjecture.Proof.Isomorphism

/-!
# Transport of local McKay correspondences

A group isomorphism transports the Sylow subgroup and every component of a
local correspondence: its intermediate subgroup, the normalizer containment,
properness, and the bijection on irreducible characters of `p'`-degree.
-/

noncomputable section

universe u

namespace McKayConjecture.InductiveMcKay

variable {X Y : Type u} [Group X] [Group Y] {p : ℕ}

/-! ### Subgroup facts used by transport -/

/-- Mapping the normalizer of a Sylow subgroup along an isomorphism gives
the normalizer of the transported Sylow subgroup. -/
theorem map_normalizer_eq_transport
    (e : X ≃* Y) (Q : Sylow p X) :
    (Subgroup.normalizer (Q : Set X)).map
        e.toMonoidHom =
      Subgroup.normalizer
        (McKayConjecture.Sylow.transport e Q : Set Y) := by
  calc
    (Subgroup.normalizer (Q : Set X)).map
          e.toMonoidHom =
        Subgroup.normalizer
          ((Q : Subgroup X).map e.toMonoidHom : Set Y) :=
      Subgroup.map_equiv_normalizer_eq
        (Q : Subgroup X) e
    _ = Subgroup.normalizer
          (McKayConjecture.Sylow.transport e Q : Set Y) := by
      rw [show
        (Q : Subgroup X).map e.toMonoidHom =
          (McKayConjecture.Sylow.transport e Q :
            Subgroup Y) from
        (McKayConjecture.Sylow.coe_transport e Q).symm]
      exact congrArg Subgroup.normalizer
        (Sylow.coe_coe
          (McKayConjecture.Sylow.transport e Q))

/-- An isomorphism maps a proper subgroup to a proper subgroup. -/
theorem map_lt_top_of_lt_top
    (e : X ≃* Y) {N : Subgroup X}
    (hN : N < ⊤) :
    N.map e.toMonoidHom < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  apply hN.ne
  rw [eq_top_iff]
  intro x _
  apply (Subgroup.mem_map_iff_mem
    (f := e.toMonoidHom) (K := N) e.injective).mp
  rw [htop]
  trivial

namespace LocalCorrespondence

variable {Q : Sylow p X}

/-! ### Transport -/

/-- The isomorphism from an intermediate subgroup to its image in the
transported ambient group. -/
def intermediateEquiv
    (e : X ≃* Y) (d : LocalCorrespondence Q) :
    d.intermediate ≃*
      d.intermediate.map e.toMonoidHom :=
  e.subgroupMap d.intermediate

@[simp]
theorem intermediateEquiv_apply_coe
    (e : X ≃* Y) (d : LocalCorrespondence Q)
    (x : d.intermediate) :
    ((intermediateEquiv e d x :
        d.intermediate.map e.toMonoidHom) : Y) =
      e x :=
  rfl

@[simp]
theorem intermediateEquiv_symm_apply_coe
    (e : X ≃* Y) (d : LocalCorrespondence Q)
    (y : d.intermediate.map e.toMonoidHom) :
    (((intermediateEquiv e d).symm y :
        d.intermediate) : X) =
      e.symm y :=
  rfl

/-- Transport a local correspondence along an isomorphism of ambient
groups. -/
def transport
    (e : X ≃* Y) (Q : Sylow p X)
    (d : LocalCorrespondence Q) :
    LocalCorrespondence
      (McKayConjecture.Sylow.transport e Q) where
  intermediate :=
    d.intermediate.map e.toMonoidHom
  normalizer_le := by
    rw [← map_normalizer_eq_transport e Q]
    exact Subgroup.map_mono d.normalizer_le
  proper_of_normalizer_ne_top := by
    intro hnormalizer
    apply map_lt_top_of_lt_top e
    apply d.proper_of_normalizer_ne_top
    intro htop
    apply hnormalizer
    rw [← map_normalizer_eq_transport e Q, htop]
    exact Subgroup.map_equiv_top e
  correspondence :=
    (IrreducibleCharacter.pPrimeComapEquiv p e).trans
      (d.correspondence.trans
        (IrreducibleCharacter.pPrimeComapEquiv p
          (intermediateEquiv e d).symm))

@[simp]
theorem transport_intermediate
    (e : X ≃* Y) (Q : Sylow p X)
    (d : LocalCorrespondence Q) :
    (transport e Q d).intermediate =
      d.intermediate.map e.toMonoidHom :=
  rfl

@[simp]
theorem transport_correspondence_apply
    (e : X ≃* Y) (Q : Sylow p X)
    (d : LocalCorrespondence Q)
    (χ : PPrimeIrreducibleCharacter Y p) :
    (transport e Q d).correspondence χ =
      IrreducibleCharacter.pPrimeComapEquiv p
        (intermediateEquiv e d).symm
        (d.correspondence
          (IrreducibleCharacter.pPrimeComapEquiv
            p e χ)) :=
  rfl

@[simp]
theorem transport_correspondence_coe
    (e : X ≃* Y) (Q : Sylow p X)
    (d : LocalCorrespondence Q)
    (χ : PPrimeIrreducibleCharacter Y p) :
    ((transport e Q d).correspondence χ).1 =
      (d.correspondence
        (IrreducibleCharacter.pPrimeComapEquiv
          p e χ)).1.comap
        (intermediateEquiv e d).symm :=
  rfl

@[simp]
theorem transport_correspondence_symm_apply
    (e : X ≃* Y) (Q : Sylow p X)
    (d : LocalCorrespondence Q)
    (ψ : PPrimeIrreducibleCharacter
      (transport e Q d).intermediate p) :
    (transport e Q d).correspondence.symm ψ =
      (IrreducibleCharacter.pPrimeComapEquiv
        p e).symm
        (d.correspondence.symm
          ((IrreducibleCharacter.pPrimeComapEquiv p
            (intermediateEquiv e d).symm).symm ψ)) :=
  rfl

/-- Transporting an intermediate subgroup forward and then backward
recovers the original subgroup. -/
@[simp]
theorem transport_symm_intermediate
    (e : X ≃* Y) (Q : Sylow p X)
    (d : LocalCorrespondence Q) :
    (transport e.symm
      (McKayConjecture.Sylow.transport e Q)
      (transport e Q d)).intermediate =
        d.intermediate := by
  rw [transport_intermediate, transport_intermediate,
    Subgroup.map_map]
  have he :
      e.symm.toMonoidHom.comp e.toMonoidHom =
        MonoidHom.id X := by
    ext x
    simp
  rw [he, Subgroup.map_id]

end LocalCorrespondence

end McKayConjecture.InductiveMcKay
