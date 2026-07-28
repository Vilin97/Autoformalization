/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.EquivariantLocal
import McKayConjecture.InductiveMcKay.Transport
import McKayConjecture.CharacterTriple.Transport
import McKayConjecture.InductiveMcKay.Condition

/-!
# Transport of equivariant local McKay correspondences

An isomorphism of ambient groups conjugates their automorphism groups.  It
identifies the stabilizers of corresponding Sylow subgroups, transports an
invariant intermediate subgroup, and preserves equivariance of the local
character correspondence.
-/

noncomputable section

open scoped Pointwise

universe u

namespace McKayConjecture.InductiveMcKay

variable {X Y : Type u} [Group X] [Group Y] {p : ℕ}

/-! ### Conjugating automorphisms and Sylow stabilizers -/

/-- Transporting a Sylow subgroup commutes with conjugating an ambient
automorphism across a group isomorphism. -/
theorem Sylow.transport_smul_congr
    (e : X ≃* Y) (P : Sylow p X) (a : MulAut X) :
    McKayConjecture.Sylow.transport e (a • P) =
      MulAut.congr e a •
        McKayConjecture.Sylow.transport e P := by
  apply Sylow.ext
  simp only [McKayConjecture.Sylow.coe_transport,
    Sylow.pointwise_smul_def,
    Subgroup.pointwise_smul_def]
  change
    ((P : Subgroup X).map a.toMonoidHom).map
        e.toMonoidHom =
      ((P : Subgroup X).map e.toMonoidHom).map
        (MulAut.congr e a).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.congr]

/-- Conjugating an automorphism across an ambient isomorphism preserves
membership in the corresponding Sylow stabilizers. -/
theorem SylowAutStabilizer.congr_mem_iff
    (e : X ≃* Y) (P : Sylow p X) (a : MulAut X) :
    MulAut.congr e a ∈
        SylowAutStabilizer
          (McKayConjecture.Sylow.transport e P) ↔
      a ∈ SylowAutStabilizer P := by
  rw [SylowAutStabilizer.mem_iff,
    SylowAutStabilizer.mem_iff,
    ← Sylow.transport_smul_congr]
  constructor
  · intro h
    have h' := congrArg
      (McKayConjecture.Sylow.transport e.symm) h
    simpa using h'
  · exact fun h ↦ congrArg
      (McKayConjecture.Sylow.transport e) h

/-- Conjugation across an ambient group isomorphism identifies the
automorphism stabilizers of corresponding Sylow subgroups. -/
def sylowAutStabilizerEquiv
    (e : X ≃* Y) (P : Sylow p X) :
    SylowAutStabilizer P ≃*
      SylowAutStabilizer
        (McKayConjecture.Sylow.transport e P) where
  toFun a :=
    ⟨MulAut.congr e a.1,
      (SylowAutStabilizer.congr_mem_iff
        e P a.1).2 a.2⟩
  invFun b :=
    ⟨(MulAut.congr e).symm b.1, by
      apply (SylowAutStabilizer.congr_mem_iff
        e P ((MulAut.congr e).symm b.1)).1
      rw [(MulAut.congr e).apply_symm_apply b.1]
      exact b.2⟩
  left_inv a := by
    apply Subtype.ext
    exact (MulAut.congr e).symm_apply_apply a.1
  right_inv b := by
    apply Subtype.ext
    exact (MulAut.congr e).apply_symm_apply b.1
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (MulAut.congr e) a.1 b.1

@[simp]
theorem sylowAutStabilizerEquiv_apply_coe
    (e : X ≃* Y) (P : Sylow p X)
    (a : SylowAutStabilizer P) :
    (sylowAutStabilizerEquiv e P a).1 =
      MulAut.congr e a.1 :=
  rfl

@[simp]
theorem sylowAutStabilizerEquiv_apply
    (e : X ≃* Y) (P : Sylow p X)
    (a : SylowAutStabilizer P) (y : Y) :
    (sylowAutStabilizerEquiv e P a).1 y =
      e (a.1 (e.symm y)) :=
  rfl

@[simp]
theorem sylowAutStabilizerEquiv_symm_apply_coe
    (e : X ≃* Y) (P : Sylow p X)
    (b : SylowAutStabilizer
      (McKayConjecture.Sylow.transport e P)) :
    ((sylowAutStabilizerEquiv e P).symm b).1 =
      (MulAut.congr e).symm b.1 :=
  rfl

/-! ### Transporting automorphism actions on characters -/

/-- Pullback of `p'`-characters intertwines an automorphism with its
conjugate across a group isomorphism. -/
@[simp]
theorem pPrimeComapEquiv_congr_smul
    (e : X ≃* Y) (q : ℕ) (a : MulAut X)
    (χ : PPrimeIrreducibleCharacter Y q) :
    IrreducibleCharacter.pPrimeComapEquiv q e
        (MulAut.congr e a • χ) =
      a •
        IrreducibleCharacter.pPrimeComapEquiv q e χ := by
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext x
  change
    χ.1.values ((MulAut.congr e a).symm (e x)) =
      χ.1.values (e (a.symm x))
  simp [MulAut.congr]

/-- Covariant form of `pPrimeComapEquiv_congr_smul`, using pullback along
the inverse isomorphism. -/
@[simp]
theorem pPrimeComapEquiv_symm_smul
    (e : X ≃* Y) (q : ℕ) (a : MulAut X)
    (χ : PPrimeIrreducibleCharacter X q) :
    IrreducibleCharacter.pPrimeComapEquiv q e.symm
        (a • χ) =
      MulAut.congr e a •
        IrreducibleCharacter.pPrimeComapEquiv
          q e.symm χ := by
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext y
  change
    χ.1.values (a.symm (e.symm y)) =
      χ.1.values
        (e.symm ((MulAut.congr e a).symm y))
  simp [MulAut.congr]

/-- Ambient character pullback intertwines the actions of corresponding
Sylow automorphism stabilizers. -/
@[simp]
theorem pPrimeComapEquiv_sylowStabilizer_smul
    (e : X ≃* Y) (P : Sylow p X) (q : ℕ)
    (a : SylowAutStabilizer P)
    (χ : PPrimeIrreducibleCharacter Y q) :
    IrreducibleCharacter.pPrimeComapEquiv q e
        (sylowAutStabilizerEquiv e P a • χ) =
      a •
        IrreducibleCharacter.pPrimeComapEquiv q e χ :=
  pPrimeComapEquiv_congr_smul e q a.1 χ

/-- The same intertwining law, indexed by an automorphism in the transported
Sylow stabilizer. -/
@[simp]
theorem pPrimeComapEquiv_sylowStabilizer_symm_smul
    (e : X ≃* Y) (P : Sylow p X) (q : ℕ)
    (b : SylowAutStabilizer
      (McKayConjecture.Sylow.transport e P))
    (χ : PPrimeIrreducibleCharacter Y q) :
    IrreducibleCharacter.pPrimeComapEquiv q e
        (b • χ) =
      (sylowAutStabilizerEquiv e P).symm b •
        IrreducibleCharacter.pPrimeComapEquiv q e χ := by
  have h :=
    pPrimeComapEquiv_sylowStabilizer_smul
      e P q ((sylowAutStabilizerEquiv e P).symm b) χ
  rw [(sylowAutStabilizerEquiv e P).apply_symm_apply b] at h
  exact h

/-! ### Stabilizers of corresponding characters -/

/-- Conjugation identifies the stabilizers of a character and its pullback
across the ambient isomorphism. -/
theorem PPrimeCharacterStabilizer.congr_mem_iff
    (e : X ≃* Y) (P : Sylow p X)
    (χ : PPrimeIrreducibleCharacter Y p)
    (a : SylowAutStabilizer P) :
    sylowAutStabilizerEquiv e P a ∈
        PPrimeCharacterStabilizer
          (McKayConjecture.Sylow.transport e P) χ ↔
      a ∈ PPrimeCharacterStabilizer P
        (IrreducibleCharacter.pPrimeComapEquiv
          p e χ) := by
  rw [PPrimeCharacterStabilizer.mem_iff,
    PPrimeCharacterStabilizer.mem_iff]
  constructor
  · intro h
    calc
      a •
          IrreducibleCharacter.pPrimeComapEquiv
            p e χ =
          IrreducibleCharacter.pPrimeComapEquiv p e
            (sylowAutStabilizerEquiv e P a • χ) :=
        (pPrimeComapEquiv_sylowStabilizer_smul
          e P p a χ).symm
      _ = IrreducibleCharacter.pPrimeComapEquiv
            p e χ := congrArg
        (IrreducibleCharacter.pPrimeComapEquiv p e) h
  · intro h
    apply
      (IrreducibleCharacter.pPrimeComapEquiv
        p e).injective
    calc
      IrreducibleCharacter.pPrimeComapEquiv p e
          (sylowAutStabilizerEquiv e P a • χ) =
          a •
            IrreducibleCharacter.pPrimeComapEquiv
              p e χ :=
        pPrimeComapEquiv_sylowStabilizer_smul
          e P p a χ
      _ = IrreducibleCharacter.pPrimeComapEquiv
            p e χ := h

/-- The induced isomorphism between stabilizers of corresponding
`p'`-characters. -/
def pPrimeCharacterStabilizerEquiv
    (e : X ≃* Y) (P : Sylow p X)
    (χ : PPrimeIrreducibleCharacter Y p) :
    PPrimeCharacterStabilizer P
        (IrreducibleCharacter.pPrimeComapEquiv p e χ) ≃*
      PPrimeCharacterStabilizer
        (McKayConjecture.Sylow.transport e P) χ where
  toFun a :=
    ⟨sylowAutStabilizerEquiv e P a.1,
      (PPrimeCharacterStabilizer.congr_mem_iff
        e P χ a.1).2 a.2⟩
  invFun b :=
    ⟨(sylowAutStabilizerEquiv e P).symm b.1, by
      apply (PPrimeCharacterStabilizer.congr_mem_iff
        e P χ
        ((sylowAutStabilizerEquiv e P).symm b.1)).1
      rw [(sylowAutStabilizerEquiv e P).apply_symm_apply
        b.1]
      exact b.2⟩
  left_inv a := by
    apply Subtype.ext
    exact (sylowAutStabilizerEquiv e P).symm_apply_apply
      a.1
  right_inv b := by
    apply Subtype.ext
    exact (sylowAutStabilizerEquiv e P).apply_symm_apply
      b.1
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (sylowAutStabilizerEquiv e P)
      a.1 b.1

@[simp]
theorem pPrimeCharacterStabilizerEquiv_apply_coe
    (e : X ≃* Y) (P : Sylow p X)
    (χ : PPrimeIrreducibleCharacter Y p)
    (a : PPrimeCharacterStabilizer P
      (IrreducibleCharacter.pPrimeComapEquiv p e χ)) :
    (pPrimeCharacterStabilizerEquiv e P χ a).1 =
      sylowAutStabilizerEquiv e P a.1 :=
  rfl

@[simp]
theorem pPrimeCharacterStabilizerEquiv_symm_apply_coe
    (e : X ≃* Y) (P : Sylow p X)
    (χ : PPrimeIrreducibleCharacter Y p)
    (b : PPrimeCharacterStabilizer
      (McKayConjecture.Sylow.transport e P) χ) :
    ((pPrimeCharacterStabilizerEquiv
      e P χ).symm b).1 =
        (sylowAutStabilizerEquiv e P).symm b.1 :=
  rfl

/-! ### Transporting invariant intermediate subgroups -/

/-- Conjugating an automorphism commutes with mapping a subgroup across the
ambient isomorphism. -/
theorem map_congr_aut_eq
    (e : X ≃* Y) (N : Subgroup X) (a : MulAut X) :
    (N.map e.toMonoidHom).map
        (MulAut.congr e a).toMonoidHom =
      (N.map a.toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.congr]

namespace EquivariantLocalCorrespondence

variable {P : Sylow p X}

/-- The image of an invariant intermediate subgroup is invariant under the
transported Sylow automorphism stabilizer. -/
theorem transportIntermediateInvariant
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P) :
    AutomorphismInvariant
      (SylowAutStabilizer
        (McKayConjecture.Sylow.transport e P))
      (d.intermediate.map e.toMonoidHom) := by
  intro b
  let a : SylowAutStabilizer P :=
    (sylowAutStabilizerEquiv e P).symm b
  have hb :
      sylowAutStabilizerEquiv e P a = b :=
    (sylowAutStabilizerEquiv e P).apply_symm_apply b
  rw [← hb]
  change
    (d.intermediate.map e.toMonoidHom).map
        (MulAut.congr e a.1).toMonoidHom =
      d.intermediate.map e.toMonoidHom
  rw [map_congr_aut_eq]
  exact congrArg
    (fun N : Subgroup X ↦ N.map e.toMonoidHom)
    (d.intermediate_invariant a)

/-- Restriction to the transported intermediate subgroup is the conjugate
of restriction to the original intermediate subgroup. -/
theorem intermediateRestriction_transport
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P)
    (a : SylowAutStabilizer P) :
    MulAut.congr
        (LocalCorrespondence.intermediateEquiv
          e d.toLocalCorrespondence)
        (SylowAutStabilizer.intermediateRestrictionHom
          P d.intermediate d.intermediate_invariant a) =
      SylowAutStabilizer.intermediateRestrictionHom
        (McKayConjecture.Sylow.transport e P)
        (d.intermediate.map e.toMonoidHom)
        (transportIntermediateInvariant e P d)
        (sylowAutStabilizerEquiv e P a) := by
  ext n
  rfl

/-- Character transport between the old and new intermediate subgroups
intertwines their restricted stabilizer actions. -/
@[simp]
theorem pPrimeComapEquiv_intermediate_smul
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P)
    (q : ℕ) (a : SylowAutStabilizer P)
    (ψ : PPrimeIrreducibleCharacter d.intermediate q) :
    letI :=
      SylowAutStabilizer.intermediatePPrimeCharacterMulAction
        P d.intermediate d.intermediate_invariant q
    letI :=
      SylowAutStabilizer.intermediatePPrimeCharacterMulAction
        (McKayConjecture.Sylow.transport e P)
        (d.intermediate.map e.toMonoidHom)
        (transportIntermediateInvariant e P d) q
    IrreducibleCharacter.pPrimeComapEquiv q
        (LocalCorrespondence.intermediateEquiv
          e d.toLocalCorrespondence).symm
        (a • ψ) =
      sylowAutStabilizerEquiv e P a •
        IrreducibleCharacter.pPrimeComapEquiv q
          (LocalCorrespondence.intermediateEquiv
            e d.toLocalCorrespondence).symm ψ := by
  change
    IrreducibleCharacter.pPrimeComapEquiv q
        (LocalCorrespondence.intermediateEquiv
          e d.toLocalCorrespondence).symm
        ((SylowAutStabilizer.intermediateRestrictionHom
          P d.intermediate d.intermediate_invariant a) • ψ) =
      (SylowAutStabilizer.intermediateRestrictionHom
        (McKayConjecture.Sylow.transport e P)
        (d.intermediate.map e.toMonoidHom)
        (transportIntermediateInvariant e P d)
        (sylowAutStabilizerEquiv e P a)) •
          IrreducibleCharacter.pPrimeComapEquiv q
            (LocalCorrespondence.intermediateEquiv
              e d.toLocalCorrespondence).symm ψ
  rw [← intermediateRestriction_transport e P d a]
  exact pPrimeComapEquiv_symm_smul
    (LocalCorrespondence.intermediateEquiv
      e d.toLocalCorrespondence)
    q
    (SylowAutStabilizer.intermediateRestrictionHom
      P d.intermediate d.intermediate_invariant a)
    ψ

/-! ### Transport of equivariant local correspondences -/

/-- Transport an equivariant local correspondence along an isomorphism of
ambient groups. -/
def transport
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P) :
    EquivariantLocalCorrespondence
      (McKayConjecture.Sylow.transport e P) where
  toLocalCorrespondence :=
    LocalCorrespondence.transport
      e P d.toLocalCorrespondence
  intermediate_invariant :=
    transportIntermediateInvariant e P d
  map_smul' := by
    letI := d.intermediateCharacterMulAction
    letI :=
      SylowAutStabilizer.intermediatePPrimeCharacterMulAction
        (McKayConjecture.Sylow.transport e P)
        (d.intermediate.map e.toMonoidHom)
        (transportIntermediateInvariant e P d) p
    intro b χ
    let a : SylowAutStabilizer P :=
      (sylowAutStabilizerEquiv e P).symm b
    change
      IrreducibleCharacter.pPrimeComapEquiv p
          (LocalCorrespondence.intermediateEquiv
            e d.toLocalCorrespondence).symm
          (d.correspondence
            (IrreducibleCharacter.pPrimeComapEquiv
              p e (b • χ))) =
        b •
          IrreducibleCharacter.pPrimeComapEquiv p
            (LocalCorrespondence.intermediateEquiv
              e d.toLocalCorrespondence).symm
            (d.correspondence
              (IrreducibleCharacter.pPrimeComapEquiv
                p e χ))
    rw [pPrimeComapEquiv_sylowStabilizer_symm_smul]
    rw [d.map_smul]
    rw [pPrimeComapEquiv_intermediate_smul]
    rw [(sylowAutStabilizerEquiv e P).apply_symm_apply b]

@[simp]
theorem transport_toLocalCorrespondence
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P) :
    (transport e P d).toLocalCorrespondence =
      LocalCorrespondence.transport
        e P d.toLocalCorrespondence :=
  rfl

@[simp]
theorem transport_intermediate
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P) :
    (transport e P d).intermediate =
      d.intermediate.map e.toMonoidHom :=
  rfl

@[simp]
theorem transport_correspondence_apply
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter Y p) :
    (transport e P d).correspondence χ =
      IrreducibleCharacter.pPrimeComapEquiv p
        (LocalCorrespondence.intermediateEquiv
          e d.toLocalCorrespondence).symm
        (d.correspondence
          (IrreducibleCharacter.pPrimeComapEquiv
            p e χ)) :=
  rfl

@[simp]
theorem transport_map_smul
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P)
    (b : SylowAutStabilizer
      (McKayConjecture.Sylow.transport e P))
    (χ : PPrimeIrreducibleCharacter Y p) :
    letI := (transport e P d).intermediateCharacterMulAction
    (transport e P d).correspondence (b • χ) =
      b • (transport e P d).correspondence χ :=
  (transport e P d).map_smul b χ

/-! ### Isomorphisms of the character-stabilizer semidirect products -/

/-- The ambient semidirect products attached to corresponding characters
are isomorphic. -/
def ambientSemidirectEquiv
    (e : X ≃* Y) (P : Sylow p X)
    (χ : PPrimeIrreducibleCharacter Y p) :
    (X ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer P
          (IrreducibleCharacter.pPrimeComapEquiv p e χ)) ≃*
      (Y ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer
          (McKayConjecture.Sylow.transport e P) χ) :=
  SemidirectProduct.congr e
    (pPrimeCharacterStabilizerEquiv e P χ) (by
      intro a
      ext x
      change
        e (a.1.1 x) =
          (sylowAutStabilizerEquiv e P a.1).1
            (e x)
      simp)

@[simp]
theorem ambientSemidirectEquiv_apply_left
    (e : X ≃* Y) (P : Sylow p X)
    (χ : PPrimeIrreducibleCharacter Y p)
    (z :
      X ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer P
          (IrreducibleCharacter.pPrimeComapEquiv p e χ)) :
    (ambientSemidirectEquiv e P χ z).left =
      e z.left :=
  rfl

@[simp]
theorem ambientSemidirectEquiv_apply_right
    (e : X ≃* Y) (P : Sylow p X)
    (χ : PPrimeIrreducibleCharacter Y p)
    (z :
      X ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer P
          (IrreducibleCharacter.pPrimeComapEquiv p e χ)) :
    (ambientSemidirectEquiv e P χ z).right =
      pPrimeCharacterStabilizerEquiv e P χ z.right :=
  rfl

@[simp]
theorem ambientSemidirectEquiv_symm_apply_left
    (e : X ≃* Y) (P : Sylow p X)
    (χ : PPrimeIrreducibleCharacter Y p)
    (z :
      Y ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer
          (McKayConjecture.Sylow.transport e P) χ) :
    ((ambientSemidirectEquiv e P χ).symm z).left =
      e.symm z.left :=
  rfl

@[simp]
theorem ambientSemidirectEquiv_symm_apply_right
    (e : X ≃* Y) (P : Sylow p X)
    (χ : PPrimeIrreducibleCharacter Y p)
    (z :
      Y ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer
          (McKayConjecture.Sylow.transport e P) χ) :
    ((ambientSemidirectEquiv e P χ).symm z).right =
      (pPrimeCharacterStabilizerEquiv
        e P χ).symm z.right :=
  rfl

/-- The intermediate semidirect products attached to corresponding
characters are isomorphic. -/
def intermediateSemidirectEquiv
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter Y p) :
    (d.intermediate ⋊[
        d.stabilizerIntermediateAction
          (IrreducibleCharacter.pPrimeComapEquiv p e χ)]
        PPrimeCharacterStabilizer P
          (IrreducibleCharacter.pPrimeComapEquiv p e χ)) ≃*
      ((transport e P d).intermediate ⋊[
        (transport e P d).stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer
          (McKayConjecture.Sylow.transport e P) χ) :=
  SemidirectProduct.congr
    (LocalCorrespondence.intermediateEquiv
      e d.toLocalCorrespondence)
    (pPrimeCharacterStabilizerEquiv e P χ) (by
      intro a
      ext n
      change
        e (a.1.1 n.1) =
          (sylowAutStabilizerEquiv e P a.1).1
            (e n.1)
      simp)

@[simp]
theorem intermediateSemidirectEquiv_apply_left
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter Y p)
    (z :
      d.intermediate ⋊[d.stabilizerIntermediateAction
          (IrreducibleCharacter.pPrimeComapEquiv p e χ)]
        PPrimeCharacterStabilizer P
          (IrreducibleCharacter.pPrimeComapEquiv p e χ)) :
    (intermediateSemidirectEquiv e P d χ z).left =
      LocalCorrespondence.intermediateEquiv
        e d.toLocalCorrespondence z.left :=
  rfl

@[simp]
theorem intermediateSemidirectEquiv_apply_right
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter Y p)
    (z :
      d.intermediate ⋊[d.stabilizerIntermediateAction
          (IrreducibleCharacter.pPrimeComapEquiv p e χ)]
        PPrimeCharacterStabilizer P
          (IrreducibleCharacter.pPrimeComapEquiv p e χ)) :
    (intermediateSemidirectEquiv e P d χ z).right =
      pPrimeCharacterStabilizerEquiv
        e P χ z.right :=
  rfl

@[simp]
theorem intermediateSemidirectEquiv_symm_apply_left
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter Y p)
    (z :
      (transport e P d).intermediate ⋊[(transport e P d).stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer
          (McKayConjecture.Sylow.transport e P) χ) :
    ((intermediateSemidirectEquiv
      e P d χ).symm z).left =
        (LocalCorrespondence.intermediateEquiv
          e d.toLocalCorrespondence).symm z.left :=
  rfl

@[simp]
theorem intermediateSemidirectEquiv_symm_apply_right
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter Y p)
    (z :
      (transport e P d).intermediate ⋊[(transport e P d).stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer
          (McKayConjecture.Sylow.transport e P) χ) :
    ((intermediateSemidirectEquiv
      e P d χ).symm z).right =
        (pPrimeCharacterStabilizerEquiv
          e P χ).symm z.right :=
  rfl

/-- Relabelling the old canonical semidirect embedding gives the canonical
embedding for the transported datum. -/
theorem semidirectEmbedding_transport_apply
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter Y p)
    (z :
      (transport e P d).intermediate ⋊[(transport e P d).stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer
          (McKayConjecture.Sylow.transport e P) χ) :
    ambientSemidirectEquiv e P χ
        (d.semidirectEmbedding
          (IrreducibleCharacter.pPrimeComapEquiv p e χ)
          ((intermediateSemidirectEquiv
            e P d χ).symm z)) =
      (transport e P d).semidirectEmbedding χ z := by
  apply SemidirectProduct.ext
  · rw [(transport e P d).semidirectEmbedding_left]
    rw [ambientSemidirectEquiv_apply_left,
      d.semidirectEmbedding_left]
    rw [intermediateSemidirectEquiv_symm_apply_left]
    change e (e.symm (z.left : Y)) = (z.left : Y)
    exact e.apply_symm_apply _
  · rw [(transport e P d).semidirectEmbedding_right]
    rw [ambientSemidirectEquiv_apply_right,
      d.semidirectEmbedding_right]
    rw [intermediateSemidirectEquiv_symm_apply_right]
    exact (pPrimeCharacterStabilizerEquiv
      e P χ).apply_symm_apply z.right

/-- Monoid-hom form of `semidirectEmbedding_transport_apply`. -/
theorem semidirectEmbedding_transport
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter Y p) :
    (ambientSemidirectEquiv e P χ).toMonoidHom.comp
        ((d.semidirectEmbedding
          (IrreducibleCharacter.pPrimeComapEquiv p e χ)).comp
          (intermediateSemidirectEquiv
            e P d χ).symm.toMonoidHom) =
      (transport e P d).semidirectEmbedding χ := by
  apply MonoidHom.ext
  intro z
  exact semidirectEmbedding_transport_apply
    e P d χ z

/-! ### Relabelling the semidirect character triples -/

private theorem characterTriple_ext
    {A : Type u} [Finite A] [Group A]
    {T U : CharacterTriple A}
    (hN : T.normalSubgroup = U.normalSubgroup)
    (hχ : HEq T.character U.character) :
    T = U := by
  cases T
  cases U
  cases hN
  cases eq_of_heq hχ
  rfl

private theorem comap_subgroupCongr_heq
    {A : Type u} [Group A]
    {H K : Subgroup A} (h : H = K)
    (χ : IrreducibleCharacter K) :
    HEq (χ.comap (MulEquiv.subgroupCongr h)) χ := by
  cases h
  apply heq_of_eq
  exact IrreducibleCharacter.comap_refl χ

private theorem characterTriple_ext_comap
    {A : Type u} [Finite A] [Group A]
    {T U : CharacterTriple A}
    (hN : T.normalSubgroup = U.normalSubgroup)
    (hχ :
      T.character =
        U.character.comap
          (MulEquiv.subgroupCongr hN)) :
    T = U := by
  apply characterTriple_ext hN
  exact (heq_of_eq hχ).trans
    (comap_subgroupCongr_heq hN U.character)

/-- The canonical normal subgroup in the ambient semidirect product is
preserved by the semidirect-product relabelling. -/
theorem ambientTriple_transport_normalSubgroup
    [Finite X] [Finite Y]
    (e : X ≃* Y) (P : Sylow p X)
    (χ : PPrimeIrreducibleCharacter Y p) :
    ((ambientTriple (P := P)
        (IrreducibleCharacter.pPrimeComapEquiv
          p e χ)).comap
        (ambientSemidirectEquiv e P χ).symm).normalSubgroup =
      (ambientTriple
        (P := McKayConjecture.Sylow.transport e P)
        χ).normalSubgroup := by
  change
    (MonoidHom.range
      (SemidirectProduct.inl :
        X →*
          (X ⋊[PPrimeCharacterStabilizer.ambientAction]
            PPrimeCharacterStabilizer P
              (IrreducibleCharacter.pPrimeComapEquiv
                p e χ)))).comap
        (ambientSemidirectEquiv
          e P χ).symm.toMonoidHom =
      MonoidHom.range
        (SemidirectProduct.inl :
          Y →*
            (Y ⋊[PPrimeCharacterStabilizer.ambientAction]
              PPrimeCharacterStabilizer
                (McKayConjecture.Sylow.transport e P) χ))
  rw [SemidirectProduct.range_inl_eq_ker_rightHom,
    SemidirectProduct.range_inl_eq_ker_rightHom]
  ext z
  simp

/-- The canonical normal subgroup in the intermediate semidirect product is
preserved by relabelling. -/
theorem intermediateTriple_transport_normalSubgroup
    [Finite X] [Finite Y]
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter Y p) :
    ((d.intermediateTriple
        (IrreducibleCharacter.pPrimeComapEquiv
          p e χ)).comap
        (intermediateSemidirectEquiv
          e P d χ).symm).normalSubgroup =
      ((transport e P d).intermediateTriple
        χ).normalSubgroup := by
  change
    (MonoidHom.range
      (SemidirectProduct.inl :
        d.intermediate →*
          (d.intermediate ⋊[
            d.stabilizerIntermediateAction
              (IrreducibleCharacter.pPrimeComapEquiv p e χ)]
            PPrimeCharacterStabilizer P
              (IrreducibleCharacter.pPrimeComapEquiv
                p e χ)))).comap
        (intermediateSemidirectEquiv
          e P d χ).symm.toMonoidHom =
      MonoidHom.range
        (SemidirectProduct.inl :
          (transport e P d).intermediate →*
            ((transport e P d).intermediate ⋊[
              (transport e P d).stabilizerIntermediateAction χ]
              PPrimeCharacterStabilizer
                (McKayConjecture.Sylow.transport e P) χ))
  rw [SemidirectProduct.range_inl_eq_ker_rightHom,
    SemidirectProduct.range_inl_eq_ker_rightHom]
  ext z
  change
    ((intermediateSemidirectEquiv
      e P d χ).symm z).right = 1 ↔
        z.right = 1
  rw [intermediateSemidirectEquiv_symm_apply_right]
  simp

/-- Relabelling the old ambient semidirect character triple gives the
ambient triple attached to the transported character. -/
theorem ambientTriple_transport
    [Finite X] [Finite Y]
    (e : X ≃* Y) (P : Sylow p X)
    (χ : PPrimeIrreducibleCharacter Y p) :
    (ambientTriple (P := P)
        (IrreducibleCharacter.pPrimeComapEquiv
          p e χ)).comap
        (ambientSemidirectEquiv e P χ).symm =
      ambientTriple
        (P := McKayConjecture.Sylow.transport e P)
        χ := by
  have hN :=
    ambientTriple_transport_normalSubgroup
      e P χ
  apply characterTriple_ext_comap hN
  apply IrreducibleCharacter.ext
  funext z
  change
    χ.1.values
        (e ((ambientSemidirectEquiv
          e P χ).symm z.1).left) =
      χ.1.values z.1.left
  rw [ambientSemidirectEquiv_symm_apply_left,
    e.apply_symm_apply]

/-- Relabelling the old intermediate semidirect character triple gives the
intermediate triple of the transported local correspondence. -/
theorem intermediateTriple_transport
    [Finite X] [Finite Y]
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter Y p) :
    (d.intermediateTriple
        (IrreducibleCharacter.pPrimeComapEquiv
          p e χ)).comap
        (intermediateSemidirectEquiv
          e P d χ).symm =
      (transport e P d).intermediateTriple χ := by
  have hN :=
    intermediateTriple_transport_normalSubgroup
      e P d χ
  apply characterTriple_ext_comap hN
  apply IrreducibleCharacter.ext
  funext z
  change
    (d.correspondence
      (IrreducibleCharacter.pPrimeComapEquiv
        p e χ)).1.values
        ((intermediateSemidirectEquiv
          e P d χ).symm z.1).left =
      (d.correspondence
        (IrreducibleCharacter.pPrimeComapEquiv
          p e χ)).1.values
        ((LocalCorrespondence.intermediateEquiv
          e d.toLocalCorrespondence).symm z.1.left)
  rw [intermediateSemidirectEquiv_symm_apply_left]

/-- Character-triple compatibility is preserved by transport of the
equivariant local correspondence. -/
theorem tripleCompatible_transport
    [Finite X] [Finite Y]
    (e : X ≃* Y) (P : Sylow p X)
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter Y p)
    (h :
      d.TripleCompatible
        (IrreducibleCharacter.pPrimeComapEquiv
          p e χ)) :
    (transport e P d).TripleCompatible χ := by
  rcases h with
    ⟨V, W, _, _, _, _, _, _, _, _, C, hC⟩
  refine ⟨V, W, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_⟩
  rw [← ambientTriple_transport e P χ,
    ← intermediateTriple_transport e P d χ]
  refine ⟨C.comap
    (ambientSemidirectEquiv e P χ).symm
    (intermediateSemidirectEquiv
      e P d χ).symm, ?_⟩
  change
    (ambientSemidirectEquiv e P χ).toMonoidHom.comp
        (C.embedding.comp
          (intermediateSemidirectEquiv
            e P d χ).symm.toMonoidHom) =
      (transport e P d).semidirectEmbedding χ
  rw [hC]
  exact semidirectEmbedding_transport
    e P d χ

end EquivariantLocalCorrespondence

namespace LocalInductiveMcKayData

/-- Transport the full local inductive-McKay datum, including all
character-triple compatibility witnesses, along an ambient group
isomorphism. -/
def transport
    [Finite X] [Finite Y]
    (e : X ≃* Y) (P : Sylow p X)
    (d : LocalInductiveMcKayData P) :
    LocalInductiveMcKayData
      (McKayConjecture.Sylow.transport e P) where
  toEquivariantLocalCorrespondence :=
    d.toEquivariant.transport e P
  triple_compatible := by
    intro χ
    exact
      EquivariantLocalCorrespondence.tripleCompatible_transport
        e P d.toEquivariant χ
        (d.triple_compatible
          (IrreducibleCharacter.pPrimeComapEquiv
            p e χ))

@[simp]
theorem transport_toEquivariant
    [Finite X] [Finite Y]
    (e : X ≃* Y) (P : Sylow p X)
    (d : LocalInductiveMcKayData P) :
    (transport e P d).toEquivariant =
      d.toEquivariant.transport e P :=
  rfl

@[simp]
theorem transport_toLocal
    [Finite X] [Finite Y]
    (e : X ≃* Y) (P : Sylow p X)
    (d : LocalInductiveMcKayData P) :
    (transport e P d).toLocal =
      LocalCorrespondence.transport
        e P d.toLocal :=
  rfl

end LocalInductiveMcKayData

end McKayConjecture.InductiveMcKay
