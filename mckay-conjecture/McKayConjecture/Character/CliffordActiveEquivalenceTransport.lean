/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ActiveEquivalenceTransport
import McKayConjecture.Character.ActiveOrbitTransport
import McKayConjecture.Character.CliffordActivePartition

/-!
# Transport of active Clifford partitions along group equivalences

A commuting equivalence between an ambient finite group and a normal
subgroup transports conjugacy orbits, prime-to-`p` Clifford blocks, and
the exact active-orbit partition.  This file packages those transports and
identifies the assembled blockwise equivalence with ordinary pullback of
ambient characters.

The construction is useful when the equivalence is conjugation by an
element normalizing both the ambient subgroup and its normal subgroup.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordPartition

open CliffordCorrespondence
open CliffordEquivalence

variable {G G' : Type} [Group G] [Group G']
variable [Finite G] [Finite G']
variable (K : Subgroup G) [K.Normal]
variable (K' : Subgroup G') [K'.Normal]

noncomputable local instance cliffordEquivalenceTransportFintypeG :
    Fintype G :=
  Fintype.ofFinite G

noncomputable local instance cliffordEquivalenceTransportFintypeG' :
    Fintype G' :=
  Fintype.ofFinite G'

/-- Pullback of normal-subgroup characters intertwines the two ambient
conjugation actions. -/
theorem comapEquiv_conjBy
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom)
    (g : G')
    (θ : IrreducibleCharacter K) :
    IrreducibleCharacter.comapEquiv eK
        ((eG g) • θ) =
      g •
        IrreducibleCharacter.comapEquiv eK θ := by
  apply IrreducibleCharacter.ext
  funext k
  change
    θ.values
        ((MulAut.conjNormal (H := K) (eG g)).symm
          (eK k)) =
      θ.values
        (eK
          ((MulAut.conjNormal (H := K') g).symm k))
  congr 1
  apply Subtype.ext
  have hpoint :=
    congrArg
      (fun f : K' →* G ↦
        f ((MulAut.conjNormal (H := K') g).symm k))
      hcomm
  have hk :=
    congrArg (fun f : K' →* G ↦ f k) hcomm
  change eG (k : G') = (eK k : K) at hk
  simp only [MulAut.conjNormal_symm_apply]
  change
    (eG g)⁻¹ * (eK k : G) * eG g =
      (eK
        ((MulAut.conjNormal (H := K') g).symm k) : G)
  rw [← hk]
  simpa using hpoint

/-- Prime-to-`p` form of `comapEquiv_conjBy`. -/
theorem pPrimeComapEquiv_conjBy
    (p : ℕ)
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom)
    (g : G')
    (θ : PPrimeIrreducibleCharacter K p) :
    IrreducibleCharacter.pPrimeComapEquiv p eK
        ((eG g) • θ) =
      g •
        IrreducibleCharacter.pPrimeComapEquiv p eK θ := by
  apply Subtype.ext
  exact comapEquiv_conjBy K K' eG eK hcomm g θ.1

/-- Relabelling both the ambient group and its normal subgroup transports
the ambient conjugacy-orbit space of irreducible subgroup characters. -/
def orbitSpaceComapEquiv
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom) :
    OrbitSpace K ≃ OrbitSpace K' :=
  Quotient.congr
    (IrreducibleCharacter.comapEquiv eK)
    (fun θ ψ ↦ by
      simp only [MulAction.orbitRel_apply,
        MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨g, hg⟩
        refine ⟨eG.symm g, ?_⟩
        rw [← comapEquiv_conjBy
          K K' eG eK hcomm (eG.symm g) ψ]
        simpa using
          congrArg
            (IrreducibleCharacter.comapEquiv eK) hg
      · rintro ⟨g, hg⟩
        refine ⟨eG g, ?_⟩
        apply (IrreducibleCharacter.comapEquiv eK).injective
        rw [comapEquiv_conjBy
          K K' eG eK hcomm g ψ]
        exact hg)

@[simp]
theorem orbitSpaceComapEquiv_mk
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom)
    (θ : IrreducibleCharacter K) :
    orbitSpaceComapEquiv K K' eG eK hcomm
        (Quotient.mk'' θ) =
      Quotient.mk'' (θ.comap eK) :=
  rfl

/-- Reversing a commuting square of ambient and subgroup equivalences gives
the corresponding commuting square for the inverse equivalences. -/
theorem subgroupEquivalenceSquare_symm
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom) :
    eG.symm.toMonoidHom.comp K.subtype =
      K'.subtype.comp eK.symm.toMonoidHom := by
  apply MonoidHom.ext
  intro k
  have hpoint :=
    congrArg
      (fun f : K' →* G ↦ f (eK.symm k))
      hcomm
  apply eG.injective
  change
    eG (eG.symm (k : G)) =
      eG ((eK.symm k : K') : G')
  rw [eG.apply_symm_apply]
  simpa using hpoint.symm

/-- The chosen representative of the transported orbit belongs to the
same target orbit as the literal pullback of the source representative. -/
theorem orbitSpaceComapEquiv_out_eq
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom)
    (q : OrbitSpace K) :
    (Quotient.mk''
        (orbitSpaceComapEquiv K K' eG eK hcomm q).out :
          OrbitSpace K') =
      Quotient.mk'' (q.out.comap eK) := by
  calc
    (Quotient.mk''
        (orbitSpaceComapEquiv K K' eG eK hcomm q).out :
          OrbitSpace K') =
        orbitSpaceComapEquiv K K' eG eK hcomm q :=
      Quotient.out_eq' _
    _ = Quotient.mk'' (q.out.comap eK) := by
      calc
        orbitSpaceComapEquiv K K' eG eK hcomm q =
            orbitSpaceComapEquiv K K' eG eK hcomm
              (Quotient.mk'' q.out) := by
          exact congrArg
            (orbitSpaceComapEquiv K K' eG eK hcomm)
            (Quotient.out_eq' q).symm
        _ = Quotient.mk'' (q.out.comap eK) :=
          orbitSpaceComapEquiv_mk
            K K' eG eK hcomm q.out

@[simp]
theorem orbitSpaceComapEquiv_symm_mk
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom)
    (θ : IrreducibleCharacter K') :
    (orbitSpaceComapEquiv K K' eG eK hcomm).symm
        (Quotient.mk'' θ) =
      Quotient.mk'' (θ.comap eK.symm) := by
  apply (orbitSpaceComapEquiv K K' eG eK hcomm).injective
  rw [(orbitSpaceComapEquiv
    K K' eG eK hcomm).apply_symm_apply]
  change
    Quotient.mk'' θ =
      Quotient.mk'' ((θ.comap eK.symm).comap eK)
  simp

/-- Simultaneous pullback of the ambient and normal-subgroup characters
transports one prime-to-`p` Clifford orbit block. -/
def pPrimeOrbitBlockComapEquiv
    (p : ℕ)
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom)
    (q : OrbitSpace K) :
    PPrimeOrbitBlock K p q ≃
      PPrimeOrbitBlock K' p
        (orbitSpaceComapEquiv K K' eG eK hcomm q) where
  toFun χ := by
    refine ⟨⟨χ.1.1.comap eG, ?_⟩, χ.2⟩
    apply
      (liesOverOrbit_iff_of_quotient_mk_eq
        K'
        (orbitSpaceComapEquiv_out_eq
          K K' eG eK hcomm q)
        (χ.1.1.comap eG)).mpr
    apply liesOverOrbit_of_liesOver K'
    exact
      (liesOverAlong_comap_equiv_iff
        eG eK K.subtype K'.subtype hcomm
        q.out χ.1.1).mpr
        ((liesOverOrbit_iff_liesOver
          K q.out χ.1.1).mp χ.1.2)
  invFun χ := by
    let q' :=
      orbitSpaceComapEquiv K K' eG eK hcomm q
    let hcomm' :=
      subgroupEquivalenceSquare_symm
        K K' eG eK hcomm
    refine ⟨⟨χ.1.1.comap eG.symm, ?_⟩, χ.2⟩
    apply
      (liesOverOrbit_iff_of_quotient_mk_eq
        K
        (show
          (Quotient.mk'' q.out : OrbitSpace K) =
            Quotient.mk'' (q'.out.comap eK.symm) by
          calc
            (Quotient.mk'' q.out : OrbitSpace K) = q :=
              Quotient.out_eq' q
            _ =
                (orbitSpaceComapEquiv
                  K K' eG eK hcomm).symm q' := by
              exact
                (orbitSpaceComapEquiv
                  K K' eG eK hcomm).symm_apply_apply q |>.symm
            _ =
                Quotient.mk'' (q'.out.comap eK.symm) := by
              calc
                (orbitSpaceComapEquiv
                    K K' eG eK hcomm).symm q' =
                    (orbitSpaceComapEquiv
                      K K' eG eK hcomm).symm
                        (Quotient.mk'' q'.out) := by
                  exact congrArg
                    (orbitSpaceComapEquiv
                      K K' eG eK hcomm).symm
                    (Quotient.out_eq' q').symm
                _ = Quotient.mk'' (q'.out.comap eK.symm) :=
                  orbitSpaceComapEquiv_symm_mk
                    K K' eG eK hcomm q'.out)
        (χ.1.1.comap eG.symm)).mpr
    apply liesOverOrbit_of_liesOver K
    exact
      (liesOverAlong_comap_equiv_iff
        eG.symm eK.symm K'.subtype K.subtype hcomm'
        q'.out χ.1.1).mpr
        ((liesOverOrbit_iff_liesOver
          K' q'.out χ.1.1).mp χ.1.2)
  left_inv χ := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv χ := by
    apply Subtype.ext
    apply Subtype.ext
    simp

@[simp]
theorem pPrimeOrbitBlockComapEquiv_apply_character
    (p : ℕ)
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom)
    (q : OrbitSpace K)
    (χ : PPrimeOrbitBlock K p q) :
    (pPrimeOrbitBlockComapEquiv
      K K' p eG eK hcomm q χ).1.1 =
      χ.1.1.comap eG :=
  rfl

/-- Simultaneous pullback transports exactly the active Clifford-orbit
indices. -/
def activeOrbitComapEquiv
    (p : ℕ)
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom) :
    ActiveOrbit K p ≃ ActiveOrbit K' p :=
  (orbitSpaceComapEquiv K K' eG eK hcomm).subtypeEquiv
    (fun q ↦
      (pPrimeOrbitBlockComapEquiv
        K K' p eG eK hcomm q).nonempty_congr)

@[simp]
theorem activeOrbitComapEquiv_apply_coe
    (p : ℕ)
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom)
    (q : ActiveOrbit K p) :
    (activeOrbitComapEquiv K K' p eG eK hcomm q).1 =
      orbitSpaceComapEquiv K K' eG eK hcomm q.1 :=
  rfl

/-- The block transports induced by an ambient equivalence, packaged as an
exact active orbitwise Clifford correspondence. -/
def activePPrimeOrbitwiseComapCorrespondence
    (p : ℕ)
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom) :
    ActivePPrimeOrbitwiseCorrespondence K K' p where
  activeOrbitEquiv :=
    activeOrbitComapEquiv K K' p eG eK hcomm
  blockEquiv := fun q ↦
    pPrimeOrbitBlockComapEquiv
      K K' p eG eK hcomm q.1

/-- The orbitwise transport assembled through the exact active Clifford
partition is ordinary pullback of ambient prime-to-`p` characters. -/
@[simp]
theorem activePPrimeOrbitwiseComapCorrespondence_assemble_apply
    (p : ℕ)
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom)
    (χ : PPrimeIrreducibleCharacter G p) :
    (activePPrimeOrbitwiseComapCorrespondence
      K K' p eG eK hcomm).assemble χ =
      IrreducibleCharacter.pPrimeComapEquiv p eG χ := by
  apply Subtype.ext
  rfl

/-- Equivalence-level form of active Clifford-partition transport. -/
theorem activePPrimeOrbitwiseComapCorrespondence_assemble
    (p : ℕ)
    (eG : G' ≃* G)
    (eK : K' ≃* K)
    (hcomm :
      eG.toMonoidHom.comp K'.subtype =
        K.subtype.comp eK.toMonoidHom) :
    (activePPrimeOrbitwiseComapCorrespondence
      K K' p eG eK hcomm).assemble =
      IrreducibleCharacter.pPrimeComapEquiv p eG := by
  ext χ
  exact
    activePPrimeOrbitwiseComapCorrespondence_assemble_apply
      K K' p eG eK hcomm χ

end CliffordPartition
end McKayConjecture
