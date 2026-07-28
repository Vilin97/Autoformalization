/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerTraceIdeal

/-!
# Equivariance of relative traces

A group automorphism carries the left cosets of `Q` bijectively to the
left cosets of the image subgroup.  If a linear automorphism intertwines
the corresponding group actions, it therefore carries the relative
trace from `Q` to the relative trace from the image of `Q`.

The final theorem specializes this observation to an automorphism of an
algebra with a compatible group action.  It is the termwise input needed
to prove that such an automorphism preserves the Brauer trace ideal.
-/

noncomputable section

open scoped BigOperators

namespace Representation

variable {k P V : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]

noncomputable local instance equivarianceLeftCosetFintype
    (Q : Subgroup P) :
    Fintype (P ⧸ Q) :=
  Fintype.ofFinite (P ⧸ Q)

/-- A group equivalence carries the left cosets of a subgroup to the
left cosets of its image subgroup. -/
def leftCosetMapEquiv
    (e : P ≃* P)
    (Q : Subgroup P) :
    P ⧸ Q ≃ P ⧸ Q.map e.toMonoidHom where
  toFun :=
    Quotient.map' e fun a b hab ↦ by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      simpa only [map_inv, map_mul, MulEquiv.coe_toMonoidHom] using
        Subgroup.mem_map_of_mem e.toMonoidHom hab
  invFun :=
    Quotient.map' e.symm fun a b hab ↦ by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      simpa only [map_inv, map_mul, MulEquiv.coe_toMonoidHom] using
        (Subgroup.mem_map_equiv.mp hab)
  left_inv c := by
    induction c using QuotientGroup.induction_on with
    | _ g =>
      change
        QuotientGroup.mk (s := Q)
            (e.symm (e g)) =
          QuotientGroup.mk (s := Q) g
      rw [e.symm_apply_apply]
  right_inv c := by
    induction c using QuotientGroup.induction_on with
    | _ g =>
      change
        QuotientGroup.mk (s := Q.map e.toMonoidHom)
            (e (e.symm g)) =
          QuotientGroup.mk (s := Q.map e.toMonoidHom) g
      rw [e.apply_symm_apply]

omit [Fintype P] in
@[simp]
theorem leftCosetMapEquiv_mk
    (e : P ≃* P)
    (Q : Subgroup P)
    (g : P) :
    leftCosetMapEquiv e Q (QuotientGroup.mk g) =
      QuotientGroup.mk (e g) :=
  rfl

/-- Transport a subgroup-invariant vector along compatible
automorphisms of the group and the representation space. -/
def transportInvariant
    (rho : Representation k P V)
    (eP : P ≃* P)
    (eV : V ≃ₗ[k] V)
    (hcompat :
      ∀ (g : P) (v : V),
        eV (rho g v) = rho (eP g) (eV v))
    (Q : Subgroup P)
    (x : invariants (rho.comp Q.subtype)) :
    invariants (rho.comp (Q.map eP.toMonoidHom).subtype) where
  val := eV x
  property q := by
    obtain ⟨g, hg, hgeq⟩ := q.property
    calc
      rho (q : P) (eV (x : V)) =
          rho (eP g) (eV (x : V)) := by
            rw [← hgeq]
            simp only [MulEquiv.coe_toMonoidHom]
      _ = eV (rho g (x : V)) := (hcompat g x).symm
      _ = eV (x : V) := by
        have hx := x.property ⟨g, hg⟩
        change rho g (x : V) = (x : V) at hx
        rw [hx]

omit [Fintype P] in
@[simp]
theorem transportInvariant_coe
    (rho : Representation k P V)
    (eP : P ≃* P)
    (eV : V ≃ₗ[k] V)
    (hcompat :
      ∀ (g : P) (v : V),
        eV (rho g v) = rho (eP g) (eV v))
    (Q : Subgroup P)
    (x : invariants (rho.comp Q.subtype)) :
    (transportInvariant rho eP eV hcompat Q x : V) =
      eV (x : V) :=
  rfl

omit [Fintype P] in
/-- The summands used for relative traces agree after transporting the
coset and the invariant vector. -/
theorem transportInvariant_cosetTerm
    (rho : Representation k P V)
    (eP : P ≃* P)
    (eV : V ≃ₗ[k] V)
    (hcompat :
      ∀ (g : P) (v : V),
        eV (rho g v) = rho (eP g) (eV v))
    (Q : Subgroup P)
    (x : invariants (rho.comp Q.subtype))
    (c : P ⧸ Q) :
    eV (rho c.out (x : V)) =
      rho (leftCosetMapEquiv eP Q c).out
        (transportInvariant rho eP eV hcompat Q x : V) := by
  let d : P ⧸ Q.map eP.toMonoidHom :=
    leftCosetMapEquiv eP Q c
  have hquotient :
      QuotientGroup.mk (s := Q.map eP.toMonoidHom) (d.out : P) =
        QuotientGroup.mk (s := Q.map eP.toMonoidHom)
          (eP c.out : P) := by
    calc
      QuotientGroup.mk (s := Q.map eP.toMonoidHom) (d.out : P) = d :=
        QuotientGroup.out_eq' d
      _ = leftCosetMapEquiv eP Q c := rfl
      _ = leftCosetMapEquiv eP Q
          (QuotientGroup.mk (s := Q) c.out) := by
            rw [QuotientGroup.out_eq' c]
      _ = QuotientGroup.mk (s := Q.map eP.toMonoidHom)
          (eP c.out : P) :=
        leftCosetMapEquiv_mk eP Q c.out
  have hmem :
      d.out⁻¹ * eP c.out ∈ Q.map eP.toMonoidHom :=
    QuotientGroup.leftRel_apply.mp
      (Quotient.exact' hquotient)
  let q : Q.map eP.toMonoidHom :=
    ⟨d.out⁻¹ * eP c.out, hmem⟩
  have hfactor :
      eP c.out = d.out * (q : P) := by
    dsimp [q]
    simp
  calc
    eV (rho c.out (x : V)) =
        rho (eP c.out) (eV (x : V)) :=
      hcompat c.out x
    _ = rho (d.out * (q : P)) (eV (x : V)) := by
      rw [hfactor]
    _ = rho d.out (rho (q : P) (eV (x : V))) := by
      rw [map_mul]
      rfl
    _ = rho d.out (eV (x : V)) := by
      have hqfixed :=
        (transportInvariant rho eP eV hcompat Q x).property q
      change
        rho (q : P) (eV (x : V)) = eV (x : V) at hqfixed
      rw [hqfixed]
    _ = rho (leftCosetMapEquiv eP Q c).out
        (transportInvariant rho eP eV hcompat Q x : V) :=
      rfl

/-- Relative trace values are equivariant under compatible
automorphisms of the acting group and the representation space. -/
theorem relativeTraceValue_equivariant
    (rho : Representation k P V)
    (eP : P ≃* P)
    (eV : V ≃ₗ[k] V)
    (hcompat :
      ∀ (g : P) (v : V),
        eV (rho g v) = rho (eP g) (eV v))
    (Q : Subgroup P)
    (x : invariants (rho.comp Q.subtype)) :
    eV (relativeTraceValue rho Q x) =
      relativeTraceValue rho (Q.map eP.toMonoidHom)
        (transportInvariant rho eP eV hcompat Q x) := by
  rw [relativeTraceValue, relativeTraceValue, map_sum]
  exact
    Fintype.sum_equiv
      (leftCosetMapEquiv eP Q)
      (fun c : P ⧸ Q ↦ eV (rho c.out (x : V)))
      (fun d : P ⧸ Q.map eP.toMonoidHom ↦
        rho d.out
          (transportInvariant rho eP eV hcompat Q x : V))
      (transportInvariant_cosetTerm rho eP eV hcompat Q x)

section Algebra

variable {A : Type}
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- Transport a fixed algebra element to the fixed algebra for the
image subgroup. -/
def transportFixedSubalgebra
    (eP : P ≃* P)
    (eA : A ≃ₐ[k] A)
    (hcompat :
      ∀ (g : P) (a : A),
        eA (g • a) = eP g • eA a)
    (Q : Subgroup P)
    (x : fixedSubalgebra (k := k) (P := Q) (A := A)) :
    fixedSubalgebra
      (k := k) (P := Q.map eP.toMonoidHom) (A := A) where
  val := eA x
  property q := by
    obtain ⟨g, hg, hgeq⟩ := q.property
    calc
      (q : P) • eA (x : A) =
          eP g • eA (x : A) := by
            rw [← hgeq]
            simp only [MulEquiv.coe_toMonoidHom]
      _ = eA (g • (x : A)) := (hcompat g x).symm
      _ = eA (x : A) := by
        have hx := x.property ⟨g, hg⟩
        change g • (x : A) = (x : A) at hx
        rw [hx]

omit [Fintype P] in
@[simp]
theorem transportFixedSubalgebra_coe
    (eP : P ≃* P)
    (eA : A ≃ₐ[k] A)
    (hcompat :
      ∀ (g : P) (a : A),
        eA (g • a) = eP g • eA a)
    (Q : Subgroup P)
    (x : fixedSubalgebra (k := k) (P := Q) (A := A)) :
    (transportFixedSubalgebra eP eA hcompat Q x : A) =
      eA (x : A) :=
  rfl

/-- A compatible algebra automorphism carries the fixed-algebra
relative trace from `Q` to the trace from the image of `Q`. -/
theorem fixedRelativeTrace_equivariant
    (eP : P ≃* P)
    (eA : A ≃ₐ[k] A)
    (hcompat :
      ∀ (g : P) (a : A),
        eA (g • a) = eP g • eA a)
    (Q : Subgroup P)
    (x : fixedSubalgebra (k := k) (P := Q) (A := A)) :
    eA
        ((fixedRelativeTrace (k := k) (P := P) (A := A) Q x :
          fixedSubalgebra (k := k) (P := P) (A := A)) : A) =
      ((fixedRelativeTrace
          (k := k) (P := P) (A := A)
          (Q.map eP.toMonoidHom)
          (transportFixedSubalgebra eP eA hcompat Q x) :
        fixedSubalgebra (k := k) (P := P) (A := A)) : A) := by
  exact
    relativeTraceValue_equivariant
      (algebraActionRepresentation (k := k) (P := P) (A := A))
      eP eA.toLinearEquiv hcompat Q ⟨x, x.property⟩

end Algebra

end Representation
