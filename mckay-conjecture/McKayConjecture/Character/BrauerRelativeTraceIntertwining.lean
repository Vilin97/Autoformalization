/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerRelativeTraceEquivariance

/-!
# Intertwining maps and relative traces

The equivariance theorem for relative traces also has a useful
two-representation form.  A linear map `f : V → W` intertwining `ρ`
with `σ` along a group automorphism carries the relative trace for
`ρ` from `Q` to the relative trace for `σ` from the image of `Q`.

Unlike `CompatibleAutomorphism`, the linear map need not be
invertible.  This form is used for multiplication maps between
different twisted components of an interior algebra.
-/

noncomputable section

open scoped BigOperators

namespace Representation

variable {k P V W : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

noncomputable local instance intertwiningLeftCosetFintype
    (Q : Subgroup P) :
    Fintype (P ⧸ Q) :=
  Fintype.ofFinite (P ⧸ Q)

/-- Transport a subgroup-invariant vector through an intertwining
linear map and a group automorphism. -/
def transportInvariantAlong
    (ρ : Representation k P V)
    (σ : Representation k P W)
    (e : P ≃* P)
    (f : V →ₗ[k] W)
    (hcompat :
      ∀ (g : P) (v : V),
        f (ρ g v) = σ (e g) (f v))
    (Q : Subgroup P)
    (x : invariants (ρ.comp Q.subtype)) :
    invariants
      (σ.comp (Q.map e.toMonoidHom).subtype) where
  val := f x
  property q := by
    obtain ⟨g, hg, hgeq⟩ := q.property
    calc
      σ (q : P) (f (x : V)) =
          σ (e g) (f (x : V)) := by
        rw [← hgeq]
        simp only [MulEquiv.coe_toMonoidHom]
      _ = f (ρ g (x : V)) :=
        (hcompat g x).symm
      _ = f (x : V) := by
        have hx := x.property ⟨g, hg⟩
        change ρ g (x : V) = (x : V) at hx
        rw [hx]

omit [Fintype P] in
@[simp]
theorem transportInvariantAlong_coe
    (ρ : Representation k P V)
    (σ : Representation k P W)
    (e : P ≃* P)
    (f : V →ₗ[k] W)
    (hcompat :
      ∀ (g : P) (v : V),
        f (ρ g v) = σ (e g) (f v))
    (Q : Subgroup P)
    (x : invariants (ρ.comp Q.subtype)) :
    (transportInvariantAlong ρ σ e f hcompat Q x : W) =
      f (x : V) :=
  rfl

omit [Fintype P] in
/-- Termwise compatibility after transporting a coset and an
invariant vector. -/
theorem transportInvariantAlong_cosetTerm
    (ρ : Representation k P V)
    (σ : Representation k P W)
    (e : P ≃* P)
    (f : V →ₗ[k] W)
    (hcompat :
      ∀ (g : P) (v : V),
        f (ρ g v) = σ (e g) (f v))
    (Q : Subgroup P)
    (x : invariants (ρ.comp Q.subtype))
    (c : P ⧸ Q) :
    f (ρ c.out (x : V)) =
      σ (leftCosetMapEquiv e Q c).out
        (transportInvariantAlong
          ρ σ e f hcompat Q x : W) := by
  let d : P ⧸ Q.map e.toMonoidHom :=
    leftCosetMapEquiv e Q c
  have hquotient :
      QuotientGroup.mk (s := Q.map e.toMonoidHom) d.out =
        QuotientGroup.mk (s := Q.map e.toMonoidHom)
          (e c.out) := by
    calc
      QuotientGroup.mk
          (s := Q.map e.toMonoidHom) d.out =
          d :=
        QuotientGroup.out_eq' d
      _ = leftCosetMapEquiv e Q c := rfl
      _ = leftCosetMapEquiv e Q
          (QuotientGroup.mk (s := Q) c.out) := by
        rw [QuotientGroup.out_eq' c]
      _ = QuotientGroup.mk
          (s := Q.map e.toMonoidHom) (e c.out) :=
        leftCosetMapEquiv_mk e Q c.out
  have hmem :
      d.out⁻¹ * e c.out ∈ Q.map e.toMonoidHom :=
    QuotientGroup.leftRel_apply.mp
      (Quotient.exact' hquotient)
  let q : Q.map e.toMonoidHom :=
    ⟨d.out⁻¹ * e c.out, hmem⟩
  have hfactor :
      e c.out = d.out * (q : P) := by
    dsimp [q]
    simp
  calc
    f (ρ c.out (x : V)) =
        σ (e c.out) (f (x : V)) :=
      hcompat c.out x
    _ = σ (d.out * (q : P)) (f (x : V)) := by
      rw [hfactor]
    _ = σ d.out (σ (q : P) (f (x : V))) := by
      rw [map_mul]
      rfl
    _ = σ d.out (f (x : V)) := by
      have hq :=
        (transportInvariantAlong
          ρ σ e f hcompat Q x).property q
      change σ (q : P) (f (x : V)) = f (x : V) at hq
      rw [hq]
    _ = σ (leftCosetMapEquiv e Q c).out
        (transportInvariantAlong
          ρ σ e f hcompat Q x : W) :=
      rfl

/-- Relative trace values commute with an intertwining linear map,
with the subgroup transported by the group automorphism. -/
theorem relativeTraceValue_intertwining
    (ρ : Representation k P V)
    (σ : Representation k P W)
    (e : P ≃* P)
    (f : V →ₗ[k] W)
    (hcompat :
      ∀ (g : P) (v : V),
        f (ρ g v) = σ (e g) (f v))
    (Q : Subgroup P)
    (x : invariants (ρ.comp Q.subtype)) :
    f (relativeTraceValue ρ Q x) =
      relativeTraceValue σ (Q.map e.toMonoidHom)
        (transportInvariantAlong
          ρ σ e f hcompat Q x) := by
  rw [relativeTraceValue, relativeTraceValue, map_sum]
  exact
    Fintype.sum_equiv
      (leftCosetMapEquiv e Q)
      (fun c : P ⧸ Q ↦ f (ρ c.out (x : V)))
      (fun d : P ⧸ Q.map e.toMonoidHom ↦
        σ d.out
          (transportInvariantAlong
            ρ σ e f hcompat Q x : W))
      (transportInvariantAlong_cosetTerm
        ρ σ e f hcompat Q x)

end Representation
