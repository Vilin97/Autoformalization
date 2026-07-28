/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.Hom
import McKayConjecture.Character.Automorphism
import McKayConjecture.InductiveMcKay.Normalizer

/-!
# Automorphisms stabilizing a Sylow subgroup

For a Sylow subgroup `P`, this file defines the group customarily denoted
`Aut(G)_P`.  Its elements preserve `N_G(P)`, so they restrict to automorphisms
of the Sylow normalizer.  More generally, the same construction restricts any
group of automorphisms to any invariant subgroup.

The resulting homomorphisms to subgroup automorphism groups induce actions on
ordinary irreducible characters of `p'`-degree.  The final definitions package
the equivariance condition needed in an inductive McKay statement.
-/

noncomputable section

open scoped Pointwise

universe u

namespace McKayConjecture.InductiveMcKay

variable {G : Type u} [Group G] {p : ℕ}

/-- The stabilizer `Aut(G)_P` of a Sylow subgroup under automorphisms of `G`. -/
abbrev SylowAutStabilizer (P : Sylow p G) : Subgroup (MulAut G) :=
  MulAction.stabilizer (MulAut G) P

namespace SylowAutStabilizer

variable {P : Sylow p G}

@[simp]
theorem mem_iff (a : MulAut G) :
    a ∈ SylowAutStabilizer P ↔ a • P = P :=
  MulAction.mem_stabilizer_iff

/-- An automorphism in `Aut(G)_P` maps the underlying subgroup `P` to itself. -/
theorem map_sylow_eq (a : SylowAutStabilizer P) :
    (P : Subgroup G).map (a.1 : G →* G) = P := by
  have h := congrArg (fun Q : Sylow p G ↦ (Q : Subgroup G)) a.2
  exact h

/-- An automorphism in `Aut(G)_P` maps `N_G(P)` to itself. -/
theorem map_normalizer_eq (a : SylowAutStabilizer P) :
    (Subgroup.normalizer (P : Subgroup G)).map (a.1 : G →* G) =
      Subgroup.normalizer (P : Subgroup G) := by
  calc
    (Subgroup.normalizer (P : Subgroup G)).map (a.1 : G →* G) =
        Subgroup.normalizer ((P : Subgroup G).map (a.1 : G →* G)) :=
      Subgroup.map_equiv_normalizer_eq (P : Subgroup G) a.1
    _ = Subgroup.normalizer (P : Subgroup G) := by
      rw [map_sylow_eq a]

end SylowAutStabilizer

/-- A subgroup `A ≤ Aut(G)` leaves a subgroup `H ≤ G` invariant. -/
def AutomorphismInvariant (A : Subgroup (MulAut G)) (H : Subgroup G) : Prop :=
  ∀ a : A, H.map (a.1 : G →* G) = H

namespace AutomorphismInvariant

variable {A : Subgroup (MulAut G)} {H : Subgroup G}

/-- Restrict one automorphism in `A` to an `A`-invariant subgroup `H`. -/
def restrict (hH : AutomorphismInvariant A H) (a : A) : MulAut H where
  toFun x :=
    ⟨a.1 x.1, by
      have hx :
          a.1 x.1 ∈ H.map (a.1 : G →* G) :=
        Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩
      exact (congrArg (fun K : Subgroup G ↦ a.1 x.1 ∈ K) (hH a)).mp hx⟩
  invFun x :=
    ⟨a.1.symm x.1, by
      change (a⁻¹).1 x.1 ∈ H
      have hx :
          (a⁻¹).1 x.1 ∈ H.map ((a⁻¹).1 : G →* G) :=
        Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩
      exact
        (congrArg (fun K : Subgroup G ↦ (a⁻¹).1 x.1 ∈ K) (hH a⁻¹)).mp hx⟩
  left_inv x := by
    apply Subtype.ext
    exact a.1.symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact a.1.apply_symm_apply x.1
  map_mul' x y := by
    apply Subtype.ext
    exact a.1.map_mul x.1 y.1

@[simp]
theorem coe_restrict_apply (hH : AutomorphismInvariant A H) (a : A) (x : H) :
    ((restrict hH a x : H) : G) = a.1 x.1 :=
  rfl

@[simp]
theorem coe_restrict_symm_apply (hH : AutomorphismInvariant A H) (a : A) (x : H) :
    (((restrict hH a).symm x : H) : G) = a.1.symm x.1 :=
  rfl

/-- Restriction to an invariant subgroup is a homomorphism of automorphism
groups. -/
def restrictionHom (hH : AutomorphismInvariant A H) : A →* MulAut H where
  toFun := restrict hH
  map_one' := by
    ext x
    rfl
  map_mul' a b := by
    ext x
    rfl

@[simp]
theorem restrictionHom_apply_coe (hH : AutomorphismInvariant A H)
    (a : A) (x : H) :
    (((restrictionHom hH a) x : H) : G) = a.1 x.1 :=
  rfl

/-- The action induced on irreducible characters of `q'`-degree by restriction
to an invariant subgroup.  This definition can be installed locally with
`letI`. -/
@[instance_reducible]
def pPrimeCharacterMulAction (hH : AutomorphismInvariant A H) (q : ℕ) :
    MulAction A (PPrimeIrreducibleCharacter H q) :=
  MulAction.compHom _ (restrictionHom hH)

end AutomorphismInvariant

namespace SylowAutStabilizer

variable (P : Sylow p G)

/-- The Sylow normalizer is invariant under `Aut(G)_P`. -/
theorem normalizer_invariant :
    AutomorphismInvariant (SylowAutStabilizer P)
      (Subgroup.normalizer (P : Subgroup G)) :=
  map_normalizer_eq

/-- Restriction from `Aut(G)_P` to `Aut(N_G(P))`. -/
def normalizerRestrictionHom :
    SylowAutStabilizer P →* MulAut (SylowNormalizer P) :=
  AutomorphismInvariant.restrictionHom (normalizer_invariant P)

@[simp]
theorem normalizerRestrictionHom_apply_coe
    (a : SylowAutStabilizer P) (x : SylowNormalizer P) :
    (((normalizerRestrictionHom P a) x : SylowNormalizer P) : G) = a.1 x.1 :=
  rfl

@[simp]
theorem normalizerRestrictionHom_symm_apply_coe
    (a : SylowAutStabilizer P) (x : SylowNormalizer P) :
    ((((normalizerRestrictionHom P a).symm x : SylowNormalizer P) : G)) =
      a.1.symm x.1 :=
  rfl

/-- The induced action of `Aut(G)_P` on the `q'`-degree irreducible characters
of `N_G(P)`. -/
instance instMulActionNormalizerPPrime (q : ℕ) :
    MulAction (SylowAutStabilizer P)
      (PPrimeIrreducibleCharacter (SylowNormalizer P) q) :=
  MulAction.compHom _ (normalizerRestrictionHom P)

@[simp]
theorem smul_normalizer_pPrime_values (q : ℕ)
    (a : SylowAutStabilizer P)
    (χ : PPrimeIrreducibleCharacter (SylowNormalizer P) q)
    (x : SylowNormalizer P) :
    (a • χ).1.values x =
      χ.1.values ((normalizerRestrictionHom P a).symm x) :=
  rfl

/-- Restriction from `Aut(G)_P` to the automorphism group of any invariant
intermediate subgroup. -/
def intermediateRestrictionHom (N : Subgroup G)
    (hN : AutomorphismInvariant (SylowAutStabilizer P) N) :
    SylowAutStabilizer P →* MulAut N :=
  AutomorphismInvariant.restrictionHom hN

/-- The induced action on `q'`-degree irreducible characters of an invariant
intermediate subgroup.  This definition can be installed locally with
`letI`. -/
@[instance_reducible]
def intermediatePPrimeCharacterMulAction (N : Subgroup G)
    (hN : AutomorphismInvariant (SylowAutStabilizer P) N) (q : ℕ) :
    MulAction (SylowAutStabilizer P)
      (PPrimeIrreducibleCharacter N q) :=
  MulAction.compHom _ (intermediateRestrictionHom P N hN)

end SylowAutStabilizer

/-- Equivariance of a proposed McKay correspondence under `Aut(G)_P`.

The source uses the action inherited from `MulAut G`; the target uses the
restriction action through `Aut(N_G(P))` defined above.
-/
def IsEquivariantMcKayEquiv (P : Sylow p G)
    (e : PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter (SylowNormalizer P) p) : Prop :=
  ∀ (a : SylowAutStabilizer P) (χ : PPrimeIrreducibleCharacter G p),
    e (a • χ) = a • e χ

/-- An equivalence of `p'`-degree character sets together with its
`Aut(G)_P`-equivariance certificate. -/
structure EquivariantMcKayEquiv (P : Sylow p G) where
  /-- The underlying character bijection. -/
  toEquiv :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter (SylowNormalizer P) p
  /-- Compatibility with the stabilizer action. -/
  map_smul' : IsEquivariantMcKayEquiv P toEquiv

namespace EquivariantMcKayEquiv

variable {P : Sylow p G}

instance : CoeFun (EquivariantMcKayEquiv P)
    (fun _ ↦ PPrimeIrreducibleCharacter G p →
      PPrimeIrreducibleCharacter (SylowNormalizer P) p) :=
  ⟨fun e ↦ e.toEquiv⟩

@[simp]
theorem map_smul (e : EquivariantMcKayEquiv P)
    (a : SylowAutStabilizer P) (χ : PPrimeIrreducibleCharacter G p) :
    e (a • χ) = a • e χ :=
  e.map_smul' a χ

end EquivariantMcKayEquiv

end McKayConjecture.InductiveMcKay
