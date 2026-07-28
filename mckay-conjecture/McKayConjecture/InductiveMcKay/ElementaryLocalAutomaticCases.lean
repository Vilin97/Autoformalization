/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.PerfectGroupLocalConstraints
import McKayConjecture.InductiveMcKay.TrivialLocal

/-!
# Elementary automatic cases for full local inductive-McKay data

The complete local datum is canonical whenever the Sylow normalizer is the
whole group.  This file records several elementary hypotheses which force
that situation:

* the ambient group is a `p`-group;
* the ambient group is finite nilpotent;
* the group order divides a power of `p`; or
* the full automorphism group is subsingleton (which forces the ambient
  group to be commutative, because every inner automorphism is trivial).

These are genuine constructions of `LocalInductiveMcKayData`; no numerical
or character-triple input is hidden in their hypotheses.
-/

noncomputable section

open scoped IsMulCommutative

universe u

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

namespace EquivariantLocalCorrespondence

variable {G : Type u} [Group G] {p : ℕ}

/-- If the Sylow-stabilizing automorphism group is subsingleton, every
numerical local correspondence is automatically invariant and equivariant.

This deliberately produces only `EquivariantLocalCorrespondence`: a
trivial automorphism action does not by itself supply the projective
character-triple witnesses required by `LocalInductiveMcKayData`. -/
def of_subsingleton_sylowAutStabilizer
    (P : Sylow p G)
    [Subsingleton (SylowAutStabilizer P)]
    (d : LocalCorrespondence P) :
    EquivariantLocalCorrespondence P where
  toLocalCorrespondence := d
  intermediate_invariant := by
    intro a
    rw [Subsingleton.elim a 1]
    change
      Subgroup.map
          ((1 : SylowAutStabilizer P).1.toMonoidHom)
          d.intermediate =
        d.intermediate
    have hone :
        (1 : SylowAutStabilizer P).1.toMonoidHom =
          MonoidHom.id G := by
      ext
      rfl
    rw [hone, Subgroup.map_id]
  map_smul' := by
    intro a χ
    rw [Subsingleton.elim a 1]
    simp

end EquivariantLocalCorrespondence

namespace LocalInductiveMcKayData

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ}

/-- If the whole ambient group is a `p`-group, every Sylow `p`-subgroup is
the whole group and hence has the canonical full local datum. -/
theorem nonempty_of_isPGroup
    (P : Sylow p G)
    (hG : IsPGroup p G) :
    Nonempty (LocalInductiveMcKayData P) := by
  have hPtop :
      (P : Subgroup G) = ⊤ :=
    (P.is_maximal'
      (hG.to_subgroup (⊤ : Subgroup G)) le_top).symm
  have hPnormal : (P : Subgroup G).Normal := by
    rw [hPtop]
    infer_instance
  letI : (P : Subgroup G).Normal := hPnormal
  exact ⟨LocalInductiveMcKayData.of_normal_sylow P⟩

/-- A Sylow subgroup of a finite nilpotent group is normal, so the
canonical full local datum applies. -/
theorem nonempty_of_isNilpotent
    [Fact p.Prime]
    (P : Sylow p G)
    (hG : Group.IsNilpotent G) :
    Nonempty (LocalInductiveMcKayData P) := by
  letI : Group.IsNilpotent G := hG
  exact ⟨LocalInductiveMcKayData.of_normal_sylow P⟩

/-- If the finite group order divides a power of `p`, the group is a
`p`-group and its full local datum is canonical. -/
theorem nonempty_of_card_dvd_prime_power
    (P : Sylow p G)
    (n : ℕ)
    (hcard : Nat.card G ∣ p ^ n) :
    Nonempty (LocalInductiveMcKayData P) :=
  nonempty_of_isPGroup P
    (IsPGroup.of_card_dvd_pow hcard)

/-- In particular, a group of prime-power order has canonical full local
data at that prime. -/
theorem nonempty_of_card_eq_prime_power
    (P : Sylow p G)
    (n : ℕ)
    (hcard : Nat.card G = p ^ n) :
    Nonempty (LocalInductiveMcKayData P) :=
  nonempty_of_card_dvd_prime_power P n
    (hcard.symm ▸ dvd_refl (p ^ n))

/-- A finite group whose order divides a prime is cyclic, hence has
canonical full local data at every prime (not only at the prime appearing
in its order). -/
theorem nonempty_of_card_dvd_prime
    {q : ℕ} [Fact q.Prime]
    (P : Sylow p G)
    (hcard : Nat.card G ∣ q) :
    Nonempty (LocalInductiveMcKayData P) :=
  ⟨LocalInductiveMcKayData.of_isMulCommutative
    (isCyclic_of_card_dvd_prime hcard).isMulCommutative P⟩

/-- Every group of order the square of a prime is commutative, so it has
canonical full local data at every prime. -/
theorem nonempty_of_card_eq_prime_sq
    {q : ℕ} [Fact q.Prime]
    (P : Sylow p G)
    (hcard : Nat.card G = q ^ 2) :
    Nonempty (LocalInductiveMcKayData P) :=
  ⟨LocalInductiveMcKayData.of_isMulCommutative
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq
      hcard) P⟩

/-- If the full automorphism group is subsingleton, inner automorphisms are
trivial, hence the ambient group is commutative and every Sylow subgroup
has canonical full local data. -/
theorem nonempty_of_subsingleton_mulAut
    (P : Sylow p G)
    (hAut : Subsingleton (MulAut G)) :
    Nonempty (LocalInductiveMcKayData P) := by
  letI : Subsingleton (MulAut G) := hAut
  exact
    ⟨LocalInductiveMcKayData.of_isMulCommutative
      (isMulCommutative_of_subsingleton_mulAut (G := G)) P⟩

end LocalInductiveMcKayData

end InductiveMcKay
end McKayConjecture
