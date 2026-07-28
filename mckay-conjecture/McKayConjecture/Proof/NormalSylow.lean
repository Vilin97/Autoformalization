/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Proof.Correspondence

/-!
# The McKay correspondence for a normal Sylow subgroup

When a Sylow subgroup is normal, its normalizer is the whole group.  Transport
along the canonical isomorphism gives the McKay correspondence immediately.
-/

noncomputable section

universe u

namespace McKayConjecture

variable {G : Type u} [Group G] {p : ℕ} (P : Sylow p G)

/-- The canonical group isomorphism from a full Sylow normalizer to the
ambient group. -/
def normalizerEquivOfEqTop
    (hP : Subgroup.normalizer (P : Set G) = ⊤) :
    SylowNormalizer P ≃* G :=
  (MulEquiv.subgroupCongr hP).trans Subgroup.topEquiv

/-- If the Sylow normalizer is the whole group, the McKay correspondence is
transport along the canonical isomorphism. -/
def mcKayCorrespondenceOfNormalizerEqTop
    (hP : Subgroup.normalizer (P : Set G) = ⊤) :
    McKayCorrespondence G p P :=
  IrreducibleCharacter.pPrimeComapEquiv p
    (normalizerEquivOfEqTop P hP)

/-- A normal Sylow subgroup has the canonical McKay correspondence. -/
def mcKayCorrespondenceOfNormalSylow
    [hP : (P : Subgroup G).Normal] :
    McKayCorrespondence G p P :=
  mcKayCorrespondenceOfNormalizerEqTop P
    (Subgroup.normalizer_eq_top (H := (P : Subgroup G)))

/-- The McKay statement in the base case of normalizer induction. -/
theorem Statement.of_normalizer_eq_top [Finite G] [Fact p.Prime]
    (hP : Subgroup.normalizer (P : Set G) = ⊤) :
    Statement G p P :=
  Statement.of_correspondence
    (mcKayCorrespondenceOfNormalizerEqTop P hP)

/-- A normal Sylow subgroup satisfies the McKay statement. -/
theorem Statement.of_normal_sylow [Finite G] [Fact p.Prime]
    [hP : (P : Subgroup G).Normal] :
    Statement G p P :=
  Statement.of_correspondence
    (mcKayCorrespondenceOfNormalSylow P)

/-- In particular, the McKay statement holds for finite commutative groups. -/
theorem Statement.of_commGroup {G : Type u} [CommGroup G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    Statement G p P :=
  Statement.of_normal_sylow P

end McKayConjecture
