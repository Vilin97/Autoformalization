/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.FrattiniArgument
import McKayConjecture.GroupTheory.NormalizerProductProper

/-!
# Proper intermediate subgroups from a local normalizer

Let `N ⫳ G`, let `Q` be a Sylow subgroup of `N`, and let
`M < N` contain `N_N(Q)`.  If the ambient normalizer `N_G(Q)`
normalizes `M`, then `M N_G(Q)` is a proper subgroup of `G`.
This is the subgroup decrease used in the final Rossi argument.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G]

/-- Mapping a proper subgroup of `N` through the subtype inclusion gives
a proper subgroup of the ambient copy of `N`. -/
theorem map_subtype_lt_ambient_of_lt_top
    (N : Subgroup G)
    (M : Subgroup N)
    (hM : M < ⊤) :
    M.map N.subtype < N := by
  apply lt_of_le_of_ne
  · exact
      (Subgroup.map_le_range
        N.subtype M).trans_eq
        N.range_subtype
  · intro heq
    apply hM.ne
    have hcomap :=
      congrArg (Subgroup.comap N.subtype) heq
    rw [Subgroup.comap_map_eq_self_of_injective
        N.subtype_injective,
      Subgroup.comap_subtype,
      Subgroup.subgroupOf_self] at hcomap
    exact hcomap

namespace Sylow

variable {p : ℕ}
variable (N : Subgroup G) [N.Normal]

omit [N.Normal] in
/-- The intersection of `N` with the ambient normalizer of a Sylow
subgroup `Q ≤ N` is contained in the ambient image of any subgroup
containing `N_N(Q)`. -/
theorem inf_ambientNormalizer_le_map_of_internalNormalizer_le
    (Q : Sylow p N)
    (M : Subgroup N)
    (hQM :
      Subgroup.normalizer (Q : Set N) ≤ M) :
    N ⊓
        Subgroup.normalizer
          (ambientSubgroup Q : Set G) ≤
      M.map N.subtype := by
  rw [inf_comm,
    ← map_normalizer_eq_inf_ambientNormalizer Q]
  exact Subgroup.map_mono hQM

omit [N.Normal] in
/-- A proper local subgroup containing the internal normalizer yields a
proper ambient intermediate subgroup after adjoining the ambient
normalizer. -/
theorem map_sup_ambientNormalizer_lt_top
    (Q : Sylow p N)
    (M : Subgroup N)
    (hM : M < ⊤)
    (hQM :
      Subgroup.normalizer (Q : Set N) ≤ M)
    (hinvariant :
      Subgroup.normalizer
          (ambientSubgroup Q : Set G) ≤
        Subgroup.normalizer
          (M.map N.subtype)) :
    M.map N.subtype ⊔
        Subgroup.normalizer
          (ambientSubgroup Q : Set G) <
      ⊤ := by
  exact
    sup_lt_top_of_lt_of_le_normalizer_of_inf_le
      N (M.map N.subtype)
        (Subgroup.normalizer
          (ambientSubgroup Q : Set G))
      (map_subtype_lt_ambient_of_lt_top N M hM)
      hinvariant
      (inf_ambientNormalizer_le_map_of_internalNormalizer_le
        N Q M hQM)

omit [N.Normal] in
/-- Central-index form of `map_sup_ambientNormalizer_lt_top`. -/
theorem centralIndex_map_sup_ambientNormalizer_lt
    [Finite G]
    (Q : Sylow p N)
    (M : Subgroup N)
    (hM : M < ⊤)
    (hQM :
      Subgroup.normalizer (Q : Set N) ≤ M)
    (hinvariant :
      Subgroup.normalizer
          (ambientSubgroup Q : Set G) ≤
        Subgroup.normalizer
          (M.map N.subtype))
    (hZ :
      Subgroup.center G ≤
        M.map N.subtype ⊔
          Subgroup.normalizer
            (ambientSubgroup Q : Set G)) :
    centralIndex
        ↥(M.map N.subtype ⊔
          Subgroup.normalizer
            (ambientSubgroup Q : Set G)) <
      centralIndex G :=
  centralIndex_lt_of_center_le_of_lt_top
    (M.map N.subtype ⊔
      Subgroup.normalizer
        (ambientSubgroup Q : Set G))
    hZ
    (map_sup_ambientNormalizer_lt_top
      N Q M hM hQM hinvariant)

end Sylow
end GroupTheory
end McKayConjecture
