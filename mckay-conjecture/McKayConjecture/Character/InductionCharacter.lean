/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import McKayConjecture.Character.Induction

/-!
# The character of an induced representation

This file connects mathlib's coinvariant construction of an induced
representation with the classical induced-character formula.
-/

noncomputable section

open scoped MonoidAlgebra

open Finsupp

universe u

namespace McKayConjecture

section LinearAlgebra

variable {k α : Type*} [Field k] [Fintype α] [DecidableEq α]

/-- The trace of a linear map that permutes a finite basis is the number of
fixed basis vectors. -/
theorem trace_of_map_basis {M : Type*} [AddCommGroup M] [Module k M]
    (b : Module.Basis α k M) (f : M →ₗ[k] M) (σ : α → α)
    (hf : ∀ x, f (b x) = b (σ x)) :
    LinearMap.trace k M f =
      ∑ x : α, if σ x = x then 1 else 0 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hf,
    Module.Basis.repr_self_apply]

/-- The trace of a linear map that permutes the standard basis is the number
of fixed basis vectors. -/
theorem trace_finsupp_of_map_single (f : (α →₀ k) →ₗ[k] (α →₀ k))
    (σ : α → α) (hf : ∀ x, f (.single x 1) = .single (σ x) 1) :
    LinearMap.trace k (α →₀ k) f =
      ∑ x : α, if σ x = x then 1 else 0 := by
  apply trace_of_map_basis Finsupp.basisSingleOne f σ
  simpa only [Finsupp.coe_basisSingleOne] using hf

variable {K M : Type*} [Group K] [Fintype K] [AddCommGroup M]
  [Module k M] [Invertible (Fintype.card K : k)]

/-- Over a field in which the group order is invertible, coinvariants and
invariants are canonically linearly equivalent by averaging. -/
def coinvariantsEquivInvariants (ρ : Representation k K M) :
    ρ.Coinvariants ≃ₗ[k] ρ.invariants := by
  let toInv : ρ.Coinvariants →ₗ[k] ρ.invariants :=
    Representation.Coinvariants.lift ρ
      (ρ.isProj_averageMap.codRestrict) (fun g ↦ by
        ext x
        change ρ.averageMap (ρ g x) = ρ.averageMap x
        change
          ρ.asAlgebraHom (GroupAlgebra.average k K) (ρ g x) =
            ρ.asAlgebraHom (GroupAlgebra.average k K) x
        rw [← Representation.asAlgebraHom_single_one ρ g,
          ← Module.End.mul_apply, ← map_mul,
          GroupAlgebra.mul_average_right])
  let fromInv : ρ.invariants →ₗ[k] ρ.Coinvariants :=
    Representation.Coinvariants.mk ρ ∘ₗ ρ.invariants.subtype
  exact LinearEquiv.ofLinear toInv fromInv
    (by
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply,
        Representation.Coinvariants.lift_mk, fromInv, toInv]
      exact ρ.isProj_averageMap.map_id x x.2)
    (by
      apply Representation.Coinvariants.hom_ext
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply,
        Representation.Coinvariants.lift_mk, fromInv, toInv]
      simp only [Representation.averageMap, GroupAlgebra.average,
        invOf_eq_inv, MonoidAlgebra.of_apply, map_smul, map_sum,
        Representation.asAlgebraHom_single, one_smul,
        Submodule.subtype_apply, LinearMap.IsProj.codRestrict_apply,
        LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
        Representation.Coinvariants.mk_self_apply, Finset.sum_const,
        Finset.card_univ, LinearMap.id_coe, id_eq]
      rw [← Nat.cast_smul_eq_nsmul k, ← mul_smul,
        inv_mul_cancel₀ (Invertible.ne_zero _), one_smul])

@[simp]
theorem coinvariantsEquivInvariants_mk (ρ : Representation k K M) (x : M) :
    coinvariantsEquivInvariants ρ (Representation.Coinvariants.mk ρ x) =
      ρ.isProj_averageMap.codRestrict x :=
  rfl

@[simp]
theorem coinvariantsEquivInvariants_symm_apply
    (ρ : Representation k K M) (x : ρ.invariants) :
    (coinvariantsEquivInvariants ρ).symm x =
      Representation.Coinvariants.mk ρ x :=
  rfl

/-- An equivariant endomorphism commutes with the averaging projection. -/
theorem averageMap_comm (ρ : Representation k K M)
    (f : ρ.IntertwiningMap ρ) :
    ρ.averageMap ∘ₗ f.toLinearMap =
      f.toLinearMap ∘ₗ ρ.averageMap := by
  ext x
  simp [Representation.averageMap, GroupAlgebra.average, _root_.map_sum,
    f.isIntertwining]

/-- The trace on the range of a projection can be computed on the ambient
space by composing with that projection. -/
theorem trace_restrict_eq_trace_projection {U : Submodule k M}
    [Module.Finite k M] {p T : M →ₗ[k] M}
    (hp : LinearMap.IsProj U p)
    (hT : Set.MapsTo T U U) :
    LinearMap.trace k U (T.restrict hT) =
      LinearMap.trace k M (p ∘ₗ T) := by
  symm
  calc
    LinearMap.trace k M (p ∘ₗ T) =
        LinearMap.trace k M
          (U.subtype ∘ₗ (hp.codRestrict ∘ₗ T)) := by
            rw [← LinearMap.comp_assoc, hp.subtype_comp_codRestrict]
    _ = LinearMap.trace k U
          ((hp.codRestrict ∘ₗ T) ∘ₗ U.subtype) :=
      LinearMap.trace_comp_comm' _ _
    _ = LinearMap.trace k U (T.restrict hT) := by
      congr 1
      ext x
      exact hp.map_id (T x) (hT x.2)

end LinearAlgebra

namespace InductionCharacter

variable {G : Type} [Group G] [Fintype G]

local instance subgroupFintype (S : Subgroup G) : Fintype S :=
  Fintype.ofFinite S

local instance : DecidableEq G :=
  Classical.decEq G

/-- The ambient tensor product whose `S`-coinvariants define induction. -/
abbrev Ambient (S : Subgroup G) (V : FDRep ℂ S) :=
  TensorProduct ℂ (MonoidAlgebra ℂ G) V

/-- The `S`-action on the ambient tensor product used in mathlib's
coinvariant model of induction. -/
abbrev ambientRepresentation (S : Subgroup G) (V : FDRep ℂ S) :
    Representation ℂ S (Ambient S V) :=
  Representation.tprod
    ((Representation.leftRegular ℂ G).comp S.subtype) V.ρ

/-- Right translation by `g⁻¹` on the group-algebra tensor factor.  This is
the ambient map that descends to the action of `g` on induction. -/
def ambientAction (S : Subgroup G) (V : FDRep ℂ S) (g : G) :
    Ambient S V →ₗ[ℂ] Ambient S V :=
  (MonoidAlgebra.mapDomainLinearMap ℂ ℂ fun x : G ↦ x * g⁻¹).rTensor V

/-- The group-algebra permutation occurring after a subgroup element acts
and then the ambient right translation acts. -/
def groupAlgebraPermutation (s g : G) :
    MonoidAlgebra ℂ G →ₗ[ℂ] MonoidAlgebra ℂ G :=
  MonoidAlgebra.mapDomainLinearMap ℂ ℂ fun x : G ↦ s * x * g⁻¹

omit [Fintype G] in
@[simp]
theorem groupAlgebraPermutation_single (s g x : G) :
    groupAlgebraPermutation s g (.single x 1) =
      .single (s * x * g⁻¹) 1 := by
  simp [groupAlgebraPermutation]

/-- The trace of the group-algebra permutation is its number of fixed group
elements. -/
theorem trace_groupAlgebraPermutation (s g : G) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
        (groupAlgebraPermutation s g) =
      ∑ x : G, if s * x * g⁻¹ = x then 1 else 0 :=
  trace_of_map_basis (MonoidAlgebra.basis G ℂ)
    (groupAlgebraPermutation s g) (fun x ↦ s * x * g⁻¹) (by
      intro x
      simp only [MonoidAlgebra.basis_apply]
      exact groupAlgebraPermutation_single s g x)

/-- The ambient action commutes with the subgroup action. -/
def ambientActionIntertwining (S : Subgroup G) (V : FDRep ℂ S)
    (g : G) :
    (ambientRepresentation S V).IntertwiningMap
      (ambientRepresentation S V) :=
  ⟨ambientAction S V g, fun _ ↦ by
    ext
    simp [ambientAction, mul_assoc]⟩

omit [Fintype G] in
/-- The action on mathlib's coinvariant model of induction is induced by
`ambientAction`. -/
theorem ind_action_eq_coinvariantsMap [Finite G] (S : Subgroup G)
    (V : FDRep ℂ S) (g : G) :
    (FDRep.ind S.subtype V).ρ g =
      Representation.Coinvariants.map
        (ambientRepresentation S V) (ambientRepresentation S V)
        (ambientActionIntertwining S V g) :=
  rfl

omit [Fintype G] in
/-- A subgroup action followed by the ambient induction action is a tensor
product of the corresponding group-algebra permutation and the original
representation action. -/
theorem ambientRepresentation_comp_ambientAction (S : Subgroup G)
    (V : FDRep ℂ S) (s : S) (g : G) :
    (ambientRepresentation S V) s ∘ₗ ambientAction S V g =
      TensorProduct.map (groupAlgebraPermutation (s : G) g) (V.ρ s) := by
  ext
  simp [ambientAction, groupAlgebraPermutation, mul_assoc]

/-- The trace of one summand in the averaged ambient action. -/
theorem trace_ambientRepresentation_comp_ambientAction
    (S : Subgroup G) (V : FDRep ℂ S) (s : S) (g : G) :
    LinearMap.trace ℂ (Ambient S V)
        ((ambientRepresentation S V) s ∘ₗ ambientAction S V g) =
      (∑ x : G, if s.1 * x * g⁻¹ = x then 1 else 0) *
        V.character s := by
  rw [ambientRepresentation_comp_ambientAction,
    LinearMap.trace_tensorProduct',
    trace_groupAlgebraPermutation]
  rfl

/-- Expanding the averaging projection expresses the ambient trace as a
finite sum of the tensor-product trace summands. -/
theorem trace_average_comp_ambientAction (S : Subgroup G)
    (V : FDRep ℂ S) [Invertible (Fintype.card S : ℂ)] (g : G) :
    LinearMap.trace ℂ (Ambient S V)
        ((ambientRepresentation S V).averageMap ∘ₗ
          ambientAction S V g) =
      (Fintype.card S : ℂ)⁻¹ *
        ∑ s : S,
          (∑ x : G, if s.1 * x * g⁻¹ = x then 1 else 0) *
            V.character s := by
  have havg :
      (ambientRepresentation S V).averageMap =
        (Fintype.card S : ℂ)⁻¹ •
          ∑ s : S, (ambientRepresentation S V) s := by
    ext x
    simp [Representation.averageMap, GroupAlgebra.average, _root_.map_sum]
  rw [havg, LinearMap.smul_comp, map_smul]
  have hcomp :
      (∑ s : S, (ambientRepresentation S V) s) ∘ₗ
          ambientAction S V g =
        ∑ s : S,
          (ambientRepresentation S V) s ∘ₗ ambientAction S V g := by
    ext
    simp
  rw [hcomp, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact trace_ambientRepresentation_comp_ambientAction S V s g

omit [Fintype G] in
/-- The fixed-point equation for the group-algebra permutation is equivalent
to identifying the subgroup element with a conjugate of `g`. -/
theorem mul_mul_inv_eq_iff_eq_conj (s x g : G) :
    s * x * g⁻¹ = x ↔ s = x * g * x⁻¹ := by
  constructor
  · intro h
    calc
      s = (s * x * g⁻¹) * g * x⁻¹ := by group
      _ = x * g * x⁻¹ := by rw [h]
  · intro h
    rw [h]
    group

/-- For a fixed group element `x`, summing over subgroup elements collapses
to the single classical induction summand indexed by `x⁻¹`. -/
theorem sum_subgroup_fixed_eq_inductionTerm (S : Subgroup G)
    (V : FDRep ℂ S) (x g : G) :
    (∑ s : S,
        if s.1 * x * g⁻¹ = x then V.character s else 0) =
      ClassFunction.inductionTerm S V.characterClassFunction x⁻¹ g := by
  by_cases hx : x * g * x⁻¹ ∈ S
  · let t : S := ⟨x * g * x⁻¹, hx⟩
    have hfixed (s : S) :
        s.1 * x * g⁻¹ = x ↔ s = t := by
      rw [mul_mul_inv_eq_iff_eq_conj]
      constructor
      · intro hs
        apply Subtype.ext
        exact hs
      · intro hs
        exact congrArg Subtype.val hs
    have hsum :
        (∑ s : S,
            if s.1 * x * g⁻¹ = x then V.character s else 0) =
          V.character t := by
      simp_rw [hfixed]
      exact Fintype.sum_ite_eq' t V.character
    rw [hsum]
    have hx' : (x⁻¹)⁻¹ * g * x⁻¹ ∈ S := by
      simpa using hx
    rw [ClassFunction.inductionTerm_of_mem S
      V.characterClassFunction hx']
    congr 1
    apply Subtype.ext
    simp [t]
  · have hnone (s : S) : ¬s.1 * x * g⁻¹ = x := by
      intro hs
      apply hx
      rw [← (mul_mul_inv_eq_iff_eq_conj s.1 x g).mp hs]
      exact s.2
    have hx' : (x⁻¹)⁻¹ * g * x⁻¹ ∉ S := by
      simpa using hx
    simp [hnone, ClassFunction.inductionTerm_of_not_mem S
      V.characterClassFunction hx']

/-- The double trace sum is exactly the unnormalized classical
induced-character sum. -/
theorem sum_trace_terms_eq_sum_inductionTerm (S : Subgroup G)
    (V : FDRep ℂ S) (g : G) :
    (∑ s : S,
        (∑ x : G, if s.1 * x * g⁻¹ = x then 1 else 0) *
          V.character s) =
      ∑ x : G,
        ClassFunction.inductionTerm S V.characterClassFunction x g := by
  calc
    (∑ s : S,
        (∑ x : G, if s.1 * x * g⁻¹ = x then 1 else 0) *
          V.character s) =
        ∑ s : S, ∑ x : G,
          if s.1 * x * g⁻¹ = x then V.character s else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : s.1 * x * g⁻¹ = x <;> simp [h]
    _ = ∑ x : G, ∑ s : S,
          if s.1 * x * g⁻¹ = x then V.character s else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : G,
          ClassFunction.inductionTerm S V.characterClassFunction x⁻¹ g := by
      apply Finset.sum_congr rfl
      intro x _
      exact sum_subgroup_fixed_eq_inductionTerm S V x g
    _ = ∑ x : G,
          ClassFunction.inductionTerm S V.characterClassFunction x g :=
      Equiv.sum_comp (Equiv.inv G)
        (fun x ↦ ClassFunction.inductionTerm
          S V.characterClassFunction x g)

omit [Fintype G] in
/-- The ambient action preserves the invariant subspace. -/
theorem ambientAction_mapsTo_invariants (S : Subgroup G)
    (V : FDRep ℂ S) (g : G) :
    Set.MapsTo (ambientAction S V g)
      (ambientRepresentation S V).invariants
      (ambientRepresentation S V).invariants := by
  intro x hx s
  calc
    (ambientRepresentation S V) s (ambientAction S V g x) =
        ambientAction S V g ((ambientRepresentation S V) s x) :=
      (Representation.IntertwiningMap.isIntertwining
        (ambientRepresentation S V) (ambientRepresentation S V)
        (ambientActionIntertwining S V g) s x).symm
    _ = ambientAction S V g x :=
      congrArg (ambientAction S V g) (hx s)

/-- The averaging equivalence from the coinvariant carrier of induction to
the corresponding invariant subspace. -/
abbrev indEquivInvariants (S : Subgroup G) (V : FDRep ℂ S)
    [Invertible (Fintype.card S : ℂ)] :
    FDRep.ind S.subtype V ≃ₗ[ℂ]
      (ambientRepresentation S V).invariants :=
  coinvariantsEquivInvariants (ambientRepresentation S V)

/-- Under the coinvariants--invariants equivalence, the action on induction
is the restriction of the ambient right-translation action. -/
theorem indEquivInvariants_conj (S : Subgroup G) (V : FDRep ℂ S)
    [Invertible (Fintype.card S : ℂ)] (g : G) :
    (indEquivInvariants S V).conj ((FDRep.ind S.subtype V).ρ g) =
      (ambientAction S V g).restrict
        (ambientAction_mapsTo_invariants S V g) := by
  ext x
  change
    (ambientRepresentation S V).averageMap
        (ambientAction S V g x) =
      ambientAction S V g x
  calc
    (ambientRepresentation S V).averageMap
        (ambientAction S V g x) =
        ambientAction S V g
          ((ambientRepresentation S V).averageMap x) := by
      simpa [LinearMap.comp_apply, ambientActionIntertwining] using
        LinearMap.ext_iff.mp
        (averageMap_comm (ambientRepresentation S V)
          (ambientActionIntertwining S V g)) x
    _ = ambientAction S V g x :=
      congrArg (ambientAction S V g)
        ((ambientRepresentation S V).isProj_averageMap.map_id x x.2)

/-- The character of induction is the ambient trace of right translation
composed with the subgroup-averaging projection. -/
theorem ind_character_eq_trace_average_comp (S : Subgroup G)
    (V : FDRep ℂ S) [Invertible (Fintype.card S : ℂ)] (g : G) :
    (FDRep.ind S.subtype V).character g =
      LinearMap.trace ℂ (Ambient S V)
        ((ambientRepresentation S V).averageMap ∘ₗ
          ambientAction S V g) := by
  change
    LinearMap.trace ℂ (FDRep.ind S.subtype V)
        ((FDRep.ind S.subtype V).ρ g) = _
  calc
    LinearMap.trace ℂ (FDRep.ind S.subtype V)
        ((FDRep.ind S.subtype V).ρ g) =
        LinearMap.trace ℂ (ambientRepresentation S V).invariants
          ((indEquivInvariants S V).conj
            ((FDRep.ind S.subtype V).ρ g)) :=
      by
        simpa only using
          (LinearMap.trace_conj'
            (R := ℂ)
            (M := FDRep.ind S.subtype V)
            (N := (ambientRepresentation S V).invariants)
            ((FDRep.ind S.subtype V).ρ g)
            (indEquivInvariants S V)).symm
    _ = LinearMap.trace ℂ (ambientRepresentation S V).invariants
          ((ambientAction S V g).restrict
            (ambientAction_mapsTo_invariants S V g)) := by
      rw [indEquivInvariants_conj]
    _ = LinearMap.trace ℂ (Ambient S V)
          ((ambientRepresentation S V).averageMap ∘ₗ
            ambientAction S V g) :=
      trace_restrict_eq_trace_projection
        (ambientRepresentation S V).isProj_averageMap
        (ambientAction_mapsTo_invariants S V g)

/-- The character of mathlib's coinvariant model of subgroup induction is
the classical induced character. -/
theorem ind_character_eq_induce (S : Subgroup G) (V : FDRep ℂ S)
    (g : G) :
    (FDRep.ind S.subtype V).character g =
      ClassFunction.induce S V.characterClassFunction g := by
  letI : Invertible (Fintype.card S : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [ind_character_eq_trace_average_comp,
    trace_average_comp_ambientAction,
    sum_trace_terms_eq_sum_inductionTerm,
    ClassFunction.induce_apply,
    Nat.card_eq_fintype_card]

/-- Bundled form of the ordinary induced-character formula. -/
theorem ind_characterClassFunction_eq_induce (S : Subgroup G)
    (V : FDRep ℂ S) :
    (FDRep.ind S.subtype V).characterClassFunction =
      ClassFunction.induce S V.characterClassFunction := by
  ext g
  exact ind_character_eq_induce S V g

end InductionCharacter

end McKayConjecture
