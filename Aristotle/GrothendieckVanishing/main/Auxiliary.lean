/-
  Auxiliary.lean — Topology and dimension helper lemmas

  Key results:
  - On irreducible spaces of dimension 0, the only opens are ⊥ and ⊤
  - Any morphism to a terminal object in an abelian category is epi
  - F(⊥) is terminal for any sheaf F on a topological space
-/
import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits

/-! ## Abelian category helpers -/

/-- In an abelian category, any morphism to a terminal (= zero) object is epi. -/
theorem epi_of_isTerminal_tgt {C : Type*} [Category C] [Abelian C] {X Y : C}
    (t : IsTerminal Y) (f : X ⟶ Y) : Epi f := by
  have hzero : IsZero Y := by
    rw [IsZero.iff_id_eq_zero]
    exact t.hom_ext _ _
  constructor
  intro Z g h _
  have hg : g = 0 := hzero.eq_of_src g 0
  have hh : h = 0 := hzero.eq_of_src h 0
  rw [hg, hh]

/-! ## Sheaf at the empty open set -/

/-- For any sheaf F on a topological space, F(⊥) = F(∅) is a terminal object.
    This follows from the sheaf condition on the empty cover. -/
noncomputable def isTerminal_sheaf_bot {X : Type u} [TopologicalSpace X]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    IsTerminal (F.val.obj (Opposite.op ⊥)) := by
  apply Sheaf.isTerminalOfBotCover
  intro x hx
  exact (Opens.mem_bot.mp hx).elim

/-! ## Irreducible spaces of dimension 0 -/

/-- On an irreducible space with topologicalKrullDim ≤ 0, every irreducible closed set
    equals the whole space. -/
theorem irreducibleCloseds_unique_of_dim_zero {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 0)
    (S : IrreducibleCloseds X) : (S : Set X) = Set.univ := by
  have hmax := (Order.krullDim_nonpos_iff_forall_isMax).mp hdim S
  have hle : S ≤ ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ :=
    Set.subset_univ _
  exact le_antisymm (Set.subset_univ _) (hmax hle)

/-- On an irreducible space of dimension 0, every point is dense. -/
theorem closure_singleton_eq_univ_of_dim_zero {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 0)
    (x : X) : closure ({x} : Set X) = Set.univ :=
  irreducibleCloseds_unique_of_dim_zero hdim
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- On an irreducible space of dimension ≤ 0, the only opens are ⊥ and ⊤.
    Every point is dense, so any nonempty open contains every point. -/
theorem opens_eq_bot_or_top_of_irreducibleSpace_dim_zero
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 0) (U : Opens X) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hne : (U : Set X).Nonempty
  · right
    ext x
    constructor
    · exact fun _ => trivial
    · intro _
      by_contra hx
      have hcl := closure_singleton_eq_univ_of_dim_zero hdim x
      have hsub : closure ({x} : Set X) ⊆ (U : Set X)ᶜ :=
        closure_minimal (Set.singleton_subset_iff.mpr hx) U.isOpen.isClosed_compl
      rw [hcl] at hsub
      obtain ⟨y, hy⟩ := hne
      exact hsub (Set.mem_univ y) hy
  · left
    exact Opens.ext (Set.not_nonempty_iff_eq_empty.mp hne)

/-! ## Dimension helpers -/

/-- On an irreducible space, the topological Krull dimension is ≥ 0. -/
theorem topologicalKrullDim_nonneg_of_irreducible {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] : topologicalKrullDim X ≥ 0 := by
  rw [topologicalKrullDim, ge_iff_le, Order.krullDim_nonneg_iff]
  exact ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
