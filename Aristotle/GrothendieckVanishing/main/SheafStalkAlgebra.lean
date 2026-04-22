import Aristotle.GrothendieckVanishing.main.CohomologyAPI
import Aristotle.GrothendieckVanishing.main.ZeroOutside

/-!
  SheafStalkAlgebra.lean — Stalk detection for subsheaves of `zeroOutsideInt`

  Split from `IrreducibleStep.lean`. This file now keeps only the stalk-level lemma
  used to start the irreducible Step 4 argument:
  - `exists_nonzero_stalk_in_V`: a nonzero subsheaf of `zeroOutsideInt V` has a nonzero
    stalk at some point of `V`
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-- A nonzero subsheaf of `zeroOutsideInt V` has a nonzero stalk at some point of `V`. -/
theorem exists_nonzero_stalk_in_V
    {X : TopCat.{u}} (V : Opens X)
    {R : TopCat.Presheaf AddCommGrpCat.{u} X} (hRsh : R.IsSheaf)
    (i : R ⟶ (TopCat.Sheaf.zeroOutsideInt V).val)
    [Mono i]
    (hR : ¬ IsZero R) :
    ∃ (x : X) (_ : x ∈ V)
      (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj R),
      a ≠ 0 := by
  let Rsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨R, hRsh⟩
  by_contra! h; apply hR
  have hRsh_zero : IsZero Rsh :=
    sheaf_isZero_of_zero_stalks X hRsh (fun x a => by
      by_cases hx : (x : X) ∈ (V : Set X)
      · exact h x hx a
      · have hi_inj : Function.Injective
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map i) :=
          TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective (f := i)
            (fun U =>
              (ConcreteCategory.mono_iff_injective_of_preservesPullback (i.app (op U))).mp
                ((NatTrans.mono_iff_mono_app i).mp inferInstance (op U))) x
        exact hi_inj ((stalk_zeroOutsideInt_zero_outside V x hx _).trans (map_zero _).symm)
      )
  refine Functor.isZero R ?_
  intro U
  have hforget_eval :
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U).PreservesZeroMorphisms := by
    refine ⟨?_⟩
    intro A B
    rfl
  simpa using Functor.map_isZero
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U) hRsh_zero
