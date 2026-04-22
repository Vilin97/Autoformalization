import Aristotle.GrothendieckVanishing.main.CohomologyAPI
import Aristotle.GrothendieckVanishing.main.ClosedImmersionCohomology
import Aristotle.GrothendieckVanishing.main.ConstantSheafFlasque
import Aristotle.GrothendieckVanishing.main.FiniteGeneratorReduction
import Aristotle.GrothendieckVanishing.main.ZeroOutside

/-!
  SheafStalkAlgebra.lean — Stalk algebra for sheaves of abelian groups

  Split from IrreducibleStep.lean. Contains:
  - zeroOutsideInt cohomology vanishing (zeroOutsideInt_cohomology_vanishing)
  - exists_nonzero_stalk_in_V: nonzero subsheaf has nonzero stalk in V
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-- **Step 5** (Hartshorne III.2.7): given vanishing of the cokernel of
    `openHom(V ≤ ⊤)` at degree `m`, deduce vanishing of `zeroOutsideInt V` at
    degree `m + 1`. Uses the SES `0 → zeroOutsideInt V → zeroOutsideInt ⊤ → cokernel → 0`
    where `zeroOutsideInt ⊤ = Z_X` (constant sheaf, flasque on irreducible spaces). -/
theorem zeroOutsideInt_vanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (m : ℕ)
    (hCoker : Subsingleton (Sheaf.H (Limits.cokernel
      (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤))) m)) :
    Subsingleton (Sheaf.H (TopCat.Sheaf.zeroOutsideInt V) (m + 1)) := by
  have hfsh : Mono (TopCat.Sheaf.zeroOutsideInt.openHom
      (le_top : V ≤ (⊤ : Opens X))) := by
    infer_instance
  haveI : Mono ((TopCat.Sheaf.zeroOutsideInt.openHom
      (le_top : V ≤ (⊤ : Opens X))).val) := by
    exact (Sheaf.Hom.mono_iff_presheaf_mono
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u})
      (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ (⊤ : Opens X)))).1 hfsh
  have hTop : Subsingleton (Sheaf.H (TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X)) (m + 1)) := by
    let F : TopCat.Presheaf AddCommGrpCat.{u} X :=
      (TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X)).val
    have hF : F.IsSheaf := by
      simpa [F] using (TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X)).cond
    letI : IsFlasqueSheaf ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
      simpa [F, hF] using isFlasqueSheaf_zeroOutsideInt_top X
    simpa [F, hF] using
      (sheafH_subsingleton_of_flasque_presheaf (X := X) (F := F) hF m)
  exact sheafH_dimension_shift_of_mono_presheaf
    (F := (TopCat.Sheaf.zeroOutsideInt V).val)
    (G := (TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X)).val)
    (hF := (TopCat.Sheaf.zeroOutsideInt V).cond)
    (hG := (TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X)).cond)
    (f := (TopCat.Sheaf.zeroOutsideInt.openHom
      (le_top : V ≤ (⊤ : Opens X))).val)
    (n := m)
    hCoker hTop

/-! ## Sub-lemmas for Hartshorne III.2.7 Steps 3-5

These lemmas decompose the kernel vanishing argument.
`exists_good_section` is in `IrreducibleStep.lean`.
`sheafH_preserves_filtered_colimits` and `cohomology_vanishing_of_finitelyGenerated_vanishing`
are in `FiniteGeneratorReduction.lean`.
-/

/-- **Step 5** (Hartshorne III.2.7): `zeroOutsideInt V` has vanishing cohomology in every
    degree `m > dim X` on an irreducible Noetherian space.
    Proof: write `m = m' + 1`, apply `zeroOutsideInt_vanishing` (SES + flasque), then prove
    cokernel vanishing at `m'` via `closedImmersionSES` on `Vᶜ` + `PushforwardHVanishing`. -/
theorem zeroOutsideInt_cohomology_vanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (hV : V ≠ ⊥)
    (ih : VanishingIH.{u} (topologicalKrullDim X))
    (m : ℕ) (hm : m > topologicalKrullDim X) :
    Subsingleton (Sheaf.H (TopCat.Sheaf.zeroOutsideInt V) m) := by
  let C := Limits.cokernel (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤))
  -- m ≠ 0 (since m > dim X ≥ 0), write m = m' + 1
  have hm_ne : m ≠ 0 := by
    intro h; subst h; exact absurd hm (not_lt.mpr topologicalKrullDim_nonneg)
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne
  have hVcompl_lt_succ :
      topologicalKrullDim (Set.compl (V : Set X)) < ↑↑(m' + 1 : ℕ) :=
    topologicalKrullDim_subspace_lt_of_lt (X := X) (Set.compl (V : Set X))
      (by simpa [gt_iff_lt] using hm)
  have hVcompl_lt_top : topologicalKrullDim (Set.compl (V : Set X)) < ⊤ :=
    topologicalKrullDim_lt_top_of_lt_nat hVcompl_lt_succ
  have hVcompl_lt_X : topologicalKrullDim (Set.compl (V : Set X)) < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed
      V.2.isClosed_compl
      (Set.compl_ne_univ.mpr (Set.nonempty_iff_ne_empty.mpr
        (Opens.coe_eq_empty.not.mpr hV)))
      hVcompl_lt_top
  have hVcompl_lt_m' : topologicalKrullDim (Set.compl (V : Set X)) < ↑↑(m' : ℕ) :=
    topologicalKrullDim_lt_nat_of_lt_of_lt_nat_succ hVcompl_lt_X
      (by simpa [gt_iff_lt] using hm)
  -- Step 2: apply zeroOutsideInt_vanishing, reducing to cokernel vanishing at m'
  apply zeroOutsideInt_vanishing V m'
  -- Cokernel vanishing at m': use closedComplementVanishing with m' > dim Vᶜ
  exact closedComplementVanishing V hV (C := C.val) C.cond m' ih
    (by simpa [gt_iff_lt] using hVcompl_lt_m')
    (fun x hxV a => cokernel_stalk_zero_of_stalk_surj
      (F := (TopCat.Sheaf.zeroOutsideInt V).val)
      (G := (TopCat.Sheaf.zeroOutsideInt ⊤).val)
      (hF := (TopCat.Sheaf.zeroOutsideInt V).cond)
      (hG := (TopCat.Sheaf.zeroOutsideInt ⊤).cond)
      (f := (TopCat.Sheaf.zeroOutsideInt.openHom (le_top : V ≤ ⊤)).val)
      (x := x)
      (hf := sheafifyMap_zeroOutside_openHom_stalk_surj Presheaf.constZ le_top x hxV) a)

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
