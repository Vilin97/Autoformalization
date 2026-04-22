import Aristotle.GrothendieckVanishing.main.ClosedImmersionCohomology
import Aristotle.GrothendieckVanishing.main.TopologicalKrullDim
import Aristotle.GrothendieckVanishing.main.ZeroOutside

/-!
  ConstantSheafFlasque.lean — The constant sheaf on an irreducible space is flasque
-/

universe u

open CategoryTheory TopologicalSpace Limits Opposite GrothendieckTopology GrothendieckTopology.Plus

/-- The presheaf on `X` with constant value `A`. This is the presheaf input whose
sheafification is the constant sheaf used in the irreducible flasqueness argument. -/
abbrev constPresheaf (X : Type u) [TopologicalSpace X]
    (A : AddCommGrpCat.{u}) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Functor.const (Opens X)ᵒᵖ).obj A

theorem toPlus_injective_of_const
    {X : Type u} [TopologicalSpace X] {A : AddCommGrpCat.{u}}
    (U : Opens X) (hU : (U : Set X).Nonempty)
    (a b : (constPresheaf X A).obj (op U))
    (h : ConcreteCategory.hom (((Opens.grothendieckTopology X).toPlus (constPresheaf X A)).app (op U)) a =
      ConcreteCategory.hom (((Opens.grothendieckTopology X).toPlus (constPresheaf X A)).app (op U)) b) :
    a = b := by
  rw [toPlus_eq_mk, toPlus_eq_mk] at h
  rw [eq_mk_iff_exists] at h
  obtain ⟨W, _, _, heq⟩ := h
  obtain ⟨p, hp⟩ := hU
  obtain ⟨V, f, hf, _⟩ := W.2 p hp
  simpa [Meq.refine, Meq.mk] using
    congr_fun (congr_arg Subtype.val heq) (⟨V, f, hf⟩ : W.Arrow)

theorem toPlus_surjective_of_const
    {X : Type u} [TopologicalSpace X] {A : AddCommGrpCat.{u}}
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective
      (ConcreteCategory.hom (((Opens.grothendieckTopology X).toPlus (constPresheaf X A)).app (op U))) := by
  intro y; obtain ⟨S, x, hx⟩ := exists_rep y
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨V₀, f₀, hf₀, hx₀mem⟩ := S.2 x₀ hx₀
  let I₀ : S.Arrow := ⟨V₀, f₀, hf₀⟩
  have hI₀ : (I₀.Y : Set X).Nonempty := ⟨x₀, hx₀mem⟩
  refine ⟨x I₀, ?_⟩
  rw [hx, show x = Meq.mk S (x I₀) from Meq.ext _ _ fun I => by
      simpa [constPresheaf] using x.condition (Cover.Relation.mk' (fst := I) (snd := I₀)
        ⟨I.Y ⊓ I₀.Y, homOfLE inf_le_left, homOfLE inf_le_right, Subsingleton.elim _ _⟩),
      toPlus_eq_mk, eq_mk_iff_exists]
  refine ⟨S, homOfLE le_top, 𝟙 S, ?_⟩
  apply Meq.ext; intro I
  simp [Meq.refine, Meq.mk, constPresheaf]

theorem toPlus_naturality_const
    {X : Type u} [TopologicalSpace X] {A : AddCommGrpCat.{u}}
    {U V : Opens X} (i : U ⟶ V) (a : (constPresheaf X A).obj (op V)) :
    ConcreteCategory.hom (((Opens.grothendieckTopology X).toPlus (constPresheaf X A)).app (op U)) a =
      ConcreteCategory.hom (((Opens.grothendieckTopology X).plusObj (constPresheaf X A)).map i.op)
        (ConcreteCategory.hom (((Opens.grothendieckTopology X).toPlus (constPresheaf X A)).app (op V)) a) := by
  have nat := ((Opens.grothendieckTopology X).toPlus (constPresheaf X A)).naturality i.op
  calc ConcreteCategory.hom (((Opens.grothendieckTopology X).toPlus (constPresheaf X A)).app (op U)) a
      = ConcreteCategory.hom ((constPresheaf X A).map i.op ≫
          ((Opens.grothendieckTopology X).toPlus (constPresheaf X A)).app (op U)) a := by simp
    _ = ConcreteCategory.hom (((Opens.grothendieckTopology X).toPlus (constPresheaf X A)).app (op V) ≫
          ((Opens.grothendieckTopology X).plusObj (constPresheaf X A)).map i.op) a := by rw [nat]
    _ = _ := ConcreteCategory.comp_apply _ _ _

theorem toPlus_surjective_of_firstPlus
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X] {A : AddCommGrpCat.{u}}
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ConcreteCategory.hom
      (((Opens.grothendieckTopology X).toPlus ((Opens.grothendieckTopology X).plusObj (constPresheaf X A))).app (op U))) := by
  intro y; obtain ⟨S, x, hx⟩ := exists_rep y
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨V₀, f₀, hf₀, hx₀mem⟩ := S.2 x₀ hx₀
  let I₀ : S.Arrow := ⟨V₀, f₀, hf₀⟩
  have hI₀ : (I₀.Y : Set X).Nonempty := ⟨x₀, hx₀mem⟩
  obtain ⟨a, ha⟩ := toPlus_surjective_of_const I₀.Y hI₀ (x I₀)
  use ConcreteCategory.hom (((Opens.grothendieckTopology X).toPlus (constPresheaf X A)).app (op U)) a
  rw [hx, toPlus_eq_mk, eq_mk_iff_exists]
  refine ⟨S, homOfLE le_top, 𝟙 S, ?_⟩
  apply Meq.ext; intro I
  simp only [Meq.refine, Meq.mk]
  by_cases hI : (I.Y : Set X).Nonempty
  · have hkey :
        x I = ConcreteCategory.hom
          (((Opens.grothendieckTopology X).plusObj (constPresheaf X A)).map I.f.op)
            (ConcreteCategory.hom
              (((Opens.grothendieckTopology X).toPlus (constPresheaf X A)).app (op U)) a) := by
        obtain ⟨b, hb⟩ := toPlus_surjective_of_const I.Y hI (x I)
        have hZne : ((I₀.Y ⊓ I.Y : Opens X) : Set X).Nonempty :=
          nonempty_preirreducible_inter I₀.Y.isOpen I.Y.isOpen hI₀ hI
        let R : S.Relation := Cover.Relation.mk' (fst := I₀) (snd := I)
          ⟨I₀.Y ⊓ I.Y, homOfLE inf_le_left, homOfLE inf_le_right, Subsingleton.elim _ _⟩
        have hcond := x.condition R
        change ConcreteCategory.hom (((Opens.grothendieckTopology X).plusObj (constPresheaf X A)).map
            (homOfLE inf_le_left).op) (x I₀) =
          ConcreteCategory.hom (((Opens.grothendieckTopology X).plusObj (constPresheaf X A)).map
            (homOfLE inf_le_right).op) (x I) at hcond
        rw [← ha, ← hb] at hcond
        rw [← toPlus_naturality_const (homOfLE (inf_le_left (a := I₀.Y) (b := I.Y))) a,
            ← toPlus_naturality_const (homOfLE (inf_le_right (a := I₀.Y) (b := I.Y))) b] at hcond
        have hab : a = b := toPlus_injective_of_const _ hZne a b hcond
        rw [← hb, ← hab]
        exact toPlus_naturality_const I.f a
    exact hkey.symm
  · rw [Set.not_nonempty_iff_eq_empty] at hI
    have hIbot : I.Y = ⊥ := Opens.ext (by simpa using hI)
    have hcov : (⊥ : Sieve (⊥ : Opens X)) ∈ (Opens.grothendieckTopology X) ⊥ :=
      fun _ hp => (Opens.mem_bot.mp hp).elim
    exact @Subsingleton.elim _ (hIbot ▸ ⟨fun x y =>
      Plus.sep _ ⟨⊥, hcov⟩ x y fun ⟨_, _, hf⟩ => absurd hf id⟩) _ _

/-- On an irreducible space, the sheafification of the constant presheaf is flasque. -/
theorem sheafify_constPresheaf_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X] {A : AddCommGrpCat.{u}}
    {U V : Opens X} (i : U ⟶ V) :
    Epi (((Opens.grothendieckTopology X).sheafify (constPresheaf X A)).map i.op) := by
  by_cases hU : (U : Set X) = ∅
  · have : U = ⊥ := Opens.ext (by simpa using hU)
    subst this
    rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    haveI : Subsingleton (ToType (((Opens.grothendieckTopology X).sheafify (constPresheaf X A)).obj (op ⊥))) :=
      AddCommGrpCat.subsingleton_of_isZero
        (TopCat.Sheaf.isTerminalOfEmpty
          ⟨_, (Opens.grothendieckTopology X).sheafify_isSheaf (constPresheaf X A)⟩).isZero
    exact ⟨0, Subsingleton.elim _ _⟩
  · have hUne : (U : Set X).Nonempty := Set.nonempty_iff_ne_empty.mpr hU
    have hnat := ((Opens.grothendieckTopology X).toSheafify (constPresheaf X A)).naturality i.op
    rw [show (constPresheaf X A).map i.op = 𝟙 _ from by ext; simp [constPresheaf],
        Category.id_comp] at hnat
    have hfac : ((Opens.grothendieckTopology X).toSheafify (constPresheaf X A)).app (op V) ≫
        ((Opens.grothendieckTopology X).sheafify (constPresheaf X A)).map i.op =
        ((Opens.grothendieckTopology X).toSheafify (constPresheaf X A)).app (op U) := hnat.symm
    haveI : Epi (((Opens.grothendieckTopology X).toSheafify (constPresheaf X A)).app (op U)) := by
      apply ConcreteCategory.epi_of_surjective
      rw [show ((Opens.grothendieckTopology X).toSheafify (constPresheaf X A)).app (op U) =
          ((Opens.grothendieckTopology X).toPlus (constPresheaf X A)).app (op U) ≫
          ((Opens.grothendieckTopology X).toPlus ((Opens.grothendieckTopology X).plusObj (constPresheaf X A))).app (op U) from by
        simp only [GrothendieckTopology.toSheafify, (Opens.grothendieckTopology X).plusMap_toPlus, NatTrans.comp_app]]
      intro y; obtain ⟨z, hz⟩ := toPlus_surjective_of_firstPlus (X := X) U hUne y
      obtain ⟨a, ha⟩ := toPlus_surjective_of_const (X := X) U hUne z
      exact ⟨a, by rw [ConcreteCategory.comp_apply, ha]; exact hz⟩
    exact epi_of_epi_fac hfac

/-- On an irreducible space, the presheaf-to-sheaf image of the constant presheaf is flasque. -/
theorem presheafToSheaf_constPresheaf_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X] {A : AddCommGrpCat.{u}}
    {U V : Opens X} (i : U ⟶ V) :
    Epi (((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (constPresheaf X A)).val.map i.op) := by
  let e := plusPlusIsoSheafify (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) (P := constPresheaf X A)
  haveI := sheafify_constPresheaf_flasque_of_irreducible (X := X) (A := A) (i := i)
  haveI : Epi (e.hom.app (op V) ≫
      (CategoryTheory.sheafify (Opens.grothendieckTopology X) (constPresheaf X A)).map i.op) := by
    rw [← e.hom.naturality i.op]; infer_instance
  exact epi_of_epi (e.hom.app (op V))
    ((CategoryTheory.sheafify (Opens.grothendieckTopology X) (constPresheaf X A)).map i.op)

theorem constantSheaf_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X]
    (A : AddCommGrpCat.{u})
    {U V : Opens X} (i : U ⟶ V) :
    Epi (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      A).val.map i.op) := by
  simpa [CategoryTheory.constantSheaf, constPresheaf] using
    (presheafToSheaf_constPresheaf_flasque_of_irreducible (X := X) (i := i))

/-- `zeroOutsideInt ⊤` is flasque on an irreducible space: it is the sheafification of
    `constZ.zeroOutside ⊤ ≅ constZ` (via `zeroOutside_top_iso`), and the constant sheaf
    on an irreducible space is flasque (`constantSheaf_flasque_of_irreducible`). -/
instance isFlasqueSheaf_zeroOutsideInt_top (X : TopCat.{u}) [IrreducibleSpace X] :
    IsFlasqueSheaf (TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X)) := by
  constructor; intro U W i
  let J := Opens.grothendieckTopology (T := X)
  let A := AddCommGrpCat.of (ULift.{u} ℤ)
  have h := constantSheaf_flasque_of_irreducible X A i
  exact @epi_of_epi_fac _ _ _ _ _ _ _ _ (epi_comp' h (IsIso.epi_of_iso _))
    (((sheafToPresheaf J AddCommGrpCat.{u}).mapIso
      ((presheafToSheaf J AddCommGrpCat.{u}).mapIso
        (TopCat.Presheaf.zeroOutside_top_iso (F := TopCat.Presheaf.constZ))).symm).hom.naturality
      i.op).symm
