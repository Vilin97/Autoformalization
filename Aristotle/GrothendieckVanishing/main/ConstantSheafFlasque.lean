/-
  ConstantSheafFlasque.lean — The constant sheaf on an irreducible space is flasque
-/
import Aristotle.GrothendieckVanishing.main.SetupCore
import Aristotle.GrothendieckVanishing.main.TopologicalKrullDim

universe u

open CategoryTheory TopologicalSpace Limits Opposite GrothendieckTopology GrothendieckTopology.Plus

private abbrev constPresheaf (X : Type u) [TopologicalSpace X]
    (A : AddCommGrpCat.{u}) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Functor.const (Opens X)ᵒᵖ).obj A

private abbrev opensGT (X : Type u) [TopologicalSpace X] : GrothendieckTopology (Opens X) :=
  Opens.grothendieckTopology X

theorem plusObj_bot_subsingleton {X : Type u} [TopologicalSpace X]
    (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Subsingleton (ToType (((Opens.grothendieckTopology X).plusObj P).obj (op ⊥))) := by
  constructor; intro x y
  have hcov : (⊥ : Sieve (⊥ : Opens X)) ∈ (Opens.grothendieckTopology X) ⊥ :=
    fun p hp => (Opens.mem_bot.mp hp).elim
  exact Plus.sep P ⟨⊥, hcov⟩ x y (fun ⟨_, _, hf⟩ => absurd hf id)

theorem toPlus_injective_of_const
    {X : Type u} [TopologicalSpace X] {A : AddCommGrpCat.{u}}
    (U : Opens X) (hU : (U : Set X).Nonempty)
    (a b : (constPresheaf X A).obj (op U))
    (h : ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X A)).app (op U)) a =
      ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X A)).app (op U)) b) :
    a = b := by
  rw [toPlus_eq_mk, toPlus_eq_mk] at h
  rw [eq_mk_iff_exists] at h
  obtain ⟨W, _, _, heq⟩ := h
  obtain ⟨p, hp⟩ := hU
  obtain ⟨V, f, hf, _⟩ := W.2 p hp
  simpa [Meq.refine, Meq.mk] using
    congr_fun (congr_arg Subtype.val heq) (⟨V, f, hf⟩ : W.Arrow)

private lemma cover_nonempty_arrow
    {X : Type u} [TopologicalSpace X]
    (U : Opens X) (hU : (U : Set X).Nonempty)
    (S : (opensGT X).Cover U) :
    ∃ I : S.Arrow, (I.Y : Set X).Nonempty := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨V, f, hf, hmem⟩ := S.2 x hx
  exact ⟨⟨V, f, hf⟩, ⟨x, hmem⟩⟩

private lemma cover_arrows_related
    {X : Type u} [TopologicalSpace X]
    {U : Opens X} (S : (opensGT X).Cover U) (I₁ I₂ : S.Arrow) :
    ∃ R : S.Relation, R.fst = I₁ ∧ R.snd = I₂ :=
  ⟨Cover.Relation.mk' (fst := I₁) (snd := I₂)
    ⟨I₁.Y ⊓ I₂.Y, homOfLE inf_le_left, homOfLE inf_le_right, Subsingleton.elim _ _⟩, rfl, rfl⟩

private lemma meq_const_values_eq
    {X : Type u} [TopologicalSpace X] {A : AddCommGrpCat.{u}}
    {U : Opens X} (S : (opensGT X).Cover U) (x : Meq (constPresheaf X A) S)
    (I₁ I₂ : S.Arrow) :
    x I₁ = x I₂ := by
  obtain ⟨R, rfl, rfl⟩ := cover_arrows_related S I₁ I₂
  simpa [constPresheaf] using x.condition R

private theorem toPlus_surjective_of_const
    {X : Type u} [TopologicalSpace X] {A : AddCommGrpCat.{u}}
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective
      (ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X A)).app (op U))) := by
  intro y; obtain ⟨S, x, hx⟩ := exists_rep y
  obtain ⟨I₀, hI₀⟩ := cover_nonempty_arrow U hU S
  refine ⟨x I₀, ?_⟩
  rw [hx, show x = Meq.mk S (x I₀) from Meq.ext _ _ fun I => meq_const_values_eq S x I I₀,
      toPlus_eq_mk, eq_mk_iff_exists]
  refine ⟨S, homOfLE le_top, 𝟙 S, ?_⟩
  apply Meq.ext; intro I
  simp [Meq.refine, Meq.mk, constPresheaf]

private lemma toPlus_naturality_const
    {X : Type u} [TopologicalSpace X] {A : AddCommGrpCat.{u}}
    {U V : Opens X} (i : U ⟶ V) (a : (constPresheaf X A).obj (op V)) :
    ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X A)).app (op U)) a =
      ConcreteCategory.hom (((opensGT X).plusObj (constPresheaf X A)).map i.op)
        (ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X A)).app (op V)) a) := by
  have nat := ((opensGT X).toPlus (constPresheaf X A)).naturality i.op
  calc ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X A)).app (op U)) a
      = ConcreteCategory.hom ((constPresheaf X A).map i.op ≫
          ((opensGT X).toPlus (constPresheaf X A)).app (op U)) a := by simp
    _ = ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X A)).app (op V) ≫
          ((opensGT X).plusObj (constPresheaf X A)).map i.op) a := by rw [nat]
    _ = _ := ConcreteCategory.comp_apply _ _ _

/-- Key lemma extracted from toPlus_surjective_of_firstPlus: preimages at different
    arrows agree because of irreducibility (intersection is nonempty). -/
private theorem toPlus_firstPlus_key
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X] {A : AddCommGrpCat.{u}}
    {U : Opens X} (S : (opensGT X).Cover U) (x : Meq ((opensGT X).plusObj (constPresheaf X A)) S)
    (I₀ : S.Arrow) (hI₀ : (I₀.Y : Set X).Nonempty)
    (a : (constPresheaf X A).obj (op U))
    (ha : ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X A)).app (op I₀.Y)) a = x I₀)
    (I : S.Arrow) (hI : (I.Y : Set X).Nonempty) :
    x I = ConcreteCategory.hom (((opensGT X).plusObj (constPresheaf X A)).map I.f.op)
      (ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X A)).app (op U)) a) := by
  obtain ⟨b, hb⟩ := toPlus_surjective_of_const I.Y hI (x I)
  have hZne : ((I₀.Y ⊓ I.Y : Opens X) : Set X).Nonempty :=
    nonempty_preirreducible_inter I₀.Y.isOpen I.Y.isOpen hI₀ hI
  let R : S.Relation := Cover.Relation.mk' (fst := I₀) (snd := I)
    ⟨I₀.Y ⊓ I.Y, homOfLE inf_le_left, homOfLE inf_le_right, Subsingleton.elim _ _⟩
  have hcond := x.condition R
  change ConcreteCategory.hom (((opensGT X).plusObj (constPresheaf X A)).map
      (homOfLE inf_le_left).op) (x I₀) =
    ConcreteCategory.hom (((opensGT X).plusObj (constPresheaf X A)).map
      (homOfLE inf_le_right).op) (x I) at hcond
  rw [← ha, ← hb] at hcond
  rw [← toPlus_naturality_const (homOfLE (inf_le_left (a := I₀.Y) (b := I.Y))) a,
      ← toPlus_naturality_const (homOfLE (inf_le_right (a := I₀.Y) (b := I.Y))) b] at hcond
  have hab : a = b := toPlus_injective_of_const _ hZne a b hcond
  rw [← hb, ← hab]
  exact toPlus_naturality_const I.f a

private theorem toPlus_surjective_of_firstPlus
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X] {A : AddCommGrpCat.{u}}
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ConcreteCategory.hom
      (((opensGT X).toPlus ((opensGT X).plusObj (constPresheaf X A))).app (op U))) := by
  intro y; obtain ⟨S, x, hx⟩ := exists_rep y
  obtain ⟨I₀, hI₀⟩ := cover_nonempty_arrow U hU S
  obtain ⟨a, ha⟩ := toPlus_surjective_of_const I₀.Y hI₀ (x I₀)
  use ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X A)).app (op U)) a
  rw [hx, toPlus_eq_mk, eq_mk_iff_exists]
  refine ⟨S, homOfLE le_top, 𝟙 S, ?_⟩
  apply Meq.ext; intro I
  simp only [Meq.refine, Meq.mk]
  by_cases hI : (I.Y : Set X).Nonempty
  · exact (toPlus_firstPlus_key S x I₀ hI₀ a ha I hI).symm
  · rw [Set.not_nonempty_iff_eq_empty] at hI
    have hIbot : I.Y = ⊥ := Opens.ext (by simpa using hI)
    exact @Subsingleton.elim _ (hIbot ▸ plusObj_bot_subsingleton _) _ _

private theorem sheafify_constPresheaf_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X] {A : AddCommGrpCat.{u}}
    {U V : Opens X} (i : U ⟶ V) :
    Epi (((opensGT X).sheafify (constPresheaf X A)).map i.op) := by
  by_cases hU : (U : Set X) = ∅
  · have : U = ⊥ := Opens.ext (by simpa using hU)
    subst this
    rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    haveI : Subsingleton (ToType (((opensGT X).sheafify (constPresheaf X A)).obj (op ⊥))) := by
      simpa [GrothendieckTopology.toSheafify] using
        plusObj_bot_subsingleton (X := X) (P := (opensGT X).plusObj (constPresheaf X A))
    exact ⟨0, Subsingleton.elim _ _⟩
  · have hUne : (U : Set X).Nonempty := Set.nonempty_iff_ne_empty.mpr hU
    have hnat := ((opensGT X).toSheafify (constPresheaf X A)).naturality i.op
    rw [show (constPresheaf X A).map i.op = 𝟙 _ from by ext; simp [constPresheaf],
        Category.id_comp] at hnat
    have hfac : ((opensGT X).toSheafify (constPresheaf X A)).app (op V) ≫
        ((opensGT X).sheafify (constPresheaf X A)).map i.op =
        ((opensGT X).toSheafify (constPresheaf X A)).app (op U) := hnat.symm
    haveI : Epi (((opensGT X).toSheafify (constPresheaf X A)).app (op U)) := by
      apply ConcreteCategory.epi_of_surjective
      rw [show ((opensGT X).toSheafify (constPresheaf X A)).app (op U) =
          ((opensGT X).toPlus (constPresheaf X A)).app (op U) ≫
          ((opensGT X).toPlus ((opensGT X).plusObj (constPresheaf X A))).app (op U) from by
        simp only [GrothendieckTopology.toSheafify, (opensGT X).plusMap_toPlus, NatTrans.comp_app]]
      intro y; obtain ⟨z, hz⟩ := toPlus_surjective_of_firstPlus (X := X) U hUne y
      obtain ⟨a, ha⟩ := toPlus_surjective_of_const (X := X) U hUne z
      exact ⟨a, by rw [ConcreteCategory.comp_apply, ha]; exact hz⟩
    exact epi_of_epi_fac hfac

private theorem presheafToSheaf_constPresheaf_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X] {A : AddCommGrpCat.{u}}
    {U V : Opens X} (i : U ⟶ V) :
    Epi (((presheafToSheaf (opensGT X) AddCommGrpCat.{u}).obj (constPresheaf X A)).val.map i.op) := by
  let e := plusPlusIsoSheafify (J := opensGT X) (D := AddCommGrpCat.{u}) (P := constPresheaf X A)
  haveI := sheafify_constPresheaf_flasque_of_irreducible (X := X) (A := A) (i := i)
  haveI : Epi (e.hom.app (op V) ≫
      (CategoryTheory.sheafify (opensGT X) (constPresheaf X A)).map i.op) := by
    rw [← e.hom.naturality i.op]; infer_instance
  exact epi_of_epi (e.hom.app (op V))
    ((CategoryTheory.sheafify (opensGT X) (constPresheaf X A)).map i.op)

theorem constantSheaf_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X]
    (A : AddCommGrpCat.{u})
    {U V : Opens X} (i : U ⟶ V) :
    Epi (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      A).val.map i.op) := by
  simpa [CategoryTheory.constantSheaf, constPresheaf] using
    (presheafToSheaf_constPresheaf_flasque_of_irreducible (X := X) (i := i))
