/-
  ConstantSheafFlasque.lean — The constant sheaf on an irreducible space is flasque
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.Auxiliary

universe u

open CategoryTheory TopologicalSpace Limits Opposite GrothendieckTopology GrothendieckTopology.Plus

private abbrev constPresheaf (X : Type u) [TopologicalSpace X] :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))

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
    {X : Type u} [TopologicalSpace X]
    (U : Opens X) (hU : (U : Set X).Nonempty)
    (a b : (constPresheaf X).obj (op U))
    (h : ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X)).app (op U)) a =
      ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X)).app (op U)) b) :
    a = b := by
  rw [toPlus_eq_mk, toPlus_eq_mk] at h
  rw [eq_mk_iff_exists] at h
  obtain ⟨W, _, _, heq⟩ := h
  obtain ⟨p, hp⟩ := hU
  obtain ⟨V, f, hf, _⟩ := W.2 p hp
  have := congr_fun (congr_arg Subtype.val heq) (⟨V, f, hf⟩ : W.Arrow)
  simp only [Functor.const_obj_obj, Meq.refine, Meq.mk] at this
  exact this

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
    {X : Type u} [TopologicalSpace X]
    {U : Opens X} (S : (opensGT X).Cover U) (x : Meq (constPresheaf X) S)
    (I₁ I₂ : S.Arrow) :
    x I₁ = x I₂ := by
  obtain ⟨R, rfl, rfl⟩ := cover_arrows_related S I₁ I₂
  simpa [constPresheaf] using x.condition R

private theorem toPlus_surjective_of_const
    {X : Type u} [TopologicalSpace X]
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective
      (ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X)).app (op U))) := by
  intro y
  obtain ⟨S, x, hx⟩ := exists_rep y
  obtain ⟨I₀, hI₀⟩ := cover_nonempty_arrow U hU S
  let a : (constPresheaf X).obj (op U) := x I₀
  have ha : ∀ I : S.Arrow, x I = a := fun I => meq_const_values_eq S x I I₀
  have hx_eq : x = Meq.mk S a := by ext I; exact ha I
  refine ⟨a, ?_⟩
  rw [hx, hx_eq, toPlus_eq_mk, eq_mk_iff_exists]
  refine ⟨S, homOfLE le_top, 𝟙 S, ?_⟩
  apply Meq.ext; intro I
  simp [Meq.refine, Meq.mk, constPresheaf]

private lemma toPlus_naturality_const
    {X : Type u} [TopologicalSpace X]
    {U V : Opens X} (i : U ⟶ V) (a : (constPresheaf X).obj (op V)) :
    ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X)).app (op U)) a =
      ConcreteCategory.hom (((opensGT X).plusObj (constPresheaf X)).map i.op)
        (ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X)).app (op V)) a) := by
  have nat := ((opensGT X).toPlus (constPresheaf X)).naturality i.op
  calc ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X)).app (op U)) a
      = ConcreteCategory.hom ((constPresheaf X).map i.op ≫
          ((opensGT X).toPlus (constPresheaf X)).app (op U)) a := by simp
    _ = ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X)).app (op V) ≫
          ((opensGT X).plusObj (constPresheaf X)).map i.op) a := by rw [nat]
    _ = _ := ConcreteCategory.comp_apply _ _ _

-- Plus construction API requires extra heartbeats for typeclass resolution
/-- Key lemma extracted from toPlus_surjective_of_firstPlus: preimages at different
    arrows agree because of irreducibility (intersection is nonempty). -/
private theorem toPlus_firstPlus_key
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    {U : Opens X} (S : (opensGT X).Cover U) (x : Meq ((opensGT X).plusObj (constPresheaf X)) S)
    (I₀ : S.Arrow) (hI₀ : (I₀.Y : Set X).Nonempty)
    (a : (constPresheaf X).obj (op U))
    (ha : ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X)).app (op I₀.Y)) a = x I₀)
    (I : S.Arrow) (hI : (I.Y : Set X).Nonempty) :
    x I = ConcreteCategory.hom (((opensGT X).plusObj (constPresheaf X)).map I.f.op)
      (ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X)).app (op U)) a) := by
  obtain ⟨b, hb⟩ := toPlus_surjective_of_const I.Y hI (x I)
  have hZne : ((I₀.Y ⊓ I.Y : Opens X) : Set X).Nonempty :=
    nonempty_preirreducible_inter I₀.Y.isOpen I.Y.isOpen hI₀ hI
  let R : S.Relation := Cover.Relation.mk' (fst := I₀) (snd := I)
    ⟨I₀.Y ⊓ I.Y, homOfLE inf_le_left, homOfLE inf_le_right, Subsingleton.elim _ _⟩
  have hcond := x.condition R
  change ConcreteCategory.hom (((opensGT X).plusObj (constPresheaf X)).map
      (homOfLE inf_le_left).op) (x I₀) =
    ConcreteCategory.hom (((opensGT X).plusObj (constPresheaf X)).map
      (homOfLE inf_le_right).op) (x I) at hcond
  rw [← ha, ← hb] at hcond
  rw [← toPlus_naturality_const (homOfLE (inf_le_left (a := I₀.Y) (b := I.Y))) a,
      ← toPlus_naturality_const (homOfLE (inf_le_right (a := I₀.Y) (b := I.Y))) b] at hcond
  have hab : a = b := toPlus_injective_of_const _ hZne a b hcond
  rw [← hb, ← hab]
  exact toPlus_naturality_const I.f a

-- Plus construction API requires extra heartbeats for typeclass resolution
private theorem toPlus_surjective_of_firstPlus
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ConcreteCategory.hom
      (((opensGT X).toPlus ((opensGT X).plusObj (constPresheaf X))).app (op U))) := by
  intro y
  obtain ⟨S, x, hx⟩ := exists_rep y
  obtain ⟨I₀, hI₀⟩ := cover_nonempty_arrow U hU S
  obtain ⟨a, ha⟩ := toPlus_surjective_of_const I₀.Y hI₀ (x I₀)
  use ConcreteCategory.hom (((opensGT X).toPlus (constPresheaf X)).app (op U)) a
  rw [hx, toPlus_eq_mk, eq_mk_iff_exists]
  refine ⟨S, homOfLE le_top, 𝟙 S, ?_⟩
  apply Meq.ext; intro I
  simp only [Meq.refine, Meq.mk]
  by_cases hI : (I.Y : Set X).Nonempty
  · exact (toPlus_firstPlus_key S x I₀ hI₀ a ha I hI).symm
  · rw [Set.not_nonempty_iff_eq_empty] at hI
    have hIbot : I.Y = ⊥ := Opens.ext (by simpa using hI)
    have hsub : Subsingleton (ToType (((opensGT X).plusObj (constPresheaf X)).obj (op I.Y))) := by
      rw [hIbot]; exact plusObj_bot_subsingleton _
    exact @Subsingleton.elim _ hsub _ _

private theorem sheafify_constPresheaf_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X]
    {U V : Opens X} (i : U ⟶ V) :
    Epi (((opensGT X).sheafify (constPresheaf X)).map i.op) := by
  by_cases hU : (U : Set X) = ∅
  · have : U = ⊥ := Opens.ext (by simpa using hU)
    subst this
    rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    refine ⟨0, ?_⟩
    have hsub : Subsingleton
        (ToType (((opensGT X).sheafify (constPresheaf X)).obj (op ⊥))) := by
      simpa [GrothendieckTopology.toSheafify] using
        (plusObj_bot_subsingleton (X := X)
          (P := (opensGT X).plusObj (constPresheaf X)))
    exact @Subsingleton.elim _ hsub _ _
  · have hUne : (U : Set X).Nonempty := Set.nonempty_iff_ne_empty.mpr hU
    have hnat := ((opensGT X).toSheafify (constPresheaf X)).naturality i.op
    have hid : (constPresheaf X).map i.op = 𝟙 _ := by
      ext a
      simp [constPresheaf]
    rw [hid, Category.id_comp] at hnat
    have hfac : ((opensGT X).toSheafify (constPresheaf X)).app (op V) ≫
        ((opensGT X).sheafify (constPresheaf X)).map i.op =
        ((opensGT X).toSheafify (constPresheaf X)).app (op U) := hnat.symm
    haveI : Epi (((opensGT X).toSheafify (constPresheaf X)).app (op U)) := by
      apply ConcreteCategory.epi_of_surjective
      have hfact : ((opensGT X).toSheafify (constPresheaf X)).app (op U) =
          ((opensGT X).toPlus (constPresheaf X)).app (op U) ≫
          ((opensGT X).toPlus ((opensGT X).plusObj (constPresheaf X))).app (op U) := by
        simp only [GrothendieckTopology.toSheafify, (opensGT X).plusMap_toPlus,
          NatTrans.comp_app]
      rw [hfact]
      intro y
      obtain ⟨z, hz⟩ := toPlus_surjective_of_firstPlus (X := X) U hUne y
      obtain ⟨a, ha⟩ := toPlus_surjective_of_const (X := X) U hUne z
      refine ⟨a, ?_⟩
      rw [ConcreteCategory.comp_apply, ha]
      exact hz
    exact epi_of_epi_fac hfac

private theorem presheafToSheaf_constPresheaf_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X]
    {U V : Opens X} (i : U ⟶ V) :
    Epi (((presheafToSheaf (opensGT X) AddCommGrpCat.{u}).obj (constPresheaf X)).val.map i.op) := by
  let e := plusPlusIsoSheafify (J := opensGT X) (D := AddCommGrpCat.{u}) (P := constPresheaf X)
  haveI := sheafify_constPresheaf_flasque_of_irreducible (X := X) (i := i)
  haveI : Epi (e.hom.app (op V) ≫
      (CategoryTheory.sheafify (opensGT X) (constPresheaf X)).map i.op) := by
    rw [← e.hom.naturality i.op]; infer_instance
  exact epi_of_epi (e.hom.app (op V))
    ((CategoryTheory.sheafify (opensGT X) (constPresheaf X)).map i.op)

theorem constantSheaf_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X]
    {U V : Opens X} (i : U ⟶ V) :
    Epi (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))).val.map i.op) := by
  simpa [CategoryTheory.constantSheaf, constPresheaf] using
    (presheafToSheaf_constPresheaf_flasque_of_irreducible (X := X) (i := i))
