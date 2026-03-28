import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits Opposite GrothendieckTopology.Plus

set_option maxHeartbeats 800000

variable {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]

private abbrev P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))

private abbrev J' : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X

/-- For the constant presheaf, `P.map f` acts as the identity. -/
lemma constPresheaf_map_eq_id {U V : Opens X} (f : U ⟶ V) (a : ULift.{u} ℤ) :
    (ConcreteCategory.hom ((P (X := X)).map f.op)) a = a := by
  simp [P]

/-- For any two arrows in a cover of a nonempty open in an irreducible space,
there exists a relation connecting them. -/
lemma cover_arrows_related
    (U : Opens X) (hU : (U : Set X).Nonempty)
    (S : (J' (X := X)).Cover U) (I₁ I₂ : S.Arrow) :
    ∃ R : S.Relation, R.fst = I₁ ∧ R.snd = I₂ := by
  by_contra h_no_relation
  simp +zetaDelta at *
  refine' h_no_relation ⟨ _, _, _, _ ⟩ rfl rfl
  exact I₁.Y ⊓ I₂.Y
  exact homOfLE inf_le_left
  exact homOfLE inf_le_right
  exact Subsingleton.elim _ _

/-- All values of a matching family for the constant presheaf on an irreducible space are equal. -/
lemma meq_const_values_eq
    (U : Opens X) (hU : (U : Set X).Nonempty)
    (S : (J' (X := X)).Cover U) (x : Meq (P (X := X)) S)
    (I₁ I₂ : S.Arrow) : x.1 I₁ = x.1 I₂ := by
  obtain ⟨R, hR₁, hR₂⟩ := cover_arrows_related U hU S I₁ I₂
  have h_eq : P.map R.r.g₁.op (x R.fst) = P.map R.r.g₂.op (x R.snd) := x.2 R
  aesop

/-- A cover of a nonempty open has an arrow. -/
lemma cover_nonempty_arrow
    (U : Opens X) (hU : (U : Set X).Nonempty)
    (S : (J' (X := X)).Cover U) : Nonempty S.Arrow := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨S, hS⟩ := S
  obtain ⟨V, hV⟩ := hS x hx
  exact ⟨⟨V, hV.choose, hV.choose_spec.1⟩⟩

/-- A matching family whose values are all equal to `a` equals `Meq.mk S a`. -/
lemma meq_eq_mk_of_values_eq
    (U : Opens X) (S : (J' (X := X)).Cover U) (x : Meq (P (X := X)) S)
    (a : (P (X := X)).obj (op U)) (ha : ∀ I : S.Arrow, x.1 I = a) :
    x = Meq.mk S a := by
  ext I; exact ha I

/-- `Meq.mk` refined along any morphism equals `Meq.mk` for the constant presheaf. -/
lemma meq_mk_refine_eq
    (U : Opens X) (S T : (J' (X := X)).Cover U) (e : S ⟶ T)
    (a : (P (X := X)).obj (op U)) :
    (Meq.mk T a).refine e = Meq.mk S a := by
  ext; aesop

/-- On an irreducible space, the toPlus map for the constant presheaf is surjective
    at nonempty opens. -/
theorem toPlus_surjective_of_irreducible_const
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ConcreteCategory.hom
      ((Opens.grothendieckTopology X).toPlus
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
        |>.app (Opposite.op U))) := by
  intro y
  obtain ⟨S, x, hx⟩ := exists_rep y
  have hne := cover_nonempty_arrow U hU S
  let I₀ := hne.some
  let a := x.1 I₀
  have ha : ∀ I : S.Arrow, x.1 I = a := fun I => meq_const_values_eq U hU S x I I₀
  have hx_eq : x = Meq.mk S a := meq_eq_mk_of_values_eq U S x a ha
  use a
  rw [hx, hx_eq, toPlus_eq_mk, eq_mk_iff_exists]
  refine ⟨S, homOfLE le_top, 𝟙 S, ?_⟩
  rw [meq_mk_refine_eq]
  apply Meq.ext
  intro I
  simp [Meq.refine, Meq.mk]
