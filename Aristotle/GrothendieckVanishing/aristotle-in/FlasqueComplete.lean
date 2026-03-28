import Mathlib

-- Harmonic `generalize_proofs` tactic

universe u

open CategoryTheory TopologicalSpace Limits Opposite GrothendieckTopology GrothendieckTopology.Plus

set_option maxHeartbeats 1600000

variable {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]

private abbrev P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))

private abbrev J : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X

/-- All arrows in a cover of a nonempty open are related.
    Uses: for any Z, g₁ : Z → I₁.Y, g₂ : Z → I₂.Y exist (Z = I₁.Y ⊓ I₂.Y or Z = ⊥),
    and g₁ ≫ I₁.f = g₂ ≫ I₂.f by Subsingleton.elim.
    PROVED by Aristotle (17b9bce9). -/
lemma cover_arrows_related_local
    (U : Opens X) (hU : (U : Set X).Nonempty)
    (S : (J (X := X)).Cover U) (I₁ I₂ : S.Arrow) :
    ∃ R : S.Relation, R.fst = I₁ ∧ R.snd = I₂ := by
  by_contra h_no_relation
  simp +zetaDelta at *
  exact h_no_relation ⟨_, _, _, _⟩ rfl rfl
  exact I₁.Y ⊓ I₂.Y
  exact homOfLE inf_le_left
  exact homOfLE inf_le_right
  exact Subsingleton.elim _ _

/-- Matching families for the constant presheaf are constant at ALL arrows. -/
lemma meq_const_values_eq_local
    (U : Opens X) (hU : (U : Set X).Nonempty)
    (S : (J (X := X)).Cover U) (x : Meq (P (X := X)) S)
    (I₁ I₂ : S.Arrow) : x.1 I₁ = x.1 I₂ := by
  obtain ⟨R, hR₁, hR₂⟩ := cover_arrows_related_local U hU S I₁ I₂
  have := x.2 R; aesop

/-- toPlus is surjective for the constant presheaf at nonempty opens. -/
lemma toPlus_surjective_local
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ConcreteCategory.hom
      ((J (X := X)).toPlus (P (X := X)) |>.app (op U))) := by
  intro y
  obtain ⟨S, x, hx⟩ := exists_rep y
  obtain ⟨p, hp⟩ := hU
  obtain ⟨V, f, hf, _⟩ := S.2 p hp
  let I₀ : S.Arrow := ⟨V, f, hf⟩
  let a := x.1 I₀
  have ha : ∀ I : S.Arrow, x.1 I = a := fun I => meq_const_values_eq_local U hU S x I I₀
  have hx_eq : x = Meq.mk S a := by ext I; exact ha I
  exact ⟨a, by rw [hx, hx_eq, toPlus_eq_mk, eq_mk_iff_exists]; exact ⟨S, homOfLE le_top, 𝟙 S, by
    apply Meq.ext; intro I; simp [Meq.refine, Meq.mk]⟩⟩

/-- toPlus is injective for the constant presheaf at nonempty opens. -/
lemma toPlus_injective_local
    (U : Opens X) (hU : (U : Set X).Nonempty) (a b : (P (X := X)).obj (op U))
    (h : ConcreteCategory.hom ((J (X := X)).toPlus (P (X := X)) |>.app (op U)) a =
      ConcreteCategory.hom ((J (X := X)).toPlus (P (X := X)) |>.app (op U)) b) :
    a = b := by
  rw [toPlus_eq_mk, toPlus_eq_mk] at h
  rw [eq_mk_iff_exists] at h
  obtain ⟨W, _, _, heq⟩ := h
  obtain ⟨p, hp⟩ := hU
  obtain ⟨V, f, hf, _⟩ := W.2 p hp
  have := congr_fun (congr_arg Subtype.val heq) (⟨V, f, hf⟩ : W.Arrow)
  simp only [Functor.const_obj_obj, Meq.refine, Meq.mk] at this
  exact this

/-- The key naturality equation: toPlus commutes with restrictions of the const presheaf.
    toPlus_U(a) = plusObj(P).map i.op (toPlus_V(a)) -/
lemma toPlus_naturality_const {U V : Opens X} (i : U ⟶ V) (a : (P (X := X)).obj (op V)) :
    ConcreteCategory.hom ((J (X := X)).toPlus (P (X := X)) |>.app (op U)) a =
    ConcreteCategory.hom ((J (X := X)).plusObj (P (X := X))).map i.op
      (ConcreteCategory.hom ((J (X := X)).toPlus (P (X := X)) |>.app (op V)) a) := by
  have nat := ((J (X := X)).toPlus (P (X := X))).naturality i.op
  -- nat : P.map i.op ≫ toPlus.app (op U) = toPlus.app (op V) ≫ plusObj(P).map i.op
  -- For const P: P.map i.op = 𝟙
  -- So: toPlus.app (op U) = toPlus.app (op V) ≫ plusObj(P).map i.op
  -- Evaluating at a: toPlus_U(a) = plusObj(P).map i.op (toPlus_V(a))
  have := congr_fun (congr_arg ConcreteCategory.hom nat) a
  simp at this
  exact this.symm

/-- Matching families for plusObj(P) are constant at nonempty opens on irreducible X.
    Uses bijectivity of toPlus + naturality. -/
lemma meq_plusObj_const_values_eq
    (U : Opens X) (hU : (U : Set X).Nonempty)
    (S : (J (X := X)).Cover U)
    (x : Meq ((J (X := X)).plusObj (P (X := X))) S)
    (I₁ I₂ : S.Arrow) : x.1 I₁ = x.1 I₂ := by
  sorry

/-- toPlus is surjective for plusObj(P) at nonempty opens. -/
lemma toPlus_plusObj_surjective_local
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ConcreteCategory.hom
      ((J (X := X)).toPlus ((J (X := X)).plusObj (P (X := X))) |>.app (op U))) := by
  sorry

/-- toSheafify is surjective at nonempty opens for the constant presheaf on irreducible X. -/
lemma toSheafify_surjective_local
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ConcreteCategory.hom
      ((J (X := X)).toSheafify (P (X := X)) |>.app (op U))) := by
  -- toSheafify = toPlus ≫ plusMap(toPlus) = toPlus ≫ toPlus(plusObj P)
  rw [GrothendieckTopology.toSheafify]
  intro y
  -- Factor: first apply toPlus(plusObj P), then toPlus
  rw [show (J.toPlus (P (X := X)) ≫ J.plusMap (J.toPlus (P (X := X)))).app (op U) =
    (J.toPlus (P (X := X))).app (op U) ≫ (J.plusMap (J.toPlus (P (X := X)))).app (op U) from rfl]
  rw [J.plusMap_toPlus] at *
  -- Now: (toPlus ≫ toPlus(plusObj P)).app (op U) = toPlus_U ≫ toPlus(plusObj P)_U
  simp only [NatTrans.comp_app] at *
  -- y ∈ sheafify(P)(U) = plusObj(plusObj P)(U)
  -- By surjectivity of toPlus(plusObj P): y = toPlus(plusObj P)(z) for some z ∈ plusObj(P)(U)
  obtain ⟨z, hz⟩ := toPlus_plusObj_surjective_local U hU y
  -- By surjectivity of toPlus: z = toPlus(a) for some a ∈ P(U)
  obtain ⟨a, ha⟩ := toPlus_surjective_local U hU z
  exact ⟨a, by rw [ConcreteCategory.comp_apply, ha, hz]⟩
