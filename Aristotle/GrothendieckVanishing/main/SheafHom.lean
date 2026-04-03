/-
  SheafHom.lean — Hom(Z_X, -) preserves filtered colimit vanishing for sheaves

  For sheaves on a Noetherian space, the constant sheaf Z_X = ΔZ has the property that
  Hom(Z_X, F) ≅ F(⊤) via constantSheafAdj. Since filtered colimits of sheaves are
  computed objectwise, Hom(Z_X, -) preserves filtered-colimit vanishing universally.
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.ConstantSheafFlasque

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-! ### Helper lemmas: Subsingleton transfer for AddCommGrpCat -/

/-- In `AddCommGrpCat`, `Subsingleton (ULift ℤ ⟶ G)` implies `Subsingleton G`. -/
theorem addCommGrpCat_subsingleton_of_subsingleton_hom
    (G : AddCommGrpCat.{u})
    (h : Subsingleton (AddCommGrpCat.of (ULift.{u} ℤ) ⟶ G)) :
    Subsingleton G := by
  constructor; intro a b
  let fa : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ G := AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun z => ULift.down z • a) (fun x y => by simp [add_smul]))
  let fb : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ G := AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun z => ULift.down z • b) (fun x y => by simp [add_smul]))
  have heq := @Subsingleton.elim _ h fa fb
  have := AddCommGrpCat.ext_iff.mp heq (⟨1⟩ : ULift.{u} ℤ)
  simpa [fa, fb] using this

/-- In `AddCommGrpCat`, `Subsingleton G` implies `Subsingleton (ULift ℤ ⟶ G)`. -/
theorem addCommGrpCat_subsingleton_hom_of_subsingleton
    (G : AddCommGrpCat.{u})
    (h : Subsingleton G) :
    Subsingleton (AddCommGrpCat.of (ULift.{u} ℤ) ⟶ G) := by
  constructor; intro f g; ext x; exact @Subsingleton.elim _ h _ _

/-! ### Filtered colimit of subsingleton Ab groups is subsingleton -/

/-- A filtered colimit of subsingleton `AddCommGrpCat` objects is subsingleton. -/
theorem addCommGrpCat_colimit_subsingleton_of_pieces
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (F : J' ⥤ AddCommGrpCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hvan : ∀ j, Subsingleton (F.obj j)) : Subsingleton c.pt := by
  have hzero : ∀ j, c.ι.app j = 0 := by
    intro j; ext x; simp [@Subsingleton.elim _ (hvan j) x 0]
  have hid : 𝟙 c.pt = 0 := hc.hom_ext (fun j => by simp [hzero j])
  constructor; intro a b
  have ha : a = 0 := by have := congrArg (·.hom a) hid; simpa using this
  have hb : b = 0 := by have := congrArg (·.hom b) hid; simpa using this
  rw [ha, hb]

/-- Filtered presheaf colimits of sheaves are sheaves on a Noetherian space.
    This is the AB5 property: filtered colimits commute with the finite limits
    that appear in the sheaf condition (Noetherian ⟹ finite covers suffice). -/
private theorem isSheaf_filtered_colimit_of_sheaves
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c : Cocone (Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (_ : IsColimit c) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) c.pt := by
  sorry

/-- Filtered colimit of sheaves with subsingleton global sections has subsingleton
    global sections. Uses `createsColimitOfIsSheaf` + evaluation. -/
theorem sheaf_colimit_sections_subsingleton
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) (c' : Cocone Y') (hc' : IsColimit c')
    (hvan : ∀ j, Subsingleton ((Y'.obj j).val.obj (op ⊤))) :
    Subsingleton (c'.pt.val.obj (op ⊤)) := by
  -- sheafToPresheaf creates this colimit (via AB5: presheaf colimit of sheaves is a sheaf)
  haveI : CreatesColimit Y' (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    Sheaf.createsColimitOfIsSheaf Y' (isSheaf_filtered_colimit_of_sheaves Y')
  -- sheafToPresheaf preserves this colimit (CreatesColimit + HasColimit → PreservesColimit)
  have hcPsh : IsColimit ((sheafToPresheaf _ _).mapCocone c') :=
    isColimitOfPreserves _ hc'
  -- evaluation at op ⊤ preserves all colimits
  have hcAb : IsColimit (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op ⊤)).mapCocone
      ((sheafToPresheaf _ _).mapCocone c')) :=
    isColimitOfPreserves _ hcPsh
  exact addCommGrpCat_colimit_subsingleton_of_pieces _ _ hcAb hvan

/-- For sheaves on a Noetherian space, `Hom(Z_X, -)` preserves filtered-colimit vanishing
    universally, where `Z_X` is the constant sheaf on `ULift ℤ`. -/
theorem constantSheaf_hom_preserves_filtered_colimit_vanishing
    {X : TopCat.{u}} [NoetherianSpace X] :
    let Z := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))
    ∀ {J' : Type u} [SmallCategory J'] [IsFiltered J']
      (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) (c' : Cocone Y'), IsColimit c' →
      (∀ j, Subsingleton (Z ⟶ Y'.obj j)) → Subsingleton (Z ⟶ c'.pt) := by
  intro Z J' _ _ Y' c' hc' hvan
  have adj := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    Limits.isTerminalTop
  have heq : ∀ F : TopCat.Sheaf AddCommGrpCat.{u} X,
      (Z ⟶ F) ≃ (AddCommGrpCat.of (ULift.{u} ℤ) ⟶
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op ⊤)).obj F) :=
    fun F => adj.homEquiv _ F
  apply (heq c'.pt).subsingleton_congr.mpr
  have hvan' : ∀ j, Subsingleton ((Y'.obj j).val.obj (op ⊤)) := by
    intro j
    exact addCommGrpCat_subsingleton_of_subsingleton_hom _
      ((heq _).subsingleton_congr.mp (hvan j))
  apply addCommGrpCat_subsingleton_hom_of_subsingleton
  exact sheaf_colimit_sections_subsingleton Y' c' hc' hvan'
