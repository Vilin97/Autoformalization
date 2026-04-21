import Aristotle.GrothendieckVanishing.main.CohomologyAPI

/-!
# FlasqueCohomology — Cohomological vanishing for flasque sheaves

Provides:
* `FlasqueVanishing`: flasque sheaves have vanishing higher cohomology

General sheaf-cohomology API lives in `CohomologyAPI.lean`.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-- Presheaf-boundary form of `FlasqueVanishing`. -/
theorem sheafH_subsingleton_of_flasque_presheaf
    (X : TopCat.{u}) {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    [IsFlasqueSheaf (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)]
    (n : ℕ) :
    Subsingleton (Sheaf.H (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) (n + 1)) := by
  induction n generalizing F with
  | zero =>
      exact sheafH_subsingleton_H1_of_flasque_presheaf (F := F) hF
  | succ n ih =>
      let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
      obtain ⟨ip⟩ := EnoughInjectives.presentation Fsh
      let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ip.shortComplex
      letI : Injective ((⟨S.X₂.val, S.X₂.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
        simpa [S] using (inferInstance : Injective S.X₂)
      letI : IsFlasqueSheaf ((⟨S.X₃.val, S.X₃.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
        simpa [S] using
          (isFlasque_X₃_of_shortExact_presheaf
            S.X₁.cond S.X₂.cond S.X₃.cond
            (f := S.f.val) (g := S.g.val)
            (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
            (by simpa [S] using ip.shortExact_shortComplex))
      have h₃H : Subsingleton (Sheaf.H
          ((⟨S.X₃.val, S.X₃.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1)) := by
        simpa using (ih (F := S.X₃.val) S.X₃.cond)
      simpa [Fsh, S] using
        (sheafH_dimension_shift_presheaf
          (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
          S.X₁.cond S.X₂.cond S.X₃.cond
          (f := S.f.val) (g := S.g.val)
          (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
          (by simpa [S] using ip.shortExact_shortComplex)
          (n + 1) h₃H)

/-- **Flasque sheaves have vanishing higher cohomology** (Nugent, PR #35790). -/
instance FlasqueVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [IsFlasqueSheaf F]
    (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F.val, F.cond⟩
  letI : IsFlasqueSheaf Fsh := by
    simpa [Fsh] using (inferInstance : IsFlasqueSheaf F)
  simpa [Fsh] using
    (sheafH_subsingleton_of_flasque_presheaf (X := X) (F := F.val) F.cond n)
