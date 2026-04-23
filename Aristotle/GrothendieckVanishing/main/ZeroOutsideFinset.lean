import Aristotle.GrothendieckVanishing.main.GeneratedSubsheaf
import Aristotle.GrothendieckVanishing.main.ZeroOutside

/-!
  ZeroOutsideFinset.lean — finite transition maps between generated subsheaves

  Contains:
  - `finsetCoproductInclGen`
  - `finsetImageInclGen`, `finsetImageInclGen_comp_ι`, `finsetImageInclGen_mono`
-/

universe u

open CategoryTheory TopologicalSpace Limits Opposite

noncomputable section

namespace TopCat

namespace Presheaf

/-- Coproduct inclusion induced by `S ⊆ S'` on the finite generator coproducts. -/
noncomputable def finsetCoproductInclGen {X : TopCat.{u}}
    {F : TopCat.Presheaf AddCommGrpCat.{u} X}
    {S S' : Finset (SectionIndex F)}
    (h : S ⊆ S') :
    (∐ fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟶
      (∐ fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) :=
  Sigma.desc fun σ =>
    Sigma.ι (fun τ : {τ // τ ∈ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ.1, h σ.2⟩

/-- Inclusion of finitely generated subsheaves induced by `S ⊆ S'`. -/
noncomputable def finsetImageInclGen {X : TopCat.{u}}
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    {S S' : Finset (SectionIndex F)}
    (h : S ⊆ S') :
    TopCat.Presheaf.finsetGeneratedSheaf hF S ⟶ TopCat.Presheaf.finsetGeneratedSheaf hF S' :=
  Limits.image.lift
    { I := TopCat.Presheaf.finsetGeneratedSheaf hF S'
      m := Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hF S')
      e := finsetCoproductInclGen h ≫
        factorThruImage (TopCat.Presheaf.finsetGeneratorMap hF S')
      fac := by
        rw [Category.assoc, Limits.image.fac]
        ext ⟨σ, hσ⟩
        simp [finsetCoproductInclGen, TopCat.Presheaf.finsetGeneratorMap,
          TopCat.Sheaf.familyMap] }

theorem finsetImageInclGen_comp_ι {X : TopCat.{u}}
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    {S S' : Finset (SectionIndex F)}
    (h : S ⊆ S') :
    finsetImageInclGen hF h ≫
        Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hF S') =
      Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hF S) := by
  simpa [finsetImageInclGen] using
    (Limits.image.lift_fac (f := TopCat.Presheaf.finsetGeneratorMap hF S)
      { I := TopCat.Presheaf.finsetGeneratedSheaf hF S'
        m := Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hF S')
        e := finsetCoproductInclGen h ≫
          factorThruImage (TopCat.Presheaf.finsetGeneratorMap hF S')
        fac := by
          rw [Category.assoc, Limits.image.fac]
          ext ⟨σ, hσ⟩
          simp [finsetCoproductInclGen, TopCat.Presheaf.finsetGeneratorMap,
            TopCat.Sheaf.familyMap] })

instance finsetImageInclGen_mono {X : TopCat.{u}}
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    {S S' : Finset (SectionIndex F)}
    (h : S ⊆ S') :
    Mono (finsetImageInclGen hF h) :=
  mono_of_mono_fac (finsetImageInclGen_comp_ι hF h)

end Presheaf

end TopCat
