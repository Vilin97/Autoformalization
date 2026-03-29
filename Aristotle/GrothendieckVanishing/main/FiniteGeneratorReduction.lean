import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.ZeroOutside

universe u

open CategoryTheory Limits Opposite TopologicalSpace Abelian

noncomputable section

namespace TopCat
namespace Sheaf

/-- In a short exact sequence of sheaves of abelian groups, if the outer cohomology groups in
degree `n` are subsingletons, then the middle cohomology group in degree `n` is also a
subsingleton. This is the covariant Ext long exact sequence in degree `n`. -/
theorem subsingleton_sheafH_of_shortExact_middle
    {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₁ : Subsingleton (Sheaf.H S.X₁ n))
    (h₃ : Subsingleton (Sheaf.H S.X₃ n)) :
    Subsingleton (Sheaf.H S.X₂ n) := by
  let Z := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))
  constructor
  intro a b
  have ha : a.comp (Ext.mk₀ S.g) (add_zero n) = 0 := @Subsingleton.elim _ h₃ _ _
  have hb : b.comp (Ext.mk₀ S.g) (add_zero n) = 0 := @Subsingleton.elim _ h₃ _ _
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₂ Z hS a ha
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₂ Z hS b hb
  rw [← hc, ← hd, @Subsingleton.elim _ h₁ c d]

/-- Hartshorne Step 3B, cohomological form: adjoining one generator preserves vanishing in a
fixed degree once vanishing is known for the previously generated subsheaf and for the quotient. -/
theorem subsingleton_of_adjoinGenerator
    {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (n : ℕ)
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    (U₀ : Opens X) (s₀ : F.presheaf.obj (op U₀))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)]
    (hold : Subsingleton (Sheaf.H (familyGeneratedSheaf U s) n))
    (hquot : Subsingleton (Sheaf.H (cokernel (oldGeneratedToAdjoinGenerated U s U₀ s₀)) n)) :
    Subsingleton (Sheaf.H (familyGeneratedSheaf (adjoinGeneratorOpens U U₀)
      (adjoinGeneratorSections U s s₀)) n) := by
  let S := adjoinGeneratorShortComplex U s U₀ s₀
  have hSE : S.ShortExact := adjoinGeneratorShortComplex_shortExact U s U₀ s₀
  exact (show Subsingleton (Sheaf.H S.X₂ n) from
    subsingleton_sheafH_of_shortExact_middle hSE n (by simpa using hold) (by simpa using hquot))

/-- A derived Step 3B form: adjoining one generator preserves vanishing in degree `n` if
vanishing is already known for the old generated subsheaf and for every epi image of
`zeroOutsideInt`. -/
theorem subsingleton_of_adjoinGenerator_of_zeroOutside
    {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (n : ℕ)
    (hzero : ∀ {G : Sheaf AddCommGrpCat.{u} X} {V : Opens X}
      (f : zeroOutsideInt V ⟶ G), Epi f → Subsingleton (Sheaf.H G n))
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    (U₀ : Opens X) (s₀ : F.presheaf.obj (op U₀))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)]
    (hold : Subsingleton (Sheaf.H (familyGeneratedSheaf U s) n)) :
    Subsingleton (Sheaf.H (familyGeneratedSheaf (adjoinGeneratorOpens U U₀)
      (adjoinGeneratorSections U s s₀)) n) := by
  apply subsingleton_of_adjoinGenerator n U s U₀ s₀ hold
  exact hzero (adjoinedGeneratorToCokernel U s U₀ s₀) inferInstance

/-- The canonical projection from a singleton coproduct to its unique summand. -/
abbrev singletonFamilyProjection {X : TopCat.{u}} (U : Fin 1 → Opens X)
    [HasCoproduct fun i : Fin 1 => zeroOutsideInt (U i)] :
    (∐ fun i : Fin 1 => zeroOutsideInt (U i)) ⟶ zeroOutsideInt (U 0) :=
  Sigma.desc fun i => by
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact 𝟙 _

@[reassoc]
theorem singletonFamilyProjection_comp_sHom {X : TopCat.{u}} {F : Sheaf AddCommGrpCat.{u} X}
    (U : Fin 1 → Opens X) (s : ∀ i : Fin 1, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i : Fin 1 => zeroOutsideInt (U i)] :
    singletonFamilyProjection U ≫ zeroOutsideInt.sHom (s 0) = familyGeneratorMap U s := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simp [singletonFamilyProjection, familyGeneratorMap]

/-- Base case for finite-generator induction: a sheaf generated epimorphically by one section is
an epi image of the corresponding `zeroOutsideInt`, so any vanishing statement known for all epi
images of `zeroOutsideInt` applies to it. -/
theorem subsingleton_of_singleton_family_of_zeroOutside
    {X : TopCat.{u}} {F : Sheaf AddCommGrpCat.{u} X}
    (n : ℕ)
    (hzero : ∀ {G : Sheaf AddCommGrpCat.{u} X} {V : Opens X}
      (f : zeroOutsideInt V ⟶ G), Epi f → Subsingleton (Sheaf.H G n))
    (U : Fin 1 → Opens X) (s : ∀ i : Fin 1, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i : Fin 1 => zeroOutsideInt (U i)]
    [Epi (familyGeneratorMap U s)] :
    Subsingleton (Sheaf.H F n) := by
  haveI : Epi (zeroOutsideInt.sHom (s 0)) :=
    epi_of_epi_fac (singletonFamilyProjection_comp_sHom U s)
  exact hzero (zeroOutsideInt.sHom (s 0)) inferInstance

end Sheaf
end TopCat
