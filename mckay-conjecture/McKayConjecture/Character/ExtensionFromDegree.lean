/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ExtensionConstituent

/-!
# Recognizing character extensions from degree

If an irreducible character lies over another irreducible character along
a homomorphism, a nonzero intertwiner embeds the smaller realization into
the restricted larger realization.  Equality of character degrees makes
that embedding an equivalence.  Hence the two restricted characters agree
pointwise, which is exactly the extension property.

This criterion separates the two numerical ingredients hidden in an
extension assertion: positive restriction multiplicity and equality of
degrees.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G H : Type} [Group G] [Group H]

/-- An irreducible character lying over another character with the same
degree is an exact extension of that character. -/
theorem IsExtensionAlong.of_liesOver_of_degree_eq
    {f : H →* G}
    {χ : IrreducibleCharacter H}
    {ψ : IrreducibleCharacter G}
    (hover :
      CliffordCorrespondence.LiesOverAlong f χ ψ)
    (hdegree : ψ.degree = χ.degree) :
    IsExtensionAlong f χ ψ := by
  obtain ⟨i, hi⟩ :=
    (CliffordCorrespondence.liesOverAlong_iff_exists_nonzero
      f χ ψ).mp hover
  have hinjective : Function.Injective i :=
    CliffordCorrespondence.fdRepHom_injective_of_nonzero_from_simple
      i hi
  have hfinrank :
      Module.finrank ℂ χ.realization =
        Module.finrank ℂ
          (FDRep.res f ψ.realization) := by
    rw [χ.realization_finrank]
    change χ.degree = Module.finrank ℂ ψ.realization
    rw [ψ.realization_finrank, hdegree]
  have hsurjective : Function.Surjective i :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hfinrank).mp hinjective
  let iRep :
      Representation.IntertwiningMap
        χ.realization.ρ
        (FDRep.res f ψ.realization).ρ :=
    ((FDRep.forget₂HomLinearEquiv
      χ.realization
      (FDRep.res f ψ.realization)).symm i).hom
  let e :
      Representation.Equiv
        χ.realization.ρ
        (FDRep.res f ψ.realization).ρ :=
    iRep.ofBijective ⟨hinjective, hsurjective⟩
  have hcharacter :
      χ.realization.character =
        (FDRep.res f ψ.realization).character :=
    Representation.char_iso e
  intro h
  calc
    ψ.values (f h) =
        ψ.realization.character (f h) :=
      (congrFun ψ.realization_character (f h)).symm
    _ =
        (FDRep.res f ψ.realization).character h :=
      rfl
    _ =
        χ.realization.character h :=
      congrFun hcharacter.symm h
    _ =
        χ.values h :=
      congrFun χ.realization_character h

/-- For a normal subgroup inclusion, lying over with equal degree is
equivalent to being an extension. -/
theorem isExtension_iff_liesOver_and_degree_eq
    {G : Type} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal]
    {χ : IrreducibleCharacter N}
    {ψ : IrreducibleCharacter G} :
    IsExtension N χ ψ ↔
      CliffordCorrespondence.LiesOverAlong N.subtype χ ψ ∧
        ψ.degree = χ.degree := by
  constructor
  · intro h
    exact ⟨h.liesOver, h.degree_eq⟩
  · rintro ⟨hover, hdegree⟩
    exact
      IsExtensionAlong.of_liesOver_of_degree_eq
        hover hdegree

end IrreducibleCharacter
end McKayConjecture
