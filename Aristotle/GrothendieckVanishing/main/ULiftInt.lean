import Mathlib
/-!
# `ULift ℤ` additive equivalence

Transport maps out of the constant `ULift ℤ` group to the chosen image of `1`.
-/

universe u
open CategoryTheory
noncomputable section
namespace AddCommGrpCat

/-- The additive equivalence `(ULift ℤ ⟶ G) ≃+ G`. -/
def uliftZMultiplesAddEquiv (G : AddCommGrpCat.{u}) :
    (AddCommGrpCat.of (ULift ℤ) ⟶ G) ≃+ G :=
  AddEquiv.trans
    (@AddCommGrpCat.homAddEquiv (AddCommGrpCat.of (ULift ℤ)) G)
    (AddEquiv.mk' (uliftZMultiplesHom G) (by
      intro x y
      ext
      simp_all only [uliftZMultiplesHom_apply_apply, smul_add, AddMonoidHom.add_apply])).symm

@[simp] theorem uliftZMultiplesAddEquiv_symm_apply
    (G : AddCommGrpCat.{u}) (x : G) (n : ULift ℤ) :
    AddCommGrpCat.Hom.hom ((AddCommGrpCat.uliftZMultiplesAddEquiv G).symm x) n =
      (n.down : ℤ) • x := rfl

end AddCommGrpCat
