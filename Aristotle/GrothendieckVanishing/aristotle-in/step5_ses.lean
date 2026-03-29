/-
  Build the short exact sequence 0 → Z_U → Z_X → cokernel → 0
  and show the cokernel has zero stalks on U (hence is "supported on Y = X\U").

  Z_U = zeroOutsideInt U = sheafification of (presheaf that is Z on V ⊆ U, 0 on V ⊄ U)
  Z_X = constant sheaf = sheafification of constant presheaf

  The inclusion Z_U ↪ Z_X comes from zeroOutsideInt.openHom with le_top : U ≤ ⊤,
  composed with an isomorphism zeroOutsideInt ⊤ ≅ Z_X.

  For the isomorphism: zeroOutsideInt ⊤ = sheafification of (presheaf that is Z on
  V ≤ ⊤ = all V, 0 otherwise). Since every V ≤ ⊤, this is the sheafification of
  the constant presheaf, which is the constant sheaf.

  Key: we need to show that the cokernel C of Z_U → Z_X satisfies:
  - stalk C x = 0 for x ∈ U
  - This means C is "supported on Y = X\U"
  - Hence C can be identified with (or mapped from) i_*(constant sheaf on Y)
    via PushforwardHVanishing
-/
import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits Opposite

/-- The presheaf extension by zero of the constant presheaf. -/
noncomputable def constZ_zeroOutside {X : TopCat.{u}} (U : Opens X) :
    TopCat.Presheaf AddCommGrpCat.{u} X :=
  ((Functor.const _).obj (AddCommGrpCat.of (ULift ℤ))).zeroOutside U

/-- The constant presheaf on X. -/
noncomputable def constPresheaf (X : TopCat.{u}) :
    TopCat.Presheaf AddCommGrpCat.{u} X :=
  (Functor.const _).obj (AddCommGrpCat.of (ULift ℤ))

/-- The inclusion map at the presheaf level: constZ_zeroOutside U → constPresheaf X.
    This is the natural transformation that is identity on V ≤ U and 0 on V ⊄ U. -/
noncomputable def constZ_zeroOutside_to_const {X : TopCat.{u}} (U : Opens X) :
    constZ_zeroOutside U ⟶ constPresheaf X := by
  sorry

/-- The presheaf map constZ_zeroOutside U → constPresheaf X is a monomorphism. -/
theorem constZ_zeroOutside_to_const_mono {X : TopCat.{u}} (U : Opens X) :
    Mono (constZ_zeroOutside_to_const U) := by
  sorry

/-- After sheafification, the map zeroOutsideInt U → constantSheaf Z is a
    monomorphism in the sheaf category. -/
theorem zeroOutsideInt_to_constantSheaf_mono {X : TopCat.{u}} (U : Opens X) :
    Mono (sheafifyMap (Opens.grothendieckTopology X)
      (constZ_zeroOutside_to_const U) :
        TopCat.Sheaf.zeroOutsideInt U ⟶
        (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ))) := by
  sorry

/-- The stalk of the cokernel of Z_U → Z_X is zero at points x ∈ U.
    This means the cokernel is "supported on Y = X\U". -/
theorem cokernel_stalk_zero_on_U {X : TopCat.{u}} (U : Opens X) (x : X) (hx : x ∈ U) :
    let f := sheafifyMap (Opens.grothendieckTopology X)
      (constZ_zeroOutside_to_const U)
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (cokernel f).val) := by
  sorry
