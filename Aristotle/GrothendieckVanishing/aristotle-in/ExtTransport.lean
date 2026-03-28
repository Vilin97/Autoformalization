import Mathlib

universe u

open CategoryTheory Abelian

set_option maxHeartbeats 800000

/-- Transport Ext along an isomorphism in the first variable.
    If A ≅ B, then Ext(B, F, n) ≃+ Ext(A, F, n).

    Uses Ext.precomp with mk₀(f.hom) and mk₀(f.inv).
    These compose to identity by:
    - mk₀(f.hom).comp(mk₀(f.inv)) = mk₀(f.inv ≫ f.hom) = mk₀(𝟙) = 1 in Ext(B,B,0)
    - precomp is functorial: precomp(a.comp(b)) = precomp(b) ∘ precomp(a)

    Mathlib tools: Ext.precomp, Ext.mk₀, Ext.mk₀_comp, Ext.precomp_id -/
noncomputable def Ext.addEquivOfIso {C : Type*} [Category C] [Abelian C] [HasExt C]
    {A B F : C} (f : A ≅ B) (n : ℕ) :
    Abelian.Ext B F n ≃+ Abelian.Ext A F n where
  toFun := (Ext.mk₀ f.hom).precomp F rfl
  invFun := (Ext.mk₀ f.inv).precomp F rfl
  left_inv x := by
    -- Need: precomp(mk₀ f.inv, precomp(mk₀ f.hom, x)) = x
    -- = precomp(mk₀(f.hom).comp(mk₀(f.inv)), x)  [by functoriality of precomp]
    -- = precomp(mk₀(f.inv ≫ f.hom), x)  [by mk₀_comp]
    -- = precomp(mk₀(𝟙), x) = x  [by precomp_id or mk₀_id]
    sorry
  right_inv x := by sorry
  map_add' x y := by
    exact map_add ((Ext.mk₀ f.hom).precomp F rfl) x y
