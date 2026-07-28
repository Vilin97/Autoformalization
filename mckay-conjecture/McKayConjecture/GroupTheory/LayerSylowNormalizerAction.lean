/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.ComponentLocalInvariant
import McKayConjecture.GroupTheory.ComponentCenter
import McKayConjecture.GroupTheory.LayerSylowCoordinates

/-!
# The normalizer action on layer Sylow coordinates

A surjective homomorphism with central kernel induces a bijection on
Sylow `p`-subgroups.  Surjectivity is mathlib's
`Sylow.mapSurjective_surjective`; injectivity follows because two lifts
of the same Sylow subgroup are conjugate inside its full preimage.  The
conjugating element differs from an element of one lift by a central
kernel element, so it already normalizes that lift.

We apply this uniqueness to component multiplication.  Ambient
conjugation permutes the components and acts on their carriers, giving a
canonical automorphism of the external component product.  This
automorphism intertwines component multiplication with conjugation on
the layer.  Hence every ambient element normalizing a layer Sylow
subgroup fixes its unique source lift and transports its coordinate
Sylow family equivariantly.

No coprimality or splitting hypothesis on the central kernel is needed.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory

namespace Sylow

variable {X : Type u} {Y : Type v}
variable [Group X] [Group Y] [Finite X]
variable {p : ℕ} [Fact p.Prime]

/-- A surjective homomorphism with central kernel is injective on Sylow
subgroups. -/
theorem mapSurjective_injective_of_ker_le_center
    {f : X →* Y} (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center X) :
    Function.Injective
      (Sylow.mapSurjective hf :
        Sylow p X → Sylow p Y) := by
  intro P R hmap
  have hmapSubgroup :
      (P : Subgroup X).map f =
        (R : Subgroup X).map f := by
    have h :=
      congrArg
        (fun S : Sylow p Y =>
          (S : Subgroup Y)) hmap
    simpa using h
  let E : Subgroup X :=
    ((P : Subgroup X).map f).comap f
  have hPE : (P : Subgroup X) ≤ E := by
    rw [← Subgroup.map_le_iff_le_comap]
  have hRE : (R : Subgroup X) ≤ E := by
    rw [← Subgroup.map_le_iff_le_comap,
      ← hmapSubgroup]
  obtain ⟨x, hx⟩ :=
    MulAction.exists_smul_eq E
      (P.subtype hPE) (R.subtype hRE)
  have hfx :
      f (x : X) ∈
        (P : Subgroup X).map f :=
    x.2
  obtain ⟨y, hyP, hfy⟩ := hfx
  let yE : E := ⟨y, hPE hyP⟩
  have hyPE :
      yE ∈ (P.subtype hPE :
        Sylow p E) := by
    exact hyP
  let k : E := x * yE⁻¹
  have hkKer :
      (k : X) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [k, yE]
    rw [map_mul, map_inv]
    rw [hfy]
    exact mul_inv_cancel _
  have hkCenterX :
      (k : X) ∈ Subgroup.center X :=
    hker hkKer
  have hkCenterE :
      k ∈ Subgroup.center E := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact
      Subgroup.mem_center_iff.mp hkCenterX
        (z : X)
  have hkNormalizer :
      k ∈ Subgroup.normalizer
        (P.subtype hPE : Set E) :=
    Subgroup.center_le_normalizer
      (P.subtype hPE : Set E) hkCenterE
  have hyNormalizer :
      yE ∈ Subgroup.normalizer
        (P.subtype hPE : Set E) :=
    (P.subtype hPE).le_normalizer hyPE
  have hxNormalizer :
      x ∈ Subgroup.normalizer
        (P.subtype hPE : Set E) := by
    have hxEq : x = k * yE := by
      simp [k]
    rw [hxEq]
    exact
      Subgroup.mul_mem _ hkNormalizer hyNormalizer
  have hxFix :
      x • P.subtype hPE =
        P.subtype hPE :=
    Sylow.smul_eq_iff_mem_normalizer.mpr
      hxNormalizer
  have hsubtype :
      P.subtype hPE =
        R.subtype hRE := by
    rw [← hx]
    exact hxFix.symm
  exact Sylow.subtype_injective hsubtype

/-- Consequently, a surjective homomorphism with central kernel gives a
bijection on Sylow subgroups. -/
theorem mapSurjective_bijective_of_ker_le_center
    {f : X →* Y} (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center X) :
    Function.Bijective
      (Sylow.mapSurjective hf :
        Sylow p X → Sylow p Y) :=
  ⟨mapSurjective_injective_of_ker_le_center
      hf hker,
    Sylow.mapSurjective_surjective hf p⟩

section Eval

variable {ι : Type u} {A : ι → Type v}
variable [∀ i, Group (A i)]
variable [Finite ι] [∀ i, Finite (A i)]

/-- Evaluating a coordinatewise product Sylow subgroup recovers the
chosen coordinate Sylow subgroup. -/
theorem eval_pi_eq
    (P : ∀ i, Sylow p (A i)) (i : ι) :
    Sylow.eval (Sylow.pi P) i = P i := by
  classical
  apply Sylow.ext
  change
    (Subgroup.pi Set.univ
        (fun j => (P j : Subgroup (A j)))).map
        (Pi.evalMonoidHom A i) =
      (P i : Subgroup (A i))
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx i (Set.mem_univ i)
  · intro hy
    refine
      ⟨Pi.mulSingle i y, ?_, by simp⟩
    change
      ∀ j, j ∈ Set.univ →
        Pi.mulSingle i y j ∈ (P j : Subgroup (A j))
    intro j _
    by_cases hji : j = i
    · subst j
      simpa using hy
    · simp [hji]

end Eval

end Sylow

section ComponentProduct

variable (G : Type) [Group G] [Finite G]

/-- Ambient conjugation, including the induced permutation of components,
as an automorphism of the external component product. -/
def layerComponentProductConjugation
    (g : G) :
    (∀ K : ComponentIndex G, K.1) ≃*
      (∀ K : ComponentIndex G, K.1) where
  toFun x L :=
    ⟨g * (x (g⁻¹ • L) : G) * g⁻¹, by
      have hindex : g • (g⁻¹ • L) = L :=
        smul_inv_smul g L
      have hmem :
          g * (x (g⁻¹ • L) : G) * g⁻¹ ∈
            (g • (g⁻¹ • L)).1 := by
        simpa only
          [componentConjugationEquiv_apply_coe] using
            (componentConjugationEquiv
              G g (g⁻¹ • L) (x (g⁻¹ • L))).2
      simpa only [hindex] using hmem⟩
  invFun x K :=
    ⟨g⁻¹ * (x (g • K) : G) * (g⁻¹)⁻¹, by
      have hindex : g⁻¹ • (g • K) = K :=
        inv_smul_smul g K
      have hmem :
          g⁻¹ * (x (g • K) : G) * (g⁻¹)⁻¹ ∈
            (g⁻¹ • (g • K)).1 := by
        simpa only
          [componentConjugationEquiv_apply_coe] using
            (componentConjugationEquiv
              G g⁻¹ (g • K) (x (g • K))).2
      simpa only [hindex] using hmem⟩
  left_inv x := by
    funext K
    apply Subtype.ext
    change
      g⁻¹ *
          (g * (x (g⁻¹ • (g • K)) : G) * g⁻¹) *
          (g⁻¹)⁻¹ =
        (x K : G)
    rw [show g⁻¹ • (g • K) = K by
      exact inv_smul_smul g K]
    simp [mul_assoc]
  right_inv x := by
    funext K
    apply Subtype.ext
    change
      g *
          (g⁻¹ * (x (g • (g⁻¹ • K)) : G) *
            (g⁻¹)⁻¹) *
          g⁻¹ =
        (x K : G)
    rw [show g • (g⁻¹ • K) = K by
      exact smul_inv_smul g K]
    simp [mul_assoc]
  map_mul' x y := by
    funext K
    apply Subtype.ext
    simp [mul_assoc]

omit [Finite G] in
@[simp]
theorem layerComponentProductConjugation_apply_coe
    (g : G)
    (x : ∀ K : ComponentIndex G, K.1)
    (L : ComponentIndex G) :
    ((layerComponentProductConjugation G g x L :
        L.1) : G) =
      g * (x (g⁻¹ • L) : G) * g⁻¹ :=
  rfl

omit [Finite G] in
@[simp]
theorem layerComponentProductConjugation_one :
    layerComponentProductConjugation G 1 =
      MulEquiv.refl
        (∀ K : ComponentIndex G, K.1) := by
  ext x K
  have hindex : (1 : G)⁻¹ • K = K := by
    simp
  have hcoe :
      ((x ((1 : G)⁻¹ • K) :
          ((1 : G)⁻¹ • K).1) : G) =
        (x K : G) := by
    rw [hindex]
  simpa [layerComponentProductConjugation_apply_coe]
    using hcoe

omit [Finite G] in
theorem layerComponentProductConjugation_mul
    (g h : G) :
    layerComponentProductConjugation G (g * h) =
      (layerComponentProductConjugation G g :
        MulAut
          (∀ K : ComponentIndex G, K.1)) *
        layerComponentProductConjugation G h := by
  ext x K
  have hindex :
      (g * h)⁻¹ • K =
        h⁻¹ • (g⁻¹ • K) := by
    simp [mul_smul]
  have hcoe :
      ((x ((g * h)⁻¹ • K) :
          ((g * h)⁻¹ • K).1) : G) =
        (x (h⁻¹ • (g⁻¹ • K)) : G) := by
    rw [hindex]
  simpa [layerComponentProductConjugation_apply_coe,
    mul_assoc] using hcoe

/-- The component-product conjugation automorphisms form the ambient
group action on the external component product. -/
def layerComponentProductConjugationHom :
    G →* MulAut
      (∀ K : ComponentIndex G, K.1) where
  toFun := layerComponentProductConjugation G
  map_one' :=
    layerComponentProductConjugation_one
      (G := G)
  map_mul' :=
    layerComponentProductConjugation_mul
      (G := G)

omit [Finite G] in
/-- A value supported in one component is transported to the conjugate
component. -/
theorem layerComponentProductConjugation_mulSingle
    [DecidableEq (ComponentIndex G)]
    (g : G) (K : ComponentIndex G) (x : K.1) :
    layerComponentProductConjugation G g
        (Pi.mulSingle
          (M := fun L : ComponentIndex G => L.1)
          K x) =
      Pi.mulSingle
        (M := fun L : ComponentIndex G => L.1)
        (g • K)
        (componentConjugationEquiv G g K x) := by
  funext L
  by_cases hL : L = g • K
  · subst L
    apply Subtype.ext
    have hindex : g⁻¹ • (g • K) = K :=
      inv_smul_smul g K
    have hvalue :
        (((Pi.mulSingle
          (M := fun L : ComponentIndex G => L.1)
          K x) (g⁻¹ • (g • K)) :
            (g⁻¹ • (g • K)).1) : G) =
          (x : G) := by
      rw [hindex]
      simp
    simpa [layerComponentProductConjugation_apply_coe]
      using hvalue
  · have hpre : g⁻¹ • L ≠ K := by
      intro h
      apply hL
      calc
        L = g • (g⁻¹ • L) :=
          (smul_inv_smul g L).symm
        _ = g • K := by rw [h]
    apply Subtype.ext
    simp [hL, hpre]

private theorem monoidHom_ext_mulSingle
    {ι : Type u} [Finite ι] [DecidableEq ι]
    {A : ι → Type v} [∀ i, Group (A i)]
    {B : Type*} [Group B]
    {f h : (∀ i, A i) →* B}
    (heq :
      ∀ (i : ι) (x : A i),
        f (Pi.mulSingle i x) =
          h (Pi.mulSingle i x)) :
    f = h := by
  letI := Fintype.ofFinite ι
  apply
    (MonoidHom.noncommPiCoprodEquiv
      (N := A) (M := B)).symm.injective
  apply Subtype.ext
  funext i
  apply MonoidHom.ext
  intro x
  exact heq i x

/-- Component-product conjugation intertwines component multiplication
with ambient conjugation on the layer. -/
theorem layerProductHom_comp_conjugation
    (g : G) :
    (layerProductHom G).comp
        (layerComponentProductConjugation G g).toMonoidHom =
      (MulAut.conjNormal g :
          MulAut (layer G)).toMonoidHom.comp
        (layerProductHom G) := by
  classical
  letI := Fintype.ofFinite (ComponentIndex G)
  apply monoidHom_ext_mulSingle
  intro K x
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  change
    layerProductHom G
        (layerComponentProductConjugation G g
          (Pi.mulSingle K x)) =
      (MulAut.conjNormal g :
        MulAut (layer G))
        (layerProductHom G (Pi.mulSingle K x))
  rw [layerComponentProductConjugation_mulSingle,
    show
      layerProductHom G
          (Pi.mulSingle (g • K)
            (componentConjugationEquiv G g K x)) =
        componentToLayerHom G (g • K)
          (componentConjugationEquiv G g K x) by
      apply Subtype.ext
      change
        Subgroup.noncommPiCoprod
            (components_pairwise_commute_elements
              (G := G))
            (Pi.mulSingle (g • K)
              (componentConjugationEquiv G g K x)) =
          (componentConjugationEquiv G g K x : G)
      exact
        Subgroup.noncommPiCoprod_mulSingle
          (g • K)
          (componentConjugationEquiv G g K x),
    show
      layerProductHom G
          (Pi.mulSingle K x) =
        componentToLayerHom G K x by
      apply Subtype.ext
      change
        Subgroup.noncommPiCoprod
            (components_pairwise_commute_elements
              (G := G))
            (Pi.mulSingle K x) =
          (x : G)
      exact
        Subgroup.noncommPiCoprod_mulSingle K x]
  apply Subtype.ext
  rfl

end ComponentProduct

section CoordinateAction

variable (G : Type) [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- Transport a component Sylow subgroup to the conjugate component. -/
def componentConjugateSylow
    (g : G) (K : ComponentIndex G)
    (P : Sylow p K.1) :
    Sylow p (g • K).1 :=
  P.mapSurjective
    (f :=
      (componentConjugationEquiv
        G g K).toMonoidHom)
    (componentConjugationEquiv G g K).surjective

@[simp, norm_cast]
theorem coe_componentConjugateSylow
    (g : G) (K : ComponentIndex G)
    (P : Sylow p K.1) :
    (componentConjugateSylow G g K P :
        Subgroup (g • K).1) =
      (P : Subgroup K.1).map
        (componentConjugationEquiv
          G g K).toMonoidHom :=
  rfl

omit [Finite G] in
/-- Evaluating after conjugating the component product is the same as
first evaluating and then conjugating that component. -/
theorem evalMonoidHom_comp_layerComponentProductConjugation
    (g : G) (K : ComponentIndex G) :
    (Pi.evalMonoidHom
        (fun L : ComponentIndex G => L.1)
        (g • K)).comp
        (layerComponentProductConjugation
          G g).toMonoidHom =
      (componentConjugationEquiv
        G g K).toMonoidHom.comp
        (Pi.evalMonoidHom
          (fun L : ComponentIndex G => L.1) K) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  have hindex : g⁻¹ • (g • K) = K :=
    inv_smul_smul g K
  have hcoe :
      ((x (g⁻¹ • (g • K)) :
          (g⁻¹ • (g • K)).1) : G) =
        (x K : G) := by
    rw [hindex]
  exact congrArg
    (fun z : G => g * z * g⁻¹) hcoe

/-- Conjugation of the component product transports an evaluated Sylow
subgroup to the Sylow subgroup evaluated in the conjugate coordinate. -/
theorem componentConjugateSylow_eval
    (g : G) (K : ComponentIndex G)
    (S : Sylow p
      (∀ L : ComponentIndex G, L.1)) :
    componentConjugateSylow G g K
        (Sylow.eval S K) =
      Sylow.eval
        ((layerComponentProductConjugation
            G g : MulAut
              (∀ L : ComponentIndex G, L.1)) • S)
        (g • K) := by
  rw [Sylow.ext_iff,
    coe_componentConjugateSylow,
    Sylow.coe_eval, Sylow.coe_eval]
  have hsmul :
      ((((layerComponentProductConjugation
          G g : MulAut
            (∀ L : ComponentIndex G, L.1)) • S) :
          Sylow p
            (∀ L : ComponentIndex G, L.1)) :
          Subgroup
            (∀ L : ComponentIndex G, L.1)) =
        (S : Subgroup
          (∀ L : ComponentIndex G, L.1)).map
            (layerComponentProductConjugation
              G g).toMonoidHom := by
    rfl
  rw [hsmul]
  rw [Subgroup.map_map, Subgroup.map_map,
    evalMonoidHom_comp_layerComponentProductConjugation]

namespace LayerSylowCoordinateData

variable {Q : Sylow p (layer G)}

/-- The coordinates stored in `LayerSylowCoordinateData` are exactly the
evaluation images of its source Sylow subgroup. -/
theorem coordinate_eq_eval
    (D : LayerSylowCoordinateData G p Q)
    (K : ComponentIndex G) :
    D.coordinate K =
      Sylow.eval D.source K := by
  calc
    D.coordinate K =
        Sylow.eval (Sylow.pi D.coordinate) K :=
      (Sylow.eval_pi_eq D.coordinate K).symm
    _ = Sylow.eval D.source K := by
      rw [D.source_eq_pi]

/-- The source field is the unique Sylow subgroup of the component
product mapping to `Q`. -/
theorem eq_source_of_map_eq
    (D : LayerSylowCoordinateData G p Q)
    (S : Sylow p
      (∀ K : ComponentIndex G, K.1))
    (hS :
      S.mapSurjective
          (layerProductHom_surjective G) =
        Q) :
    S = D.source := by
  apply
    Sylow.mapSurjective_injective_of_ker_le_center
      (layerProductHom_surjective G)
      (layerProductHom_ker_le_center G)
  rw [hS, D.map_eq]

/-- Conjugating a source lift and then mapping to the layer gives the
conjugate of the prescribed layer Sylow subgroup. -/
theorem map_conjugated_source_eq_layer_conjugate
    (D : LayerSylowCoordinateData G p Q)
    (g : G) :
    (((layerComponentProductConjugation
          G g : MulAut
            (∀ K : ComponentIndex G, K.1)) •
        D.source).mapSurjective
          (layerProductHom_surjective G)) =
      (MulAut.conjNormal g :
        MulAut (layer G)) • Q := by
  apply Sylow.ext
  have hsourceSmul :
      ((((layerComponentProductConjugation
          G g : MulAut
            (∀ K : ComponentIndex G, K.1)) •
        D.source) :
          Sylow p
            (∀ K : ComponentIndex G, K.1)) :
          Subgroup
            (∀ K : ComponentIndex G, K.1)) =
        (D.source :
          Subgroup
            (∀ K : ComponentIndex G, K.1)).map
              (layerComponentProductConjugation
                G g).toMonoidHom := by
    rfl
  have hlayerSmul :
      (((MulAut.conjNormal g :
          MulAut (layer G)) • Q :
          Sylow p (layer G)) :
          Subgroup (layer G)) =
        (Q : Subgroup (layer G)).map
          (MulAut.conjNormal g :
            MulAut (layer G)).toMonoidHom := by
    rfl
  change
    (((((layerComponentProductConjugation
        G g : MulAut
          (∀ K : ComponentIndex G, K.1)) •
      D.source) :
        Sylow p
          (∀ K : ComponentIndex G, K.1)) :
        Subgroup
          (∀ K : ComponentIndex G, K.1)).map
            (layerProductHom G)) =
      (((MulAut.conjNormal g :
        MulAut (layer G)) • Q :
        Sylow p (layer G)) :
        Subgroup (layer G))
  rw [hsourceSmul, hlayerSmul,
    Subgroup.map_map,
    layerProductHom_comp_conjugation,
    ← Subgroup.map_map,
    D.map_source_eq]

/-- If ambient conjugation fixes the layer Sylow subgroup, uniqueness of
the central-kernel lift forces it to fix the chosen source Sylow subgroup. -/
theorem source_smul_eq_of_layer_smul_eq
    (D : LayerSylowCoordinateData G p Q)
    (g : G)
    (hQ :
      (MulAut.conjNormal g :
        MulAut (layer G)) • Q = Q) :
    (layerComponentProductConjugation
        G g : MulAut
          (∀ K : ComponentIndex G, K.1)) •
      D.source =
        D.source := by
  apply
    Sylow.mapSurjective_injective_of_ker_le_center
      (layerProductHom_surjective G)
      (layerProductHom_ker_le_center G)
  rw [map_conjugated_source_eq_layer_conjugate
      (G := G) D,
    hQ, D.map_eq]

/-- Membership in the ambient normalizer of the ambient image of `Q`
is exactly enough to make ambient conjugation fix `Q` as a Sylow subgroup
of the layer. -/
theorem layer_smul_eq_of_mem_ambient_normalizer
    (_D : LayerSylowCoordinateData G p Q)
    (g : G)
    (hg :
      g ∈ Subgroup.normalizer
        ((Q : Subgroup (layer G)).map
          (layer G).subtype : Set G)) :
    (MulAut.conjNormal g :
      MulAut (layer G)) • Q = Q := by
  apply Sylow.ext
  apply
    Subgroup.map_injective
      (f := (layer G).subtype)
      Subtype.coe_injective
  have hlayerSmul :
      (((MulAut.conjNormal g :
          MulAut (layer G)) • Q :
          Sylow p (layer G)) :
          Subgroup (layer G)) =
        (Q : Subgroup (layer G)).map
          (MulAut.conjNormal g :
            MulAut (layer G)).toMonoidHom := by
    rfl
  rw [hlayerSmul, Subgroup.map_map]
  have hintertwine :
      (layer G).subtype.comp
          (MulAut.conjNormal g :
            MulAut (layer G)).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp
          (layer G).subtype := by
    ext x
    rfl
  rw [hintertwine, ← Subgroup.map_map]
  exact
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg

/-- An ambient normalizer element fixes the unique chosen source lift. -/
theorem source_smul_eq_of_mem_ambient_normalizer
    (D : LayerSylowCoordinateData G p Q)
    (g : G)
    (hg :
      g ∈ Subgroup.normalizer
        ((Q : Subgroup (layer G)).map
          (layer G).subtype : Set G)) :
    (layerComponentProductConjugation
        G g : MulAut
          (∀ K : ComponentIndex G, K.1)) •
      D.source =
        D.source :=
  source_smul_eq_of_layer_smul_eq
    (G := G) D g
      (layer_smul_eq_of_mem_ambient_normalizer
        (G := G) D g hg)

/-- Under a layer-stabilizing ambient conjugation, the coordinate Sylow
family is transported exactly to the conjugate components. -/
theorem componentConjugate_coordinate_eq_of_layer_smul_eq
    (D : LayerSylowCoordinateData G p Q)
    (g : G)
    (hQ :
      (MulAut.conjNormal g :
        MulAut (layer G)) • Q = Q)
    (K : ComponentIndex G) :
    componentConjugateSylow G g K
        (D.coordinate K) =
      D.coordinate (g • K) := by
  calc
    componentConjugateSylow G g K
        (D.coordinate K) =
      componentConjugateSylow G g K
        (Sylow.eval D.source K) := by
          rw [coordinate_eq_eval
            (G := G) D K]
    _ = Sylow.eval
        ((layerComponentProductConjugation
          G g : MulAut
            (∀ L : ComponentIndex G, L.1)) •
          D.source) (g • K) :=
      componentConjugateSylow_eval
        G g K D.source
    _ = Sylow.eval D.source (g • K) := by
      rw [source_smul_eq_of_layer_smul_eq
        (G := G) D g hQ]
    _ = D.coordinate (g • K) :=
      (coordinate_eq_eval
        (G := G) D (g • K)).symm

/-- Therefore every ambient element normalizing the ambient image of `Q`
transports the chosen coordinate family equivariantly. -/
theorem componentConjugate_coordinate_eq_of_mem_ambient_normalizer
    (D : LayerSylowCoordinateData G p Q)
    (g : G)
    (hg :
      g ∈ Subgroup.normalizer
        ((Q : Subgroup (layer G)).map
          (layer G).subtype : Set G))
    (K : ComponentIndex G) :
    componentConjugateSylow G g K
        (D.coordinate K) =
      D.coordinate (g • K) :=
  componentConjugate_coordinate_eq_of_layer_smul_eq
    (G := G) D g
    (layer_smul_eq_of_mem_ambient_normalizer
      (G := G) D g hg)
    K

end LayerSylowCoordinateData

end CoordinateAction

end GroupTheory
end McKayConjecture
