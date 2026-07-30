/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ExtensionEquivalenceTransport
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalFullInertiaScalar
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionOkuyamaWajimaCharacterInertia
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionOkuyamaWajimaInertiaGroup

/-!
# Characters on the source-character Okuyama--Wajima inertia group

Fix a prime-to-`q` character `theta` of `D = CS` and put
`Γ_theta = I_X(theta)`.  The preceding group-theoretic adapter copied the
canonical `q'`-kernel `R` of `D` into `Γ_theta`.  This file transports the
canonical character of `R` and `theta` themselves to the corresponding
copies

* `R_theta ≤ D_theta ≤ Γ_theta`,
* `D_theta = inertiaNormalCopy D theta`.

The transported character of `R_theta` is `q'`-degree, is fixed by all of
`Γ_theta`, and extends to the transported copy of `theta` on `D_theta`.
That extension is itself `Γ_theta`-invariant.  These are the exact character
hypotheses used when the ordinary Okuyama--Wajima theorem is applied inside
`Γ_theta`.

The auxiliary inertia group of the kernel character is only compared by an
inclusion `Γ_theta ≤ Δ_r`; no equality of the two inertia groups is asserted.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CliffordEquivalence
open CliffordCorrespondence
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

omit [Finite X] in
/-- If a character of a normal subgroup extends a character of a smaller
normal subgroup, then the inertia group of the extension is contained in the
inertia group of the restricted character. -/
theorem inertia_le_inertia_of_normalExtension
    (K D : Subgroup X) [K.Normal] [D.Normal]
    (hKD : K ≤ D)
    (r : IrreducibleCharacter K)
    (theta : IrreducibleCharacter D)
    (hext :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion hKD) r theta) :
    IrreducibleCharacter.inertia D theta ≤
      IrreducibleCharacter.inertia K r := by
  intro x hx
  rw [IrreducibleCharacter.mem_inertia_iff] at hx ⊢
  apply IrreducibleCharacter.ext
  funext k
  rw [IrreducibleCharacter.conjBy_values]
  let kD : D := ⟨(k : X), hKD k.2⟩
  let kConj : K :=
    (MulAut.conjNormal (H := K) x).symm k
  let kDConj : D :=
    (MulAut.conjNormal (H := D) x).symm kD
  have hvalue :=
    congrArg
      (fun chi : IrreducibleCharacter D => chi.values kD)
      hx
  rw [IrreducibleCharacter.conjBy_values] at hvalue
  have hconj :
      Subgroup.inclusion hKD kConj = kDConj := by
    apply Subtype.ext
    rfl
  calc
    r.values kConj =
        theta.values
          (Subgroup.inclusion hKD kConj) :=
      (hext kConj).symm
    _ = theta.values kDConj := by rw [hconj]
    _ = theta.values kD := hvalue
    _ = r.values k := hext k

/-- The ambient copy of the canonical kernel lies in `D = CS`. -/
theorem productAmbientPPrimeKernel_le_product
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    productAmbientPPrimeKernel S C hcentral ≤
      product S C := by
  rintro _ ⟨r, _hr, rfl⟩
  exact r.2

/-- The original character `theta` extends the canonical kernel character
after that kernel is transported to its literal ambient copy in `X`. -/
theorem productAmbientGlaubermanTheta_isAmbientKernelExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IrreducibleCharacter.IsExtensionAlong
      (Subgroup.inclusion
        (productAmbientPPrimeKernel_le_product
          S C hcentral))
      (productAmbientGlaubermanKernelCharacterInX
        S C hcentral theta).1
      theta.1 := by
  let eK :
      productAmbientPPrimeKernel S C hcentral ≃*
        productPPrimeKernel S C hcentral :=
    (productPPrimeKernelAmbientEquiv S C hcentral).symm
  intro k
  have hk :
      Subgroup.inclusion
          (productAmbientPPrimeKernel_le_product
            S C hcentral) k =
        (productPPrimeKernel S C hcentral).subtype
          (eK k) := by
    apply Subtype.ext
    change
      (k : X) =
        (((eK k :
          productPPrimeKernel S C hcentral) :
          product S C) : X)
    let e := productPPrimeKernelAmbientEquiv S C hcentral
    calc
      (k : X) =
          ((e (eK k) :
            productAmbientPPrimeKernel S C hcentral) : X) :=
        (congrArg
          (fun z :
            productAmbientPPrimeKernel S C hcentral =>
              (z : X))
          (e.apply_symm_apply k)).symm
      _ = (((eK k :
          productPPrimeKernel S C hcentral) :
          product S C) : X) := rfl
  change
    theta.1.values
        (Subgroup.inclusion
          (productAmbientPPrimeKernel_le_product
            S C hcentral) k) =
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1.values (eK k)
  rw [hk]
  exact
    productAmbientGlaubermanTheta_isSourceKernelExtension
      S C hcentral theta (eK k)

/-- The source-character inertia group is contained in the auxiliary full
inertia group of the canonical kernel character.  This is only an inclusion:
the reverse containment need not hold. -/
theorem productAmbientGlaubermanLeftInertia_le_productOkuyamaWajimaInertia
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    (ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta :
      Subgroup X) ≤
      productOkuyamaWajimaInertia
        S C hcentral hgenerate theta := by
  let D := product S C
  let K := productAmbientPPrimeKernel S C hcentral
  letI : D.Normal :=
    product_normal S C hgenerate
  letI : K.Normal :=
    productAmbientPPrimeKernel_normal
      S C hcentral hgenerate
  exact
    inertia_le_inertia_of_normalExtension
      K D
      (productAmbientPPrimeKernel_le_product
        S C hcentral)
      (productAmbientGlaubermanKernelCharacterInX
        S C hcentral theta).1
      theta.1
      (productAmbientGlaubermanTheta_isAmbientKernelExtension
        S C hcentral theta)

/-- The canonical kernel character transported to the copy of the kernel
inside `Γ_theta`. -/
def productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    PPrimeIrreducibleCharacter
      (productAmbientGlaubermanLeftInertiaPPrimeKernel
        S C hcentral hgenerate theta) q := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    IrreducibleCharacter.pPrimeComapEquiv q
      (inertiaSubgroupCopyEquiv
        (product S C) theta.1
        (productPPrimeKernel S C hcentral)).symm
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1

@[simp]
theorem productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    (productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter
        S C hcentral hgenerate theta).1 =
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1.comap
        (inertiaSubgroupCopyEquiv
          (product S C) theta.1
          (productPPrimeKernel S C hcentral)).symm :=
  rfl

/-- The original character transported to the canonical normal copy of
`D = CS` in `Γ_theta`. -/
def productAmbientGlaubermanLeftInertiaTheta
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    PPrimeIrreducibleCharacter
      (inertiaNormalCopy (product S C) theta.1) q := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact
    ⟨inertiaCopyCharacter (product S C) theta.1,
      theta.2⟩

omit [Finite X] [Fact q.Prime] in
@[simp]
theorem productAmbientGlaubermanLeftInertiaTheta_coe
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    (productAmbientGlaubermanLeftInertiaTheta
        S C hgenerate theta).1 =
      inertiaCopyCharacter (product S C) theta.1 :=
  rfl

/-- The copied kernel is contained in the copied normal product. -/
theorem
    productAmbientGlaubermanLeftInertiaPPrimeKernel_le_normalCopy
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    productAmbientGlaubermanLeftInertiaPPrimeKernel
        S C hcentral hgenerate theta ≤
      inertiaNormalCopy (product S C) theta.1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact y.2

/-- The copied character `theta` extends the copied canonical kernel
character on `R_theta ≤ D_theta`. -/
theorem
    productAmbientGlaubermanLeftInertiaTheta_isKernelExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    IrreducibleCharacter.IsExtensionAlong
      (Subgroup.inclusion
        (productAmbientGlaubermanLeftInertiaPPrimeKernel_le_normalCopy
          S C hcentral hgenerate theta))
      (productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter
        S C hcentral hgenerate theta).1
      (productAmbientGlaubermanLeftInertiaTheta
        S C hgenerate theta).1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let R := productPPrimeKernel S C hcentral
  let Rcopy :=
    productAmbientGlaubermanLeftInertiaPPrimeKernel
      S C hcentral hgenerate theta
  let D := product S C
  let Dcopy := inertiaNormalCopy D theta.1
  let eR : Rcopy ≃* R :=
    (inertiaSubgroupCopyEquiv D theta.1 R).symm
  let eD : Dcopy ≃* D :=
    inertiaNormalCopyEquiv D theta.1
  have hcomm :
      eD.toMonoidHom.comp
          (Subgroup.inclusion
            (productAmbientGlaubermanLeftInertiaPPrimeKernel_le_normalCopy
              S C hcentral hgenerate theta)) =
        R.subtype.comp eR.toMonoidHom := by
    apply MonoidHom.ext
    intro r
    apply Subtype.ext
    let e :=
      inertiaSubgroupCopyEquiv D theta.1 R
    have hr :=
      congrArg
        (fun z : Rcopy =>
          (((z :
            ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta) : X)))
        (e.apply_symm_apply r)
    change
      (((r : Rcopy) :
        ProductAmbientGlaubermanLeftInertiaGroup
          S C hgenerate theta) : X) =
        (((eR r : R) : D) : X)
    calc
      (((r : Rcopy) :
          ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta) : X) =
          (((e (eR r) : Rcopy) :
            ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta) : X) :=
        hr.symm
      _ = (((eR r : R) : D) : X) := by
        rw [inertiaSubgroupCopyEquiv_apply_coe]
        rfl
  exact
    IrreducibleCharacter.IsExtensionAlong.comap_equiv
      eD eR hcomm
      (productAmbientGlaubermanTheta_isSourceKernelExtension
        S C hcentral theta)

omit [Finite X] [Fact q.Prime] in
/-- The copied `theta` is invariant under the whole exact source inertia
group `Γ_theta`. -/
theorem productAmbientGlaubermanLeftInertiaTheta_isInvariant
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (a :
      ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    IrreducibleCharacter.conjBy
        (inertiaNormalCopy (product S C) theta.1) a
        (productAmbientGlaubermanLeftInertiaTheta
          S C hgenerate theta).1 =
      (productAmbientGlaubermanLeftInertiaTheta
        S C hgenerate theta).1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  exact inertiaCopyCharacter_invariant
    (product S C) theta.1 a

/-- The transported canonical kernel character is invariant under the whole
exact source inertia group `Γ_theta`. -/
theorem
    productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter_isInvariant
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (a :
      ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    IrreducibleCharacter.conjBy
        (productAmbientGlaubermanLeftInertiaPPrimeKernel
          S C hcentral hgenerate theta) a
        (productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter
          S C hcentral hgenerate theta).1 =
      (productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter
        S C hcentral hgenerate theta).1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let K :=
    productAmbientGlaubermanLeftInertiaPPrimeKernel
      S C hcentral hgenerate theta
  let D := inertiaNormalCopy (product S C) theta.1
  have hle :
      IrreducibleCharacter.inertia D
          (productAmbientGlaubermanLeftInertiaTheta
            S C hgenerate theta).1 ≤
        IrreducibleCharacter.inertia K
          (productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter
            S C hcentral hgenerate theta).1 :=
    inertia_le_inertia_of_normalExtension
      K D
      (productAmbientGlaubermanLeftInertiaPPrimeKernel_le_normalCopy
        S C hcentral hgenerate theta)
      (productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter
        S C hcentral hgenerate theta).1
      (productAmbientGlaubermanLeftInertiaTheta
        S C hgenerate theta).1
      (productAmbientGlaubermanLeftInertiaTheta_isKernelExtension
        S C hcentral hgenerate theta)
  rw [← IrreducibleCharacter.mem_inertia_iff]
  exact hle
    ((IrreducibleCharacter.mem_inertia_iff
      D
      (productAmbientGlaubermanLeftInertiaTheta
        S C hgenerate theta).1 a).mpr
      (productAmbientGlaubermanLeftInertiaTheta_isInvariant
        S C hgenerate theta a))

/-- Package the copied kernel character with its invariance under the copied
Sylow subgroup.  The stronger ambient invariance theorem above is the input
used by the ordinary Okuyama--Wajima adapter. -/
def productAmbientGlaubermanLeftInertiaInvariantKernelCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    PInvariantPPrimeIrreducibleCharacter
      (productAmbientGlaubermanLeftInertiaPPrimeKernel
        S C hcentral hgenerate theta)
      (productAmbientGlaubermanLeftInertiaSylow
        S C hgenerate theta :
        Subgroup
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta)) q :=
  ⟨productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter
      S C hcentral hgenerate theta,
    fun a _ha =>
      (IrreducibleCharacter.mem_inertia_iff
        (productAmbientGlaubermanLeftInertiaPPrimeKernel
          S C hcentral hgenerate theta)
        (productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter
          S C hcentral hgenerate theta).1 a).mpr
        (productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter_isInvariant
          S C hcentral hgenerate theta a)⟩

/-- The exact ambient-invariance hypothesis consumed by the ordinary
Okuyama--Wajima extension theorem, specialized to `Γ_theta`. -/
theorem
    productAmbientGlaubermanLeftInertiaInvariantKernelCharacter_ambient
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (a :
      ProductAmbientGlaubermanLeftInertiaGroup
        S C hgenerate theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    a •
        (productAmbientGlaubermanLeftInertiaInvariantKernelCharacter
          S C hcentral hgenerate theta).1.1 =
      (productAmbientGlaubermanLeftInertiaInvariantKernelCharacter
        S C hcentral hgenerate theta).1.1 :=
  productAmbientGlaubermanLeftInertiaPPrimeKernelCharacter_isInvariant
    S C hcentral hgenerate theta a

/-- The fixed points of the copied kernel under the copied Sylow subgroup
lie in the Sylow normalizer.  This is the canonical lower-bound hypothesis
for the intermediate subgroup in `okuyamaWajimaExtensionConclusion`. -/
theorem
    productAmbientGlaubermanLeftInertia_coprimeFixedPoints_le_normalizer
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    coprimeFixedPoints
        (productAmbientGlaubermanLeftInertiaPPrimeKernel
          S C hcentral hgenerate theta)
        (productAmbientGlaubermanLeftInertiaSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) ≤
      Subgroup.normalizer
        ((productAmbientGlaubermanLeftInertiaSylow
          S C hgenerate theta :
          Subgroup
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) :
          Set
            (ProductAmbientGlaubermanLeftInertiaGroup
              S C hgenerate theta)) := by
  intro x hx
  exact
    Subgroup.centralizer_le_normalizer
      ((productAmbientGlaubermanLeftInertiaSylow
        S C hgenerate theta :
        Subgroup
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta)) :
        Set
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta))
      hx.2

/-- In the orientation used by the source side of
`okuyamaWajimaExtensionConclusion`, the Sylow normalizer and copied kernel
generate all of `Γ_theta`. -/
theorem
    productAmbientGlaubermanLeftInertia_normalizer_sup_PPrimeKernel_eq_top
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    Subgroup.normalizer
          ((productAmbientGlaubermanLeftInertiaSylow
            S C hgenerate theta :
            Subgroup
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) :
            Set
              (ProductAmbientGlaubermanLeftInertiaGroup
                S C hgenerate theta)) ⊔
        productAmbientGlaubermanLeftInertiaPPrimeKernel
          S C hcentral hgenerate theta =
      ⊤ := by
  rw [sup_comm]
  exact
    productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_normalizer_eq_top
      S C hcentral hgenerate theta

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
