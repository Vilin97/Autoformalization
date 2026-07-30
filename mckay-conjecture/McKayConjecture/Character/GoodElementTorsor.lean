/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Gallagher
import McKayConjecture.Character.GoodElement

/-!
# The extension torsor in the good-element predicate

For an invariant character `θ` of `N ◁ A`, conjugation by the preimage of
the quotient centralizer preserves the extensions of `θ` to `N⟨q⟩`.
Gallagher's extension torsor then shows that it is enough to test invariance
on one chosen extension: quotient-centralizer conjugation fixes every linear
twist because it acts trivially on `N⟨q⟩ / N`.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace IrreducibleCharacter

variable {A : Type u} [Group A]
variable (N : Subgroup A) [N.Normal]

/-- Conjugation by the quotient centralizer carries an extension of an
ambient-invariant character to another extension of the same character. -/
theorem goodElementAction_isExtensionAlong
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q)
    (d : goodElementCentralizer N q) :
    IsExtensionAlong (cyclicOverInclusion N q) θ
      (goodElementAction N q d • η.1) := by
  intro n
  change
    η.1.values
        ((goodElementAction N q d).symm
          (cyclicOverInclusion N q n)) =
      θ.values n
  let n' : N := MulAut.conjNormal (H := N) (d : A)⁻¹ n
  calc
    η.1.values
        ((goodElementAction N q d).symm
          (cyclicOverInclusion N q n)) =
        η.1.values (cyclicOverInclusion N q n') := by
      congr 1
    _ = θ.values n' := η.2 n'
    _ = θ.values n :=
      values_conjNormal_eq_of_smul_eq
        N θ hinvariant (d : A)⁻¹ n

/-- The action of a quotient-centralizer element on the extension subtype. -/
def goodElementActionOnExtension
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (d : goodElementCentralizer N q)
    (η : CyclicOverExtensions N θ q) :
    CyclicOverExtensions N θ q :=
  ⟨goodElementAction N q d • η.1,
    goodElementAction_isExtensionAlong N θ hinvariant q η d⟩

@[simp]
theorem goodElementActionOnExtension_coe
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (d : goodElementCentralizer N q)
    (η : CyclicOverExtensions N θ q) :
    (goodElementActionOnExtension N θ hinvariant q d η).1 =
      goodElementAction N q d • η.1 :=
  rfl

/-- The quotient-centralizer action restricted to the extensions of an
ambient-invariant normal character.  This is a named action so callers can
install it locally when subtype-level action notation is useful. -/
@[instance_reducible]
def cyclicOverExtensionsMulAction
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N) :
    MulAction (goodElementCentralizer N q)
      (CyclicOverExtensions N θ q) where
  smul d η :=
    goodElementActionOnExtension N θ hinvariant q d η
  one_smul η := by
    apply Subtype.ext
    change goodElementAction N q 1 • η.1 = η.1
    rw [map_one, one_smul]
  mul_smul d e η := by
    apply Subtype.ext
    change
      goodElementAction N q (d * e) • η.1 =
        goodElementAction N q d •
          (goodElementAction N q e • η.1)
    rw [map_mul, mul_smul]

/-- The copy of `N` internal to `N⟨q⟩`. -/
abbrev cyclicOverNormalSubgroup (q : A ⧸ N) :
    Subgroup (cyclicOverQuotientElement N q) :=
  N.subgroupOf (cyclicOverQuotientElement N q)

/-- The original subgroup `N` is canonically isomorphic to its internal
copy in `N⟨q⟩`. -/
def cyclicOverNormalEquiv (q : A ⧸ N) :
    N ≃* cyclicOverNormalSubgroup N q where
  toFun n :=
    ⟨cyclicOverInclusion N q n, n.2⟩
  invFun n :=
    ⟨((n : cyclicOverQuotientElement N q) : A), n.2⟩
  left_inv _n := Subtype.ext rfl
  right_inv _n := Subtype.ext rfl
  map_mul' _x _y := rfl

@[simp]
theorem cyclicOverNormalEquiv_apply_coe
    (q : A ⧸ N) (n : N) :
    ((cyclicOverNormalEquiv N q n :
        cyclicOverNormalSubgroup N q) :
      cyclicOverQuotientElement N q) =
      cyclicOverInclusion N q n :=
  rfl

@[simp]
theorem cyclicOverNormalEquiv_symm_apply_coe
    (q : A ⧸ N)
    (n : cyclicOverNormalSubgroup N q) :
    ((cyclicOverNormalEquiv N q).symm n : N) =
      ⟨((n : cyclicOverQuotientElement N q) : A), n.2⟩ :=
  rfl

/-- Transport a character of `N` to the internal copy of `N` in
`N⟨q⟩`. -/
def cyclicOverInternalCharacter
    (θ : IrreducibleCharacter N) (q : A ⧸ N) :
    IrreducibleCharacter (cyclicOverNormalSubgroup N q) :=
  θ.comap (cyclicOverNormalEquiv N q).symm

/-- Extension along the canonical inclusion is equivalent to extension
from the literal internal subgroup used by Gallagher's torsor API. -/
theorem isExtensionAlong_cyclicOverInclusion_iff
    (θ : IrreducibleCharacter N)
    (q : A ⧸ N)
    (η : IrreducibleCharacter (cyclicOverQuotientElement N q)) :
    IsExtensionAlong (cyclicOverInclusion N q) θ η ↔
      IsExtensionAlong (cyclicOverNormalSubgroup N q).subtype
        (cyclicOverInternalCharacter N θ q) η := by
  constructor
  · intro hη n
    change
      η.values
          ((n : cyclicOverNormalSubgroup N q) :
            cyclicOverQuotientElement N q) =
        θ.values ((cyclicOverNormalEquiv N q).symm n)
    exact hη ((cyclicOverNormalEquiv N q).symm n)
  · intro hη n
    have h := hη (cyclicOverNormalEquiv N q n)
    calc
      η.values (cyclicOverInclusion N q n) =
          η.values
            ((cyclicOverNormalSubgroup N q).subtype
              (cyclicOverNormalEquiv N q n)) := by
        congr 1
      _ = (cyclicOverInternalCharacter N θ q).values
          (cyclicOverNormalEquiv N q n) := h
      _ = θ.values n := by
        simp [cyclicOverInternalCharacter]

/-- A linear character of `N⟨q⟩` that is trivial on `N` is fixed by
conjugation from the preimage of `C_{A/N}(q)`. -/
theorem linearCharacter_comp_goodElementAction_symm_eq
    (q : A ⧸ N)
    (d : goodElementCentralizer N q)
    (lam : cyclicOverQuotientElement N q →* ℂˣ)
    (hlam :
      ∀ n : cyclicOverNormalSubgroup N q,
        lam
          ((n : cyclicOverNormalSubgroup N q) :
            cyclicOverQuotientElement N q) = 1) :
    lam.comp (goodElementAction N q d).symm.toMonoidHom =
      lam := by
  apply MonoidHom.ext
  intro x
  let y : cyclicOverQuotientElement N q :=
    (goodElementAction N q d).symm x
  have hdCentralizes :
      QuotientGroup.mk' N (d : A) ∈
        Subgroup.centralizer
          (Subgroup.zpowers q : Set (A ⧸ N)) := by
    rw [Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure]
    exact d.2
  have hcomm :
      QuotientGroup.mk' N (x : A) *
          QuotientGroup.mk' N (d : A) =
        QuotientGroup.mk' N (d : A) *
          QuotientGroup.mk' N (x : A) :=
    Subgroup.mem_centralizer_iff.mp hdCentralizes
      (QuotientGroup.mk' N (x : A)) x.2
  have hyQuotient :
      QuotientGroup.mk' N (y : A) =
        QuotientGroup.mk' N (x : A) := by
    rw [show (y : A) =
      (d : A)⁻¹ * (x : A) * (d : A) by
        simpa only [y] using
          (goodElementAction_symm_apply_coe N q d x)]
    simp only [map_mul, map_inv]
    calc
      (QuotientGroup.mk' N (d : A))⁻¹ *
            QuotientGroup.mk' N (x : A) *
            QuotientGroup.mk' N (d : A) =
          (QuotientGroup.mk' N (d : A))⁻¹ *
            (QuotientGroup.mk' N (x : A) *
              QuotientGroup.mk' N (d : A)) := by
            rw [mul_assoc]
      _ = (QuotientGroup.mk' N (d : A))⁻¹ *
            (QuotientGroup.mk' N (d : A) *
              QuotientGroup.mk' N (x : A)) := by
            rw [hcomm]
      _ = QuotientGroup.mk' N (x : A) := by
            group
  have hyDivMem :
      (y / x : cyclicOverQuotientElement N q) ∈
        cyclicOverNormalSubgroup N q := by
    change (y : A) / (x : A) ∈ N
    apply (QuotientGroup.eq_iff_div_mem (N := N)).mp
    simpa only [← QuotientGroup.mk'_apply] using hyQuotient
  have htrivial :=
    hlam
      (⟨y / x, hyDivMem⟩ :
        cyclicOverNormalSubgroup N q)
  change lam y = lam x
  apply div_eq_one.mp
  rw [← map_div]
  exact htrivial

/-- Quotient-centralizer conjugation commutes with a linear twist that is
trivial on the internal copy of `N`. -/
theorem goodElementAction_smul_twist
    (q : A ⧸ N)
    (d : goodElementCentralizer N q)
    (lam : cyclicOverQuotientElement N q →* ℂˣ)
    (hlam :
      ∀ n : cyclicOverNormalSubgroup N q,
        lam
          ((n : cyclicOverNormalSubgroup N q) :
            cyclicOverQuotientElement N q) = 1)
    (η : IrreducibleCharacter (cyclicOverQuotientElement N q)) :
    goodElementAction N q d • twist lam η =
      twist lam (goodElementAction N q d • η) := by
  change
    (twist lam η).comap (goodElementAction N q d).symm =
      twist lam
        (η.comap (goodElementAction N q d).symm)
  rw [twist_comap,
    linearCharacter_comp_goodElementAction_symm_eq
      N q d lam hlam]

/-- To test whether `q` is good, it is enough to test invariance of one
chosen extension of `θ` to `N⟨q⟩`.  Once that extension is supplied, this
equivalence does not itself require ambient invariance of `θ`. -/
theorem isGoodQuotientElement_iff_one_extension
    [Finite A]
    (θ : IrreducibleCharacter N)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q) :
    IsGoodQuotientElement N θ q ↔
      ∀ d : goodElementCentralizer N q,
        goodElementAction N q d • η.1 = η.1 := by
  constructor
  · intro hgood d
    exact hgood η d
  · intro hchosen φ d
    have hηInternal :
        IsExtensionAlong
          (cyclicOverNormalSubgroup N q).subtype
          (cyclicOverInternalCharacter N θ q) η.1 :=
      (isExtensionAlong_cyclicOverInclusion_iff N θ q η.1).mp
        η.2
    have hφInternal :
        IsExtensionAlong
          (cyclicOverNormalSubgroup N q).subtype
          (cyclicOverInternalCharacter N θ q) φ.1 :=
      (isExtensionAlong_cyclicOverInclusion_iff N θ q φ.1).mp
        φ.2
    obtain ⟨lam, hlam, hφ⟩ :=
      hηInternal.exists_eq_twist hφInternal
    rw [hφ,
      goodElementAction_smul_twist N q d lam hlam η.1,
      hchosen d]

end IrreducibleCharacter
end McKayConjecture
