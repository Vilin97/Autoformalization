/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.PerfectCentralExtensionCenter

/-!
# A splitting criterion for universal central extensions

A perfect central extension `U → S` is universal as soon as `U` is
*centrally closed*: every central extension onto `U` splits.

The proof is the standard pullback argument.  Given another central
extension `V → S`, pull it back along `U → S`.  A section of the resulting
central extension onto `U` has a second coordinate `U → V`, which is the
required lift.  Perfectness makes that lift unique.

This criterion separates the formal category-free argument from concrete
Schur-cover computations.  In particular, for the binary icosahedral
group, only central closedness of the explicit finite group remains to be
proved from a presentation.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {U V S : Type u}
variable [Group U] [Group V] [Group S]

namespace CentralExtension

/-- The subgroup of pairs with equal image in the common target. -/
def pullbackSubgroup
    (E : CentralExtension U S)
    (F : CentralExtension V S) :
    Subgroup (U × V) where
  carrier := {x | E.projection x.1 = F.projection x.2}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    show
      E.projection (x * y).1 =
        F.projection (x * y).2
    change
      E.projection (x.1 * y.1) =
        F.projection (x.2 * y.2)
    rw [map_mul, map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    simpa [map_inv, hx]

/-- The elementary pullback of two central extensions. -/
abbrev Pullback
    (E : CentralExtension U S)
    (F : CentralExtension V S) :=
  E.pullbackSubgroup F

/-- First-coordinate projection from a pullback. -/
def pullbackFst
    (E : CentralExtension U S)
    (F : CentralExtension V S) :
    E.Pullback F →* U where
  toFun x := x.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Second-coordinate projection from a pullback. -/
def pullbackSnd
    (E : CentralExtension U S)
    (F : CentralExtension V S) :
    E.Pullback F →* V where
  toFun x := x.1.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The two pullback projections agree after mapping to the common target. -/
theorem projection_comp_pullbackFst
    (E : CentralExtension U S)
    (F : CentralExtension V S) :
    E.projection.comp (E.pullbackFst F) =
      F.projection.comp (E.pullbackSnd F) := by
  ext x
  exact x.2

/-- Projection of a pullback to its first coordinate is a central
extension. -/
def pullbackCentralExtension
    (E : CentralExtension U S)
    (F : CentralExtension V S) :
    CentralExtension (E.Pullback F) U where
  projection := E.pullbackFst F
  surjective := by
    intro u
    obtain ⟨v, hv⟩ := F.surjective (E.projection u)
    refine ⟨⟨(u, v), ?_⟩, rfl⟩
    exact hv.symm
  ker_le_center := by
    intro x hx
    have hxFst : x.1.1 = 1 :=
      MonoidHom.mem_ker.mp hx
    have hxSndKer : x.1.2 ∈ F.projection.ker := by
      apply MonoidHom.mem_ker.mpr
      have hpullback := x.2
      change
        E.projection x.1.1 =
          F.projection x.1.2 at hpullback
      rw [hxFst, map_one] at hpullback
      exact hpullback.symm
    have hxSndCenter :
        x.1.2 ∈ Subgroup.center V :=
      F.ker_le_center hxSndKer
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Prod.ext
    · simp [hxFst]
    · exact
        Subgroup.mem_center_iff.mp
          hxSndCenter y.1.2

/-- A homomorphic section of the first pullback projection supplies a map
between the original extensions over their common target. -/
def liftOfPullbackSection
    (E : CentralExtension U S)
    (F : CentralExtension V S)
    (σ : U →* E.Pullback F) :
    U →* V :=
  (E.pullbackSnd F).comp σ

theorem liftOfPullbackSection_commutes
    (E : CentralExtension U S)
    (F : CentralExtension V S)
    (σ : U →* E.Pullback F)
    (hsection :
      (E.pullbackFst F).comp σ =
        MonoidHom.id U) :
    F.projection.comp
        (E.liftOfPullbackSection F σ) =
      E.projection := by
  ext u
  have hpullback :=
    DFunLike.congr_fun
      (E.projection_comp_pullbackFst F)
      (σ u)
  change
    E.projection ((E.pullbackFst F) (σ u)) =
      F.projection ((E.pullbackSnd F) (σ u))
        at hpullback
  have hsectionApply :=
    DFunLike.congr_fun hsection u
  change
    (E.pullbackFst F) (σ u) = u
      at hsectionApply
  change
    F.projection
        ((E.pullbackSnd F) (σ u)) =
      E.projection u
  rw [← hpullback]
  rw [hsectionApply]

end CentralExtension

/-- A group is centrally closed if every central extension onto it admits
a homomorphic section. -/
def IsCentrallyClosed (U : Type u) [Group U] : Prop :=
  ∀ (V : Type u) [Group V]
    (F : CentralExtension V U),
    ∃ σ : U →* V,
      F.projection.comp σ =
        MonoidHom.id U

/-- A perfect centrally closed central extension is universal. -/
def universalCentralExtensionOfIsCentrallyClosed
    (E : CentralExtension U S)
    (hperfect : Group.IsPerfect U)
    (hclosed : IsCentrallyClosed U) :
    UniversalCentralExtension U S where
  toCentralExtension := E
  sourcePerfect := hperfect
  lift := by
    intro V _ F
    obtain ⟨σ, hsection⟩ :=
      hclosed (E.Pullback F)
        (E.pullbackCentralExtension F)
    let lift : U →* V :=
      E.liftOfPullbackSection F σ
    have hlift :
        F.projection.comp lift =
          E.projection :=
      E.liftOfPullbackSection_commutes
        F σ hsection
    refine ⟨lift, hlift, ?_⟩
    intro g hg
    exact
      F.hom_ext_of_domain_perfect
        hperfect g lift
        (hg.trans hlift.symm)

end GroupTheory
end McKayConjecture
