import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits Opposite

set_option maxHeartbeats 800000

/-
PROBLEM
On an irreducible space, a matching family for the constant presheaf over a
    cover of a nonempty open consists of equal elements at all nonempty arrows.

    This is because: for any two arrows I₁, I₂ in the cover with nonempty domains,
    I₁.Y ∩ I₂.Y is nonempty (irreducible space property), so there exists a relation
    connecting them, forcing x(I₁) = x(I₂).

    Key facts used:
    - Meq.condition: for any relation R, P.map R.g₁.op (x R.fst) = P.map R.g₂.op (x R.snd)
    - For constant presheaf: P.map f = 𝟙, so x(R.fst) = x(R.snd)
    - On irreducible X: nonempty opens have nonempty intersection (IsIrreducible.inter)

PROVIDED SOLUTION
Use `x.condition` (which is `x.2`) applied to a relation connecting I₁ and I₂.

Step 1: Since `I₁.Y` and `I₂.Y` are nonempty open subsets of an irreducible space, their intersection `I₁.Y ⊓ I₂.Y` is nonempty. Use `nonempty_preirreducible_inter I₁.Y.isOpen I₂.Y.isOpen h₁ h₂` to get a point in the intersection.

Step 2: Build a `GrothendieckTopology.Cover.Arrow.Relation I₁ I₂` with `Z = I₁.Y ⊓ I₂.Y`, `g₁ = Opens.infLELeft I₁.Y I₂.Y`, `g₂ = Opens.infLERight I₁.Y I₂.Y`. The compatibility condition `w` should follow since both compositions are the inclusion into U.

Step 3: Build a `GrothendieckTopology.Cover.Relation` (which wraps `fst`, `snd`, and `r`).

Step 4: Apply `x.condition` (or `x.2`) to this relation. Since the presheaf is constant (`Functor.const`), both `P.map r.g₁.op` and `P.map r.g₂.op` are the identity. The condition gives `id (x I₁) = id (x I₂)`, hence `x I₁ = x I₂`.

Key lemmas:
- `nonempty_preirreducible_inter` for the intersection being nonempty
- `Functor.const_obj_map` or `simp [Functor.const]` to simplify the map to identity
- `ConcreteCategory.hom_id` or similar to simplify `ConcreteCategory.hom (𝟙 _)` to `id`

Actually, note that `Meq` uses `ConcreteCategory.hom (P.map ...)`. For the constant presheaf, `P.map f = 𝟙`, so `ConcreteCategory.hom (𝟙 _)` should be `id`. The equation becomes `id (x.1 I₁) = id (x.1 I₂)`.

Actually we need to be careful: the `Cover.Relation` needs `Z` to be in the sieve, i.e. the intersection needs to map into U through the cover. The intersection `I₁.Y ⊓ I₂.Y` maps into U through either arrow, but we need to make sure the sieve condition is satisfied. Actually, looking at `Arrow.Relation`, it just needs `Z`, `g₁ : Z ⟶ I₁.Y`, `g₂ : Z ⟶ I₂.Y` with `g₁ ≫ I₁.f = g₂ ≫ I₂.f`. The `Cover.Relation` wraps this with `fst` and `snd` being arrows.

Actually, we might not need `Z` to be covered - `Arrow.Relation` doesn't require that. It just requires the square to commute. So we set `Z = I₁.Y ⊓ I₂.Y` (as an Opens), `g₁` and `g₂` are the projections.

For the `w` condition: `g₁ ≫ I₁.f = g₂ ≫ I₂.f` - in Opens, both sides are inclusions from `I₁.Y ⊓ I₂.Y` to `U`, which should be equal (they're the same inclusion).

Then we use the `Meq.condition` or `x.2` applied to the constructed `Cover.Relation` to get the result.
-/
theorem meq_const_of_irreducible
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    {U : Opens X} {S : (Opens.grothendieckTopology X).Cover U}
    (x : Meq ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))) S)
    {I₁ I₂ : S.Arrow} (h₁ : (I₁.Y : Set X).Nonempty) (h₂ : (I₂.Y : Set X).Nonempty) :
    x I₁ = x I₂ := by
  -- By the irreducible space property, since I₁.Y and I₂.Y are nonempty open sets, their intersection is also nonempty.
  have h_inter_nonempty : (I₁.Y ⊓ I₂.Y).1.Nonempty := by
    convert nonempty_preirreducible_inter I₁.Y.isOpen I₂.Y.isOpen h₁ h₂ using 1;
  -- By the irreducible space property, since I₁.Y and I₂.Y are nonempty open sets, there exists a relation (箭头) connecting them.
  obtain ⟨Z, g₁, g₂, w⟩ : ∃ (Z : Opens X) (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y), g₁ ≫ I₁.f = g₂ ≫ I₂.f ∧ Z.carrier.Nonempty := by
    refine' ⟨ _, _, _, _, h_inter_nonempty ⟩;
    all_goals try { exact CategoryTheory.homOfLE inf_le_left };
    exact CategoryTheory.homOfLE inf_le_right;
    exact Subsingleton.elim _ _;
  have h_rel : ∃ (R : GrothendieckTopology.Cover.Relation S), R.fst = I₁ ∧ R.snd = I₂ := by
    constructor;
    swap;
    constructor;
    constructor;
    exact w.1;
    exact ⟨ rfl, rfl ⟩;
  obtain ⟨ R, hR₁, hR₂ ⟩ := h_rel; have := x.2 R; aesop;