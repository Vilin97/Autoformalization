import Mathlib

universe u

open CategoryTheory TopologicalSpace

/-- On an irreducible space, the constant sheaf Z has epi restriction maps (is flasque).

    On an irreducible space, any two nonempty opens intersect. The constant sheaf
    (sheafification of the constant presheaf with value Z) assigns Z to every
    nonempty connected open, with identity restriction maps. Since every nonempty
    open in an irreducible space is connected, all restriction maps are identity = epi.

    Key facts:
    - On an irreducible space, every nonempty open is irreducible (hence connected)
    - The constant sheaf is the sheafification of the constant presheaf
    - On a connected space, the constant sheaf has F(U) = A for nonempty U
    - The restriction maps of the constant sheaf between nonempty connected opens are identity
    - The restriction to the empty open is to the terminal (zero) object, which is always epi

    Mathlib tools available:
    - `constantSheaf J D` = `Functor.const Cᵒᵖ ⋙ presheafToSheaf J D`
    - `Opens.grothendieckTopology` for the topology on opens
    - `IrreducibleSpace` typeclass
    - `IsPreirreducible.isConnected` for nonempty preirreducible → connected -/
theorem constantSheaf_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X]
    {U V : Opens X} (i : U ⟶ V) :
    Epi (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))).val.map i.op) := by
  sorry
