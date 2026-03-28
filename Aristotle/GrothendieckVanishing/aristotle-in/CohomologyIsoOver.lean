import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits Opposite Abelian

-- The second Mathlib TODO in SheafCohomology/Basic.lean:
-- "if U : C, define an isomorphism
--  (F.cohomologyPresheaf n).obj (op U) ≃+ Sheaf.H (F.over U) n"
--
-- This means: H'(U, F, n) ≅ H(F.over U, n)
-- where F.over U is the restriction of F to the overcategory C/U.
--
-- For topological spaces: C/U ≃ Opens(U) (opens contained in U)
-- and F.over U is the restriction of F to opens ≤ U.
--
-- The proof strategy (same as for the ⊤ case):
-- H'(U, F, n) = Ext(presheafToSheaf(yoneda U ⋙ free), F, n)
-- H(F.over U, n) = Ext(constantSheaf Z on C/U, F.over U, n)
--
-- Need: presheafToSheaf(yoneda U ⋙ free) on C is related to
--       constantSheaf Z on C/U via the forgetful functor C/U → C.
--
-- This is more complex than the ⊤ case because we need to work with
-- the overcategory and restriction.

-- For now, let me just prove the Subsingleton version that we need:
-- If Sheaf.H (F.over U) n is Subsingleton, then H'(U, F, n) is also Subsingleton.
-- This is sufficient for the Mayer-Vietoris argument.

-- Actually, for the MV argument, we need:
-- If n > dim(X) and the right vanishing holds, then H'(U, n) vanishes.
-- But H'(U, n) = Ext(Z_U, F, n) where Z_U is a specific sheaf.
-- The vanishing of this Ext group doesn't directly follow from
-- dimension arguments unless we can relate it to cohomology on a subspace.

-- Let me think about whether we can bypass this entirely.
-- The MV sequence gives exactness of H'(U⊔V) → H'(U) ⊕ H'(V) → H'(U⊓V)
-- If we can show H'(W) is subsingleton for ALL opens W when n > dim X,
-- then everything vanishes and we're done.

-- But showing H'(W) vanishes for all W is essentially showing
-- Ext(Z_W, F, n) = 0 for all W, which IS the Grothendieck vanishing theorem
-- for the free abelian sheaf Z_W. This is circular!

-- So the MV approach alone doesn't avoid the need for j_! or H' ≅ H for general opens.

-- ALTERNATIVE: Maybe I can prove vanishing of H' directly by induction,
-- without reducing to H on subspaces.

-- Actually, the key observation: Sheaf.H F n = Ext(Z_⊤, F, n) where Z_⊤ = constantSheaf Z.
-- And the MV LES decomposes Z_⊤ via the short exact sequence
-- 0 → Z_{U⊓V} → Z_U ⊕ Z_V → Z_{U⊔V} → 0
-- (this IS the MV short complex in Mathlib!)
--
-- So: if Ext(Z_U, F, n) = Ext(Z_V, F, n) = 0 and Ext(Z_{U⊓V}, F, n-1) = 0,
-- then Ext(Z_{U⊔V}, F, n) = 0 by the LES.
--
-- For U ⊔ V = ⊤: this gives Ext(Z_⊤, F, n) = Sheaf.H F n = 0!
--
-- And the induction works on the OPENS, not on subspaces!
-- We need: Ext(Z_W, F, n) = 0 for all W with some property
-- (maybe dim(closure W) < n).
--
-- For W = ⊥ (empty): Z_⊥ is zero, so Ext = 0. ✓
-- For W nonempty open in irreducible component: ???
--
-- Actually this IS essentially the Grothendieck vanishing proof
-- reformulated in terms of Ext(Z_W, F, n)!

-- Hmm, I think I need to keep both approaches in mind.
-- Let me just submit this analysis and see what Aristotle produces.

example : True := trivial
