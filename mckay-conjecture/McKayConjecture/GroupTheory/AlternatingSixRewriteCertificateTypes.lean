/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixPresentation

/-!
# Data types for the certified `A₆` rewrite system

A signed letter is a generator index and a sign.  Derived rules are
justified by short rewrite paths that may cite only earlier rules.  Keeping
the generated certificate in this already-decoded representation lets the
kernel replay it under Lean's default recursion limit.
-/

namespace McKayConjecture
namespace GroupTheory

/-- A signed letter in the two-generator free group. -/
abbrev AlternatingSixRewriteLetter := Fin 2 × Bool

/-- A word in the two-generator free group. -/
abbrev AlternatingSixRewriteWord := List AlternatingSixRewriteLetter

/-- The kind of one atomic equality in a rewrite-rule proof. -/
inductive AlternatingSixRewriteAtomKind
  | rule
  | cancel
  | relator
  | inverseRelator
deriving DecidableEq

/-- One contextual use of a defining equality or an earlier rewrite rule. -/
structure AlternatingSixRewriteAtom where
  leftContext : AlternatingSixRewriteWord
  rightContext : AlternatingSixRewriteWord
  kind : AlternatingSixRewriteAtomKind
  index : Nat
  forward : Bool
deriving DecidableEq

/-- One oriented rule together with its acyclic proof and central-relator
weight.  The weight records what remains if the four defining relators are
made central rather than killed. -/
structure AlternatingSixRewriteRule where
  lhs : AlternatingSixRewriteWord
  rhs : AlternatingSixRewriteWord
  proof : List AlternatingSixRewriteAtom
  weight : Fin 4 → ℤ
deriving DecidableEq

/-- One normal-form transition and its certified rewrite path. -/
structure AlternatingSixRewriteTransition where
  target : Fin 360
  proof : List AlternatingSixRewriteAtom
deriving DecidableEq

/-- A closed rewrite path used to obtain a relation among the four central
relator values. -/
structure AlternatingSixRewriteLoop where
  word : AlternatingSixRewriteWord
  proof : List AlternatingSixRewriteAtom
  weight : Fin 4 → ℤ
deriving DecidableEq

end GroupTheory
end McKayConjecture
