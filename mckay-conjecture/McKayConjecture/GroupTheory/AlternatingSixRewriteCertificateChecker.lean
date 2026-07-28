/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixRewriteCertificateTypes

/-!
# Executable checker for the `A₆` rewrite certificate

This file replays the generated typed proof paths.  Soundness in the
relevant presented groups is proved separately, so the generated data
remains outside the trusted base.
-/

namespace McKayConjecture
namespace GroupTheory

/-- The four defining relators of the ATLAS presentation. -/
def alternatingSixRewriteRelatorWord :
    Fin 4 → AlternatingSixRewriteWord :=
  ![
    [(0, true), (0, true)],
    [(1, true), (1, true), (1, true), (1, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true),
      (1, true), (0, true), (1, true), (0, true), (1, true)],
    [(0, true), (1, true), (1, true), (0, true), (1, true),
      (1, true), (0, true), (1, true), (1, true), (0, true),
      (1, true), (1, true), (0, true), (1, true), (1, true)]
  ]

/-- The four signed one-letter words used as transition columns. -/
def alternatingSixRewriteLetterWord :
    Fin 4 → AlternatingSixRewriteWord :=
  ![[(0, true)], [(0, false)], [(1, true)], [(1, false)]]

/-- The signed letter named by a cancellation-atom index. -/
def alternatingSixRewriteIndexedLetter
    (index : Nat) :
    Fin 2 × Bool :=
  match index % 4 with
  | 0 => (0, true)
  | 1 => (0, false)
  | 2 => (1, true)
  | _ => (1, false)

/-- Invert a decoded signed word. -/
def alternatingSixRewriteInverseWord
    (word : AlternatingSixRewriteWord) :
    AlternatingSixRewriteWord :=
  word.reverse.map fun letter => (letter.1, !letter.2)

/-- Coordinatewise addition of central-relator weights. -/
def alternatingSixRewriteAddWeight
    (left right : Fin 4 → ℤ) :
    Fin 4 → ℤ :=
  fun i => left i + right i

/-- Coordinatewise negation of a central-relator weight. -/
def alternatingSixRewriteNegWeight
    (weight : Fin 4 → ℤ) :
    Fin 4 → ℤ :=
  fun i => -weight i

/-- The central-relator weight of one proof atom. -/
def alternatingSixRewriteAtomWeight
    (rules : Fin 188 → AlternatingSixRewriteRule)
    (atom : AlternatingSixRewriteAtom) :
    Fin 4 → ℤ :=
  let weight :=
    match atom.kind with
    | .rule =>
        (rules (Fin.ofNat 188 atom.index)).weight
    | .cancel =>
        fun _ => 0
    | .relator =>
        fun i => if i = Fin.ofNat 4 atom.index then 1 else 0
    | .inverseRelator =>
        fun i => if i = Fin.ofNat 4 atom.index then -1 else 0
  if atom.forward then weight
  else alternatingSixRewriteNegWeight weight

/-- Sum the weights along a proof path. -/
def alternatingSixRewriteProofWeight
    (rules : Fin 188 → AlternatingSixRewriteRule) :
    List AlternatingSixRewriteAtom → Fin 4 → ℤ
  | [] => fun _ => 0
  | atom :: proof =>
      alternatingSixRewriteAddWeight
        (alternatingSixRewriteAtomWeight rules atom)
        (alternatingSixRewriteProofWeight rules proof)

/-- The two sides of the uncontextualized equality named by an atom. -/
def alternatingSixRewriteAtomPattern
    (rules : Fin 188 → AlternatingSixRewriteRule)
    (atom : AlternatingSixRewriteAtom) :
    AlternatingSixRewriteWord × AlternatingSixRewriteWord :=
  let pattern :=
    match atom.kind with
    | .rule =>
        let rule := rules (Fin.ofNat 188 atom.index)
        (rule.lhs, rule.rhs)
    | .cancel =>
        let letter := alternatingSixRewriteIndexedLetter atom.index
        ([letter, (letter.1, !letter.2)], [])
    | .relator =>
        (alternatingSixRewriteRelatorWord
          (Fin.ofNat 4 atom.index), [])
    | .inverseRelator =>
        (alternatingSixRewriteInverseWord
          (alternatingSixRewriteRelatorWord
            (Fin.ofNat 4 atom.index)), [])
  if atom.forward then pattern else (pattern.2, pattern.1)

/-- Replay one contextual proof atom. -/
def alternatingSixRewriteApplyAtom
    (rules : Fin 188 → AlternatingSixRewriteRule)
    (word : AlternatingSixRewriteWord)
    (atom : AlternatingSixRewriteAtom) :
    Option AlternatingSixRewriteWord :=
  let left := atom.leftContext
  let right := atom.rightContext
  let pattern := alternatingSixRewriteAtomPattern rules atom
  if word = left ++ pattern.1 ++ right then
    some (left ++ pattern.2 ++ right)
  else
    none

/-- Replay an acyclic proof path. -/
def alternatingSixRewriteApplyProof
    (rules : Fin 188 → AlternatingSixRewriteRule) :
    AlternatingSixRewriteWord →
      List AlternatingSixRewriteAtom →
        Option AlternatingSixRewriteWord
  | word, [] => some word
  | word, atom :: proof =>
      match alternatingSixRewriteApplyAtom rules word atom with
      | none => none
      | some next =>
          alternatingSixRewriteApplyProof rules next proof

/-- Every rule citation in a proof points to a strictly earlier rule. -/
def alternatingSixRewriteProofUsesEarlierRules
    (ruleIndex : Nat)
    (proof : List AlternatingSixRewriteAtom) :
    Bool :=
  proof.all fun atom =>
    decide (atom.kind ≠ .rule) ||
      decide (atom.index < ruleIndex)

/-- Executable validity predicate for one derived rule. -/
def AlternatingSixRewriteRule.Valid
    (rules : Fin 188 → AlternatingSixRewriteRule)
    (ruleIndex : Fin 188) :
    Bool :=
  let rule := rules ruleIndex
  decide
      (alternatingSixRewriteApplyProof rules
          rule.lhs rule.proof = some rule.rhs) &&
    alternatingSixRewriteProofUsesEarlierRules ruleIndex rule.proof &&
    decide
      (alternatingSixRewriteProofWeight rules rule.proof =
        rule.weight)

/-- Executable validity predicate for one normal-form transition. -/
def AlternatingSixRewriteTransition.Valid
    (rules : Fin 188 → AlternatingSixRewriteRule)
    (normalWords : Fin 360 → AlternatingSixRewriteWord)
    (row : Fin 4 → AlternatingSixRewriteTransition)
    (wordIndex : Fin 360) :
    Bool :=
  (List.ofFn fun letter : Fin 4 =>
      decide
        (alternatingSixRewriteApplyProof rules
            (normalWords wordIndex ++
              alternatingSixRewriteLetterWord letter)
            (row letter).proof =
          some
            (normalWords (row letter).target))).all id

/-- Executable validity predicate for a closed weighted rewrite path. -/
def AlternatingSixRewriteLoop.Valid
    (rules : Fin 188 → AlternatingSixRewriteRule)
    (loop : AlternatingSixRewriteLoop) :
    Bool :=
  decide
    (alternatingSixRewriteApplyProof rules
        loop.word loop.proof = some loop.word) &&
    decide
      (alternatingSixRewriteProofWeight rules loop.proof =
        loop.weight)

end GroupTheory
end McKayConjecture
