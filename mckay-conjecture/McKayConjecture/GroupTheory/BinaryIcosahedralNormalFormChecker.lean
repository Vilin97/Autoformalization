/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormDataTypes
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Checker for binary-icosahedral normal-form certificates

These definitions interpret the generated strings and relator certificates
inside the free group.  Transition data and transition checks are split into
small files so all checks run under Lean's default resource limits.
-/

namespace McKayConjecture
namespace GroupTheory

/-- Decode the four printed letters `a,A,b,B`; capitals denote inverses. -/
def binaryIcosahedralDecodeLetter (c : Char) :
    Fin 2 × Bool :=
  if c = 'a' then (0, true)
  else if c = 'A' then (0, false)
  else if c = 'b' then (1, true)
  else (1, false)

/-- Interpret a printed word in the free group on `a,b`. -/
def binaryIcosahedralDecodedWord (s : String) :
    List (Fin 2 × Bool) :=
  s.toList.map binaryIcosahedralDecodeLetter

/-- Interpret a printed word in the free group on `a,b`. -/
def binaryIcosahedralFreeWord (s : String) :
    FreeGroup (Fin 2) :=
  FreeGroup.mk (binaryIcosahedralDecodedWord s)

/-- Printed forms of the two defining relators. -/
def binaryIcosahedralDefiningRelatorWords :
    Nat → String
  | 0 => "aaaBBBBB"
  | _ => "ababAAA"

/-- The two defining relators together with the derived relation `a⁶`. -/
def binaryIcosahedralExtendedRelatorWords :
    Nat → String
  | 0 => "aaaBBBBB"
  | 1 => "ababAAA"
  | _ => "aaaaaa"

/-- The four one-letter words used by the transition table. -/
def binaryIcosahedralNormalFormLetterWords :
    Fin 4 → String :=
  !["a", "A", "b", "B"]

/-- Decode one compact `context,relation,inverse` certificate entry. -/
def binaryIcosahedralDecodeRelatorConjugate
    (entry : String) :
    BinaryIcosahedralRelatorConjugate :=
  match entry.splitOn "," with
  | context :: relation :: inverted :: _ =>
      ⟨context,
        if relation = "0" then 0
        else if relation = "1" then 1
        else 2,
        inverted = "1"⟩
  | _ => ⟨"", 0, false⟩

/-- Decode the semicolon-separated compact certificate representation. -/
def binaryIcosahedralDecodeCertificate
    (certificate : String) :
    List BinaryIcosahedralRelatorConjugate :=
  if certificate = "" then []
  else
    (certificate.splitOn ";").map
      binaryIcosahedralDecodeRelatorConjugate

/-- Evaluate one conjugated relator in the free group. -/
def binaryIcosahedralEvaluateRelatorConjugate
    (relatorWords : Nat → String)
    (c : BinaryIcosahedralRelatorConjugate) :
    FreeGroup (Fin 2) :=
  let p :=
    binaryIcosahedralFreeWord c.context
  let r :=
    binaryIcosahedralFreeWord
      (relatorWords c.relation)
  p *
    (if c.inverted then r⁻¹ else r) *
    p⁻¹

/-- Evaluate a product-of-conjugates certificate. -/
def binaryIcosahedralEvaluateCertificateList
    (relatorWords : Nat → String) :
    List BinaryIcosahedralRelatorConjugate →
      FreeGroup (Fin 2)
  | [] => 1
  | c :: cs =>
      binaryIcosahedralEvaluateRelatorConjugate
          relatorWords c *
        binaryIcosahedralEvaluateCertificateList
          relatorWords cs

/-- Evaluate a compact product-of-conjugates certificate. -/
def binaryIcosahedralEvaluateCertificate
    (relatorWords : Nat → String)
    (certificate : String) :
    FreeGroup (Fin 2) :=
  binaryIcosahedralEvaluateCertificateList
    relatorWords
    (binaryIcosahedralDecodeCertificate certificate)

/-- The raw free word represented by one conjugated relator. -/
def binaryIcosahedralRelatorConjugateWord
    (relatorWords : Nat → String)
    (c : BinaryIcosahedralRelatorConjugate) :
    List (Fin 2 × Bool) :=
  let p := binaryIcosahedralDecodedWord c.context
  let r :=
    binaryIcosahedralDecodedWord
      (relatorWords c.relation)
  p ++
    (if c.inverted then FreeGroup.invRev r else r) ++
    FreeGroup.invRev p

/-- The raw free word represented by a whole certificate. -/
def binaryIcosahedralCertificateWordList
    (relatorWords : Nat → String) :
    List BinaryIcosahedralRelatorConjugate →
      List (Fin 2 × Bool)
  | [] => []
  | c :: cs =>
      binaryIcosahedralRelatorConjugateWord
          relatorWords c ++
        binaryIcosahedralCertificateWordList
          relatorWords cs

/-- The raw free word represented by a compact certificate. -/
def binaryIcosahedralCertificateWord
    (relatorWords : Nat → String)
    (certificate : String) :
    List (Fin 2 × Bool) :=
  binaryIcosahedralCertificateWordList
    relatorWords
    (binaryIcosahedralDecodeCertificate certificate)

/-- Whether two signed letters cancel in a free word. -/
def binaryIcosahedralLettersCancel
    (x y : Fin 2 × Bool) : Bool :=
  decide (x.1 = y.1 ∧ x.2 ≠ y.2)

/-- Push one letter onto a reversed reduced stack. -/
def binaryIcosahedralReducePush
    (stack : List (Fin 2 × Bool))
    (x : Fin 2 × Bool) :
    List (Fin 2 × Bool) :=
  match stack with
  | [] => [x]
  | y :: ys =>
      if binaryIcosahedralLettersCancel y x
      then ys
      else x :: y :: ys

/-- A tail-recursive linear-time free reduction.  Its soundness is proved
in the companion proof file. -/
def binaryIcosahedralFastReduce
    (word : List (Fin 2 × Bool)) :
    List (Fin 2 × Bool) :=
  (word.foldl binaryIcosahedralReducePush []).reverse

/-- The assertion checked for one oriented rewrite rule. -/
def binaryIcosahedralRewriteRuleValid
    (rule : BinaryIcosahedralRewriteRule) : Prop :=
  binaryIcosahedralFastReduce
      (binaryIcosahedralDecodedWord rule.pattern.lhs ++
        FreeGroup.invRev
          (binaryIcosahedralDecodedWord rule.pattern.rhs)) =
    binaryIcosahedralFastReduce
      (binaryIcosahedralCertificateWord
        binaryIcosahedralExtendedRelatorWords
        rule.certificate)

/-- Replay one explicitly contextualized rewrite step. -/
def binaryIcosahedralApplyRewriteStep
    (patterns : Fin 122 → BinaryIcosahedralRewritePattern)
    (word : List (Fin 2 × Bool))
    (step : BinaryIcosahedralRewriteStep) :
    Option (List (Fin 2 × Bool)) :=
  let pattern := patterns step.rule
  let prefixWord :=
    binaryIcosahedralDecodedWord step.leftContext
  let suffixWord :=
    binaryIcosahedralDecodedWord step.rightContext
  if word =
      prefixWord ++
        binaryIcosahedralDecodedWord pattern.lhs ++
        suffixWord
  then
    some
      (prefixWord ++
        binaryIcosahedralDecodedWord pattern.rhs ++
        suffixWord)
  else none

/-- Replay a list of contextualized rewrite steps. -/
def binaryIcosahedralApplyRewriteTrace
    (patterns : Fin 122 → BinaryIcosahedralRewritePattern) :
    List (Fin 2 × Bool) →
      List BinaryIcosahedralRewriteStep →
        Option (List (Fin 2 × Bool))
  | word, [] => some word
  | word, step :: trace =>
      match
        binaryIcosahedralApplyRewriteStep patterns word step
      with
      | none => none
      | some next =>
          binaryIcosahedralApplyRewriteTrace patterns next trace

/-- The assertion checked for one four-entry transition row.  Each trace
starts at the advertised normal word followed by one signed generator and
ends at the advertised target normal word. -/
def binaryIcosahedralNormalFormTransitionRowValid
    (patterns : Fin 122 → BinaryIcosahedralRewritePattern)
    (i : Fin 120)
    (row : Fin 4 → BinaryIcosahedralNormalFormTransition) :
    Prop :=
  ∀ letter : Fin 4,
    binaryIcosahedralApplyRewriteTrace
        patterns
        (binaryIcosahedralDecodedWord
            (binaryIcosahedralNormalFormWords i) ++
          binaryIcosahedralDecodedWord
            (binaryIcosahedralNormalFormLetterWords letter))
        (row letter).trace =
      some
        (binaryIcosahedralDecodedWord
          (binaryIcosahedralNormalFormWords
            (row letter).target))

end GroupTheory
end McKayConjecture
