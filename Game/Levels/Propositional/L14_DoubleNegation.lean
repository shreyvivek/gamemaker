import GameServer.Commands

namespace Propositional

World "Propositional"
Level 14
Title "Double Negation Elimination"

Introduction "
In classical logic, we can remove double negation: from `¬¬P`, conclude `P`.

This principle doesn’t hold in constructive logic, which makes it an interesting tool to examine.
"

/--
To eliminate `¬¬P`, we assume `¬P`, derive a contradiction using `h : ¬¬P`, and conclude `P`.

This requires classical logic.
-/
TacticDoc Classical.byContradiction

/-- In classical logic, `¬¬P` implies `P`. -/
TheoremDoc Propositional.double_negation as "DoubleNegationElim" in "Propositional"

Statement double_negation (P : Prop) (h : ¬¬P) : P := by
  Hint "Use `Classical.byContradiction` to assume `¬P` and derive a contradiction."
  apply Classical.byContradiction
  intro hnp
  exact h hnp

NewTactic Classical.byContradiction
NewTheorem Propositional.double_negation

Conclusion "
You’ve applied **Double Negation Elimination** — valid in classical logic but not in constructive logic.
"

end Propositional
