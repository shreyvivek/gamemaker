import GameServer.Commands

namespace Propositional

World "Propositional"
Level 14
Title "Proof by Contradiction"

Introduction "
If assuming `¬P` leads to a contradiction, then `P` must be true.

This is known as **proof by contradiction**.
"

/--
To prove `P`, assume `¬P` and derive `False`.

Then use `exact` with `False.elim` to conclude anything from the contradiction.
-/
TacticDoc False.elim

/-- If `¬P → False`, then `P`. -/
TheoremDoc Propositional.contradiction_implies_p as "ContradictionImpliesP" in "Propositional"

Statement contradiction_implies_p (P : Prop) (h : ¬P → False) : P := by
  Hint "Assume `¬P`, and apply `{h}` to derive a contradiction."
  apply Classical.byContradiction
  intro hnp
  exact h hnp

NewTheorem Propositional.contradiction_implies_p

Conclusion "
You’ve completed a **proof by contradiction** — a powerful logical strategy.
"

end Propositional
