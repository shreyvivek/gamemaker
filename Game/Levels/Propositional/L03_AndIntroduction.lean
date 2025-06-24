import GameServer.Commands

namespace Propositional

World "Propositional"
Level 3
Title "And Introduction"

Introduction "
From `P` and `Q`, we can conclude `P ∧ Q`. That’s how conjunction works!

You’ll learn the `constructor` tactic in this level.
"

/--
Used when the goal is a compound proposition like `P ∧ Q`.

It splits the goal into proving both components separately.

For example: `constructor` on `P ∧ Q` gives you two goals — one for `P` and one for `Q`.
-/
TacticDoc constructor

/-- From `P` and `Q`, derive `P ∧ Q`. -/
TheoremDoc Propositional.and_intro as "AndIntro" in "Propositional"

Statement and_intro (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  Hint "Use the `constructor` tactic to split the goal `P ∧ Q` into two parts."
  constructor
  Hint "Now prove `P` using `{hp}`."
  exact hp
  Hint "Now prove `Q` using `{hq}`."
  exact hq

NewTactic constructor
NewTheorem Propositional.and_intro

Conclusion "
Nice work! You combined two truths into one solid conjunction.
"

end Propositional
