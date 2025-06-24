import GameServer.Commands

namespace Propositional

World "Propositional"
Level 5
Title "Or Introduction (Left)"

Introduction "
If you know `P`, then you can conclude `P ∨ Q`.

Let’s introduce disjunction using the `left` tactic.
"

/--
For disjunctions (`P ∨ Q`):

- `left` means: “I’ll prove `P`, and that’s enough.”
- `right` means: “I’ll prove `Q`, and that’s enough.”

Use `left` when you have a proof of `P`, and `right` when you have a proof of `Q`.
-/
TacticDoc left

/-- From `P`, derive `P ∨ Q`. -/
TheoremDoc Propositional.or_intro_left as "OrIntroLeft" in "Propositional"

Statement or_intro_left (P Q : Prop) (h : P) : P ∨ Q := by
  Hint "Use the `left` tactic to say `P ∨ Q` is true because `P` is true."
  left
  exact h

NewTactic left
NewTheorem Propositional.or_intro_left

Conclusion "
Great! You’ve learned how to state that “at least one is true.”
"

end Propositional
