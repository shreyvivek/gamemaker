import GameServer.Commands

namespace Propositional

World "Propositional"
Level 6
Title "Or Introduction (Right)"

Introduction "
If `Q` is true, then `P ∨ Q` is also true — because *at least one* must hold.

Now let’s learn how to use the `right` tactic.
"

/-- Repeated for clarity.

For disjunctions (`P ∨ Q`):

- `left` means: “I’ll prove `P`, and that’s enough.”
- `right` means: “I’ll prove `Q`, and that’s enough.”

Use `left` when you have a proof of `P`, and `right` when you have a proof of `Q`.
-/
TacticDoc right

/-- From `Q`, derive `P ∨ Q`. -/
TheoremDoc Propositional.or_intro_right as "OrIntroRight" in "Propositional"

Statement or_intro_right (P Q : Prop) (h : Q) : P ∨ Q := by
  Hint "Use the `right` tactic this time, to commit to proving `Q` instead of `P`."
  right
  Hint "Now finish the proof by showing `Q` holds using `{h}`."
  exact h

NewTactic right
NewTheorem Propositional.or_intro_right

Conclusion "
Great! You've mastered both left and right disjunction introduction.
"

end Propositional
