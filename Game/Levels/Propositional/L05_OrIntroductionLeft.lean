import GameServer.Commands
import Game.Levels.Propositional.L04_AndEliminationLeft
namespace Propositional

World "Propositional"
Level 5
Title "Or Introduction (Left)"

Introduction "
If you know `P`, then you can conclude `P ∨ Q`.

Let’s introduce disjunction using the `left` tactic.
"
/--
Purpose: Use exact when you already have a proof of exactly what the goal is asking for.

It closes the goal immediately if the term matches the goal’s type.

📌 Think of it as:

“Here's exactly what you're asking for — done!”

If your goal is `P` and you have a proof of `P` (say `h : P`), then `exact h` completes the proof.

To summarize:

You have : `h : P`
Your goal : `P`
`exact h` will complete the proof!
-/
TacticDoc exact

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
  Hint "Now you can finish the level yourself."
  exact h

NewTactic left

NewTheorem Propositional.and_elim_left
Conclusion "
Great! You’ve learned how to state that “at least one is true.”
"

end Propositional
