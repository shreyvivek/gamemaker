import GameServer.Commands
import Game.Levels.Propositional.L05_OrIntroductionLeft
namespace Propositional

World "Propositional"
Level 6
Title "Or Introduction (Right)"

Introduction "
If `Q` is true, then `P ∨ Q` is also true — because *at least one* must hold.

Now let’s learn how to use the `right` tactic.
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
Purpose: Use intro to assume something — usually when proving an implication.

If your goal is `P → Q`, `intro h` changes the goal to `Q` and gives you `h : P` as a local assumption.

📌 Think of it as:

“Let me assume `P` is true for now, and see if I can prove `Q`.”
Opens up an implication goal by introducing its assumption.

To summarize:

Your goal : `h : P → P`
After `intro h`,
you get an assumption `h : P` and your goal will just be `P`.
-/
TacticDoc intro


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

NewTheorem Propositional.or_intro_left
Conclusion "
Great! You've mastered both left and right disjunction introduction.
"

end Propositional
